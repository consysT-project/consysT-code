package de.tuda.consys.formalization

import de.tuda.consys.formalization.backend.Store
import de.tuda.consys.formalization.lang.ClassTable.{ClassTable, fields}
import de.tuda.consys.formalization.lang._
import de.tuda.consys.formalization.lang.errors.ExecutionError
import de.tuda.consys.formalization.lang.types.{BooleanTypeSuffix, ClassType, LocalTypeSuffix, NonVarTypeSuffix, NumberTypeSuffix, RefTypeSuffix, StringTypeSuffix, TypeSuffixVar, UnitTypeSuffix}

object CassandraInitializer {
    def initialize(storeAddress: String): Unit = {
        val s = Store.fromAddress(storeAddress, 9042, 2181, "datacenter1", initialize = true)
        s.close()
    }
}

class Interpreter(storeAddress: String) {
    private type VarEnv = Map[VarId, Expression]

    private val store = Store.
        fromAddress(storeAddress, 9042, 2181, "datacenter1")

    def run(ct: ClassTable, process: Statement): Unit = {
        interpret(process)(ct)
        store.close()
    }

    private def interpret(stmt: Statement)(implicit ct: ClassTable): Unit = {
        var s = stmt
        var varEnv: VarEnv = Map.empty
        while (s != Skip) {
            val (s1, varEnv1) = stepStmt(s, varEnv)
            s = s1
            varEnv = varEnv1
        }
    }

    private def isValue(e: Expression): Boolean = e match {
        case Num(_) => true
        case True => true
        case False => true
        case UnitLiteral => true
        case StringLiteral(_) => true
        case Ref(_, _) => true
        case LocalObj(_, constructor) => constructor.forall(p => isValue(p._2))
        case _ => false
    }

    private def stepExpr(e: Expression)(implicit vars: VarEnv, ct: ClassTable): Expression = e match {
        case Var(id) => vars(id)

        case Equals(e1, e2) if isValue(e1) && isValue(e2) =>
            if (e1 == e2) True
            else False

        case Equals(e1, e2) if isValue(e1) => Equals(e1, stepExpr(e2))

        case Equals(e1, e2) => Equals(stepExpr(e1), e2)

        case ArithmeticOperation(n1: Num, n2: Num, op) => op(n1, n2)

        case ArithmeticOperation(n1: Num, expr2, op) => ArithmeticOperation(n1, stepExpr(expr2), op)

        case ArithmeticOperation(expr1, expr2, op) => ArithmeticOperation(stepExpr(expr1), expr2, op)

        case ArithmeticComparison(n1: Num, n2: Num, op) => op(n1, n2)

        case ArithmeticComparison(n1: Num, expr2, op) => ArithmeticComparison(n1, stepExpr(expr2), op)

        case ArithmeticComparison(expr1, expr2, op) => ArithmeticComparison(stepExpr(expr1), expr2, op)

        case BooleanCombination(b1: BooleanValue, b2: BooleanValue, op) => op(b1, b2)

        case BooleanCombination(b1: BooleanValue, expr2, op) => BooleanCombination(b1, stepExpr(expr2), op)

        case BooleanCombination(expr1, expr2, op) => BooleanCombination(stepExpr(expr1), expr2, op)

        case LocalObj(classType, constructor) =>
            constructor.find(p => !isValue(p._2)) match {
                case Some(constructorElem) => LocalObj(classType, constructor + (constructorElem._1 -> stepExpr(constructorElem._2)))
                case None => throw ExecutionError("invalid execution path")
            }

        case Default(s, _) => s match {
            case TypeSuffixVar(_) => throw ExecutionError("invalid execution path")
            case BooleanTypeSuffix => False
            case NumberTypeSuffix => Num(0)
            case UnitTypeSuffix => UnitLiteral
            case StringTypeSuffix => StringLiteral("")
            case suffix: NonVarTypeSuffix => suffix match {
                case LocalTypeSuffix(classType) => LocalObj(classType, fields(classType).map(f => f._1 -> f._2.init))
                case RefTypeSuffix(classType) => Ref("default", classType)
            }
        }
    }

    private def stepStmt(s: Statement, vars: VarEnv)(implicit ct: ClassTable): (Statement, VarEnv) = s match {
        case ReturnExpr(e) if !isValue(e) =>
            (ReturnExpr(stepExpr(e)(vars, ct)), vars)

        case Block(blockVars, Skip) => (Skip, vars -- blockVars.map(_._2))
        case Block(blockVars, Error) => (Error, vars -- blockVars.map(_._2))
        case Block(blockVars, ReturnExpr(e)) if isValue(e) => (ReturnExpr(e), vars -- blockVars.map(_._2))
        case Block(blockVars, s) if blockVars.forall(v => isValue(v._3)) =>
            val (s1, r1) = stepStmt(s, vars ++ blockVars.map(v => v._2 -> v._3))
            val newBlockVars = blockVars.map(v => (v._1, v._2, r1(v._2)))
            (Block(newBlockVars, s1), r1 -- blockVars.map(_._2))
        case Block(blockVars, s) =>
            val i = blockVars.indexWhere(p => !isValue(p._3))
            val newBlockVars = blockVars.zipWithIndex.map(t =>
                if (t._2 == i)
                    (blockVars(i)._1, blockVars(i)._2, stepExpr(blockVars(i)._3)(vars, ct))
                else t._1)
            (Block(newBlockVars, s), vars)

        case Sequence(Error, _) => (Error, vars)
        case Sequence(ReturnExpr(e), _) if isValue(e) => (ReturnExpr(e), vars)
        case Sequence(Skip, s2) => (s2, vars)
        case Sequence(s1, s2) =>
            val (s1R, varsR) = stepStmt(s1, vars)
            (Sequence(s1R, s2), varsR)

        case If(conditionExpr, thenStmt, _) if conditionExpr == True => (thenStmt, vars)
        case If(conditionExpr, _, elseStmt) if conditionExpr == False => (elseStmt, vars)
        case If(conditionExpr, thenStmt, elseStmt) =>
            val e = stepExpr(conditionExpr)(vars, ct)
            (If(e, thenStmt, elseStmt), vars)

        case While(condition, stmt) => (If(condition, Sequence(stmt, While(condition, stmt)), Skip), vars)

        case Let(varId, e) if isValue(e) => (Skip, vars + (varId -> e))
        case Let(varId, e) => (Let(varId, stepExpr(e)(vars, ct)), vars)

        case SetField(fieldId, valueExpr) if isValue(valueExpr) =>
            val thisObj = vars(thisId).asInstanceOf[Ref]
            val handler = store.getCurrentTransaction.get.resolveHandler(
                location(thisObj.id, thisObj.classType), thisObj.classType)
            handler.setField(fieldId, valueExpr)
            (Skip, vars)
        case SetField(fieldId, valueExpr) =>
            val e = stepExpr(valueExpr)(vars, ct)
            (SetField(fieldId, e), vars)

        case GetField(varId, fieldId) if vars(thisId).isInstanceOf[Ref] =>
            val thisObj = vars(thisId).asInstanceOf[Ref]
            val handler = store.getCurrentTransaction.get.resolveHandler(
                location(thisObj.id, thisObj.classType), thisObj.classType)
            (Skip, vars + (varId -> handler.getField(fieldId)))
        case GetField(varId, fieldId) if vars(thisId).isInstanceOf[LocalObj] =>
            val thisObj = vars(thisId).asInstanceOf[LocalObj]
            (Skip, vars + (varId -> thisObj.constructor(fieldId)))

        case CallUpdate(recvExpr, methodId, argumentExprs) if isValue(recvExpr) && argumentExprs.forall(isValue) =>
            val recvRef = recvExpr.asInstanceOf[Ref]
            val mBody = ClassTable.mBody(methodId, recvRef.classType)
            mBody match {
                case _: UpdateBody =>
                case _: QueryBody => throw ExecutionError(s"invalid method sort for update ($methodId)")
            }
            val handler = store.getCurrentTransaction.get.resolveHandler(
                location(recvRef.id, recvRef.classType), recvRef.classType)
            handler.invoke(mBody.operationLevel)
            val argumentBindings = (mBody.arguments zip argumentExprs).map(p => p._1 -> p._2).toMap
            (EvalUpdate(recvExpr, methodId, argumentBindings + (thisId -> recvRef), mBody.body), vars)
        case CallUpdate(recvExpr, methodId, argumentExprs) if isValue(recvExpr) =>
            val i = argumentExprs.indexWhere(p => !isValue(p))
            val newArguments = argumentExprs.zipWithIndex.map(t =>
                if (t._2 == i)
                    stepExpr(argumentExprs(i))(vars, ct)
                else t._1)
            (CallUpdate(recvExpr, methodId, newArguments), vars)
        case CallUpdate(recvExpr, methodId, argumentExprs) =>
            val e = stepExpr(recvExpr)(vars, ct)
            (CallUpdate(e, methodId, argumentExprs), vars)

        case CallUpdateThis(methodId, argumentExprs) =>
            (CallUpdate(vars(thisId), methodId, argumentExprs), vars)

        case CallQuery(varId, recvExpr, methodId, argumentExprs) if isValue(recvExpr) && argumentExprs.forall(isValue) =>
            val mBody = recvExpr match {
                case ref: Ref => ClassTable.mBody(methodId, ref.classType)
                case obj: LocalObj => ClassTable.mBody(methodId, obj.classType)
                case _ => throw ExecutionError(s"invalid receiver value for query: $recvExpr")
            }
            mBody match {
                case _: QueryBody =>
                case _: UpdateBody => throw ExecutionError(s"invalid method sort for update ($methodId)")
            }
            if (recvExpr.isInstanceOf[Ref]) {
                val handler = store.getCurrentTransaction.get.resolveHandler(
                    location(recvExpr.asInstanceOf[Ref].id, recvExpr.asInstanceOf[Ref].classType),
                    recvExpr.asInstanceOf[Ref].classType)
                handler.invoke(mBody.operationLevel)
            }
            val argumentBindings = (mBody.arguments zip argumentExprs).map(p => p._1 -> p._2).toMap
            (EvalQuery(varId, recvExpr, methodId, argumentBindings + (thisId -> recvExpr), mBody.body), vars)
        case CallQuery(varId, recvExpr, methodId, argumentExprs) if isValue(recvExpr) =>
            val i = argumentExprs.indexWhere(p => !isValue(p))
            val newArguments = argumentExprs.zipWithIndex.map(t =>
                if (t._2 == i)
                    stepExpr(argumentExprs(i))(vars, ct)
                else t._1)
            (CallQuery(varId, recvExpr, methodId, newArguments), vars)
        case CallQuery(varId, recvExpr, methodId, argumentExprs) =>
            val e = stepExpr(recvExpr)(vars, ct)
            (CallQuery(varId, e, methodId, argumentExprs), vars)

        case CallQueryThis(varId, methodId, argumentExprs) =>
            (CallQuery(varId, vars(thisId), methodId, argumentExprs), vars)

        case EvalUpdate(_, _, _, Error) =>
            (Error, vars)
        case EvalUpdate(_, _, _, ReturnExpr(e)) if isValue(e) =>
            (Skip, vars)
        case EvalUpdate(recv, methodId, args, body) =>
            val (s1, r1) = stepStmt(body, args)
            val newArgs = r1.filter(r => args.contains(r._1))
            (EvalUpdate(recv, methodId, newArgs, s1), vars)

        case EvalQuery(_, _, _, _, Error) =>
            (Error, vars)
        case EvalQuery(varId, _, _, _, ReturnExpr(e)) if isValue(e) =>
            (Skip, vars + (varId -> e))
        case EvalQuery(varId, recv, methodId, args, body) =>
            val (s1, r1) = stepStmt(body, args)
            val newArgs = r1.filter(r => args.contains(r._1))
            (EvalQuery(varId, recv, methodId, newArgs, s1), vars)

        case Replicate(varId, refId, classType, constructor) if constructor.values.forall(isValue) =>
            store.getCurrentTransaction.get.replicateNew(location(refId, classType), classType, constructor)
            (Skip, vars + (varId -> Ref(refId, classType)))

        case Replicate(varId, refId, classType, constructor) =>
            val elem = constructor.find(p => !isValue(p._2)).get
            val newConstructor = constructor + (elem._1 -> stepExpr(elem._2)(vars, ct))
            (Replicate(varId, refId, classType, newConstructor), vars)

        case Transaction(Skip, _) =>
            store.closeTransaction()
            (Skip, vars)
        case Transaction(Error, except) =>
            store.closeTransaction()
            (except, vars)
        case Transaction(body, except) =>
            store.getCurrentTransaction match {
                case Some(_) => ()
                case None => Some(store.startTransaction())
            }
            val (s1, r1) = stepStmt(body, vars)
            (Transaction(s1, except), r1)

        case Print(expression) if isValue(expression) =>
            println(expression)
            (Skip, vars)
        case Print(expression) =>
            (Print(stepExpr(expression)(vars, ct)), vars)

        case s => throw ExecutionError(s"invalid statement: $s")
    }

    def location(refId: String, classType: ClassType): String = s"$refId-$classType"
}
