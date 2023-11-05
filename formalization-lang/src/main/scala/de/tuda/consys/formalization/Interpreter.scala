package de.tuda.consys.formalization

import de.tuda.consys.formalization.backend.Store
import de.tuda.consys.formalization.lang.ClassTable.ClassTable
import de.tuda.consys.formalization.lang._
import de.tuda.consys.formalization.lang.errors.ExecutionError

class Interpreter(storeAddress: String) {
    private type VarEnv = Map[VarId, Expression]

    private val store = Store.
        fromAddress(storeAddress, 9042, 2181, "datacenter1", initialize = true)

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
        case Ref(_, _, _, _) => true
        case LocalObj(_, constructor) => constructor.forall(p => isValue(p._2))
        case _ => false
    }

    private def stepExpr(e: Expression)(implicit vars: VarEnv): Expression = e match {
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
                case Some(value) => LocalObj(classType, constructor + value)
                case None => throw ExecutionError("invalid execution path")
            }
    }

    private def stepStmt(s: Statement, vars: VarEnv)(implicit ct: ClassTable): (Statement, VarEnv) = s match {
        case ReturnExpr(e) if !isValue(e) =>
            (ReturnExpr(stepExpr(e)(vars)), vars)

        case Block(blockVars, Skip) => (Skip, vars -- blockVars.map(_._2))
        case Block(blockVars, Error) => (Error, vars -- blockVars.map(_._2))
        case Block(blockVars, ReturnExpr(e)) if isValue(e) => (ReturnExpr(e), vars -- blockVars.map(_._2))
        case Block(blockVars, s) if blockVars.forall(v => isValue(v._3)) =>
            val (s1, r1) = stepStmt(s, vars ++ blockVars.map(v => v._2 -> v._3))
            (Block(blockVars, s1), r1)
        case Block(blockVars, s) =>
            val i = blockVars.indexWhere(p => !isValue(p._3))
            val newBlockVars = blockVars.zipWithIndex.map(t =>
                if (t._2 == i)
                    (blockVars(i)._1, blockVars(i)._2, stepExpr(blockVars(i)._3)(vars))
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
            val e = stepExpr(conditionExpr)(vars)
            (If(e, thenStmt, elseStmt), vars)

        case While(condition, stmt) => (If(condition, Sequence(stmt, While(condition, stmt)), Skip), vars)

        case Let(varId, e) if isValue(e) => (Skip, vars + (varId -> e))
        case Let(varId, e) => (Let(varId, stepExpr(e)(vars)), vars)

        case SetField(fieldId, valueExpr) if isValue(valueExpr) =>
            val thisObj = vars(thisId).asInstanceOf[Ref]
            val handler = store.getCurrentTransaction.get.resolveHandler(thisObj.id, thisObj.classType) // TODO: typed id
            handler.setField(fieldId, valueExpr)
            (Skip, vars)
        case SetField(fieldId, valueExpr) =>
            val e = stepExpr(valueExpr)(vars)
            (SetField(fieldId, e), vars)

        case GetField(varId, fieldId) if vars(thisId).isInstanceOf[Ref] =>
            val thisObj = vars(thisId).asInstanceOf[Ref]
            val handler = store.getCurrentTransaction.get.resolveHandler(thisObj.id, thisObj.classType) // TODO: typed id
            (Skip, vars + (varId -> handler.getField(fieldId)))
        case GetField(varId, fieldId) if vars(thisId).isInstanceOf[LocalObj] =>
            val thisObj = vars(thisId).asInstanceOf[LocalObj]
            (Skip, vars + (varId -> thisObj.constructor(fieldId)))

        case CallUpdate(varId, recvExpr, methodId, argumentExprs) if isValue(recvExpr) && argumentExprs.forall(isValue) =>
            val recvRef = recvExpr.asInstanceOf[Ref]
            val mBody = ClassTable.mBody(methodId, recvRef.classType)
            mBody match {
                case _: UpdateBody =>
                case _: QueryBody => throw ExecutionError(s"invalid method sort for update ($methodId)")
            }
            val handler = store.getCurrentTransaction.get.resolveHandler(recvRef.id, recvRef.classType) // TODO: typed id
            handler.invoke(mBody.operationLevel)
            val argumentBindings = (mBody.arguments zip argumentExprs).map(p => p._1 -> p._2).toMap
            (EvalUpdate(varId, recvExpr, methodId, argumentBindings + (thisId -> recvRef), mBody.body), vars)
        case CallUpdate(varId, recvExpr, methodId, argumentExprs) if isValue(recvExpr) =>
            val i = argumentExprs.indexWhere(p => !isValue(p))
            val newArguments = argumentExprs.zipWithIndex.map(t =>
                if (t._2 == i)
                    stepExpr(argumentExprs(i))(vars)
                else t._1)
            (CallUpdate(varId, recvExpr, methodId, newArguments), vars)
        case CallUpdate(varId, recvExpr, methodId, argumentExprs) =>
            val e = stepExpr(recvExpr)(vars)
            (CallUpdate(varId, e, methodId, argumentExprs), vars)

        case CallUpdateThis(varId, methodId, argumentExprs) =>
            (CallUpdate(varId, vars(thisId), methodId, argumentExprs), vars)

        case CallQuery(varId, recvExpr, methodId, argumentExprs) if isValue(recvExpr) && argumentExprs.forall(isValue) =>
            val recvRef = recvExpr.asInstanceOf[Ref]
            val mBody = ClassTable.mBody(methodId, recvRef.classType)
            mBody match {
                case _: QueryBody =>
                case _: UpdateBody => throw ExecutionError(s"invalid method sort for update ($methodId)")
            }
            val handler = store.getCurrentTransaction.get.resolveHandler(recvRef.id, recvRef.classType) // TODO: typed id
            handler.invoke(mBody.operationLevel)
            val argumentBindings = (mBody.arguments zip argumentExprs).map(p => p._1 -> p._2).toMap
            (EvalQuery(varId, recvExpr, methodId, argumentBindings + (thisId -> recvRef), mBody.body), vars)
        case CallQuery(varId, recvExpr, methodId, argumentExprs) if isValue(recvExpr) =>
            val i = argumentExprs.indexWhere(p => !isValue(p))
            val newArguments = argumentExprs.zipWithIndex.map(t =>
                if (t._2 == i)
                    stepExpr(argumentExprs(i))(vars)
                else t._1)
            (CallQuery(varId, recvExpr, methodId, newArguments), vars)
        case CallQuery(varId, recvExpr, methodId, argumentExprs) =>
            val e = stepExpr(recvExpr)(vars)
            (CallQuery(varId, e, methodId, argumentExprs), vars)

        case CallQueryThis(varId, methodId, argumentExprs) =>
            (CallQuery(varId, vars(thisId), methodId, argumentExprs), vars)

        case EvalUpdate(_, _, _, _, Error) =>
            (Error, vars)
        case EvalUpdate(varId, _, _, _, ReturnExpr(e)) if isValue(e) =>
            (Skip, vars + (varId -> e))
        case EvalUpdate(varId, recv, methodId, args, body) =>
            val (s1, r1) = stepStmt(body, args)
            val newArgs = r1.filter(r => args.contains(r._1))
            (EvalUpdate(varId, recv, methodId, newArgs, s1), vars)

        case EvalQuery(_, _, _, _, Error) =>
            (Error, vars)
        case EvalQuery(varId, _, _, _, ReturnExpr(e)) if isValue(e) =>
            (Skip, vars + (varId -> e))
        case EvalQuery(varId, recv, methodId, args, body) =>
            val (s1, r1) = stepStmt(body, args)
            val newArgs = r1.filter(r => args.contains(r._1))
            (EvalQuery(varId, recv, methodId, newArgs, s1), vars)

        case Replicate(varId, refId, classType, constructor, consistency, mutability) if constructor.values.forall(isValue) =>
            store.getCurrentTransaction.get.replicateNew(refId, classType, constructor) // TODO: typed id
            (Skip, vars + (varId -> Ref(refId, classType, consistency, mutability)))

        case Replicate(varId, refId, classType, constructor, consistency, mutability) =>
            val elem = constructor.find(p => !isValue(p._2)).get
            val newConstructor = constructor + (elem._1 -> stepExpr(elem._2)(vars))
            (Replicate(varId, refId, classType, newConstructor, consistency, mutability), vars)

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
            (Print(stepExpr(expression)(vars)), vars)

        case s => throw ExecutionError(s"invalid statement: $s")
    }
}
