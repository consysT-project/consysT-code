package de.tuda.consys.formalization.lang

import de.tuda.stg.consys.core.store.cassandra.CassandraStore

class SmallStepInterpreter(storeAddress: String) {
    private type VarEnv = Map[VarId, Expression]

    private trait VarEnvStack {
        def apply(id: VarId): Expression
        def popped: VarEnvStack
        def pushed: VarEnvStack
        def +(elem: (VarId, Expression)): VarEnvStack
        def -(elem: VarId): VarEnvStack
        def --(elems: IterableOnce[VarId]): VarEnvStack
    }

    private case object EmptyVarEnvStack extends VarEnvStack {
        def apply(id: VarId): Expression = ???
        def popped(): VarEnvStack = ???
        def pushed(): VarEnvStack = ???
        def +(elem: (VarId, Expression)): VarEnvStack = ???
        def -(elem: VarId): VarEnvStack = ???
        def --(elems: IterableOnce[VarId]): VarEnvStack = ???
    }

    private case class ConcreteVarEnvStack(top: VarEnv, tail: VarEnvStack) extends VarEnvStack {
        def apply(id: VarId): Expression = top(id)
        def popped: VarEnvStack = tail
        def pushed: VarEnvStack = ConcreteVarEnvStack(Map.empty, this)
        def +(elem: (VarId, Expression)): VarEnvStack = ConcreteVarEnvStack(top + elem, tail)
        def -(elem: VarId): VarEnvStack = ConcreteVarEnvStack(top - elem, tail)
        def --(elems: IterableOnce[VarId]): VarEnvStack = ConcreteVarEnvStack(top -- elems, tail)
    }

    private val store = CassandraStore.
        fromAddress(storeAddress, 9042, 2181, "datacenter1", initialize = true)

    def run(programDecl: ProgramDecl): Unit = {
        interpret(programDecl.body)
        store.close()
    }

    private def interpret(stmt: Statement): Unit = {
        var s = stmt
        var varEnv: VarEnvStack = ConcreteVarEnvStack(Map.empty, EmptyVarEnvStack)
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
        case Ref(_, _, _) => true
        case LocalObj(_, constructor, _, _) => constructor.forall(p => isValue(p._2))
        case _ => false
    }

    private def stepExpr(e: Expression)(implicit vars: VarEnvStack): Expression = e match {
        case Var(id) => vars(id)

        case Equals(e1, e2) if isValue(e1) && isValue(e2) =>
            if (e1 == e2) True
            else False

        case Equals(e1, e2) if isValue(e1) => Equals(e1, stepExpr(e2))

        case Equals(e1, e2) => Equals(stepExpr(e1), e2)

        case Add(Num(n1), Num(n2)) => Num(n1 + n2)

        case Add(Num(n1), expr2) => Add(Num(n1), stepExpr(expr2))

        case Add(expr1, expr2) => Add(stepExpr(expr1), expr2)
    }

    private def stepStmt(s: Statement, vars: VarEnvStack): (Statement, VarEnvStack) = s match {
        case Skip => (Skip, vars)
        case Error => (Error, vars)

        case Return => (Skip, vars.popped)

        case ReturnExpr(e) if isValue(e) =>
            (ReturnExpr(stepExpr(e)(vars)), vars)
        case ReturnExpr(e) =>
            (Skip, vars.popped + (resId -> e))

        case Block(blockVars, Skip) => (Skip, vars -- blockVars)
        case Block(blockVars, Error) => (Error, vars -- blockVars)
        case Block(blockVars, s) =>
            val (s1, r1) = stepStmt(s, vars)
            (Block(blockVars, s1), r1)

        case Sequence(Error, Return) => (Error, vars.popped)
        case Sequence(Error, ReturnExpr(_)) => (Error, vars.popped)
        case Sequence(Error, _) => (Error, vars)
        case Sequence(Skip, s2) => (s2, vars)
        case Sequence(s1, s2) =>
            val (s1R, varsR) = stepStmt(s1, vars)
            (Sequence(s1R, s2), varsR)

        case If(conditionExpr, thenStmt, _) if conditionExpr == True => (thenStmt, vars)
        case If(conditionExpr, _, elseStmt) if conditionExpr == False => (elseStmt, vars)
        case If(conditionExpr, thenStmt, elseStmt) =>
            val e = stepExpr(conditionExpr)(vars)
            (If(e, thenStmt, elseStmt), vars)

        case Let(varId, e) if isValue(e) => (Skip, vars + (varId -> e))
        case Let(varId, e) => (Let(varId, stepExpr(e)(vars)), vars)

        case SetField(fieldId, valueExpr) if isValue(valueExpr) => ???
        case SetField(fieldId, valueExpr) =>
            val e = stepExpr(valueExpr)(vars)
            (SetField(fieldId, e), vars)

        case GetField(varId, fieldId) => ???

        case CallUpdate(recvExpr, methodId, argumentExprs) if isValue(recvExpr) && argumentExprs.forall(isValue) => ???
        case CallUpdate(recvExpr, methodId, argumentExprs) if isValue(recvExpr) =>
            val i = argumentExprs.indexWhere(p => !isValue(p))
            val newArguments = argumentExprs.zipWithIndex.map(t =>
                if (t._2 == i)
                    stepExpr(argumentExprs(i))(vars)
                else t._1)
            (CallUpdate(recvExpr, methodId, newArguments), vars)
        case CallUpdate(recvExpr, methodId, argumentExprs) =>
            val e = stepExpr(recvExpr)(vars)
            (CallUpdate(e, methodId, argumentExprs), vars)

        case CallUpdateThis(methodId, argumentExprs) =>
            (CallUpdate(vars(thisId), methodId, argumentExprs), vars)

        case CallQuery(varId, recvExpr, methodId, argumentExprs) if isValue(recvExpr) && argumentExprs.forall(isValue) => ???
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

        case Replicate(varId, refId, classType, constructor, consistency, mutability) => ???

        case Transaction(body, except) => ???

        case Print(expression) if isValue(expression) =>
            println(expression)
            (Skip, vars)
    }
}

object SmallStepInterpreter {
    private class ReplicatedState(var fields: Map[FieldId, Expression]) extends Serializable
}
