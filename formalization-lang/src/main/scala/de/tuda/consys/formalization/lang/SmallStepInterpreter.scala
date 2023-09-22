package de.tuda.consys.formalization.lang

import de.tuda.stg.consys.core.store.cassandra.CassandraStore

class SmallStepInterpreter(storeAddress: String) {
    private type VarEnv = Map[VarId, Expression]

    private val store = CassandraStore.fromAddress(storeAddress, 9042, 2181, "datacenter1", initialize = true)

    def run(programDecl: ProgramDecl): Unit = {
        interpret(programDecl.body)
        store.close()
    }

    private def interpret(stmt: Statement): Unit = {
        var s = stmt
        var varEnv: List[VarEnv] = List(Map.empty)
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

    private def stepExpr(e: Expression)(implicit vars: List[VarEnv]): Expression = e match {
        case Var(id) => vars.head(id)

        case Equals(e1, e2) if isValue(e1) && isValue(e2) =>
            if (e1 == e2) True
            else False

        case Equals(e1, e2) if isValue(e1) => Equals(e1, stepExpr(e2))

        case Equals(e1, e2) => Equals(stepExpr(e1), e2)

        case Add(Num(n1), Num(n2)) => Num(n1 + n2)

        case Add(Num(n1), expr2) => Add(Num(n1), stepExpr(expr2))

        case Add(expr1, expr2) => Add(stepExpr(expr1), expr2)
    }

    private def stepStmt(s: Statement, vars: List[VarEnv]): (Statement, List[VarEnv]) = s match {
        case Skip => (Skip, vars)
        case Error => (Error, vars)

        case Return => (Skip, vars.tail)

        case ReturnExpr(e) if isValue(e) => (ReturnExpr(stepExpr(e)(vars)), vars)
        case ReturnExpr(e) => (Skip, vars.tail + (resId -> e))

        case Block(vars, s) => ???

        case Sequence(Error, Return) => (Error, vars.tail)
        case Sequence(Error, ReturnExpr(_)) => (Error, vars.tail)
        case Sequence(Error, _) => (Error, vars)
        case Sequence(Skip, s2) => (s2, vars)
        case Sequence(s1, s2) =>
            val (s1R, varsR) = stepStmt(s1, vars)
            (Sequence(s1R, s2), varsR)

        case If(conditionExpr, thenStmt, _) if conditionExpr == True => (thenStmt, vars)
        case If(conditionExpr, _, elseStmt) if conditionExpr == False => (elseStmt, vars)
        case If(conditionExpr, thenStmt, elseStmt) => If(stepExpr(conditionExpr)(vars))

        case Let(varId, e) => ???
        case SetField(fieldId, valueExpr) => ???
        case GetField(varId, fieldId) => ???
        case CallUpdate(recvExpr, methodId, argumentExprs) => ???
        case CallUpdateThis(methodId, argumentExprs) => ???
        case CallQuery(varId, recvExpr, methodId, argumentExprs) => ???
        case CallQueryThis(varId, methodId, argumentExprs) => ???
        case Replicate(varId, refId, classType, constructor, consistency, mutability) => ???
        case Transaction(body, except) => ???
        case Print(expression) => ???
    }
}
