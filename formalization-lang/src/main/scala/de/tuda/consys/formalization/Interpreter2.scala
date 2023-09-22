package de.tuda.consys.formalization
/*
import de.tuda.consys.formalization.lang._
import de.tuda.consys.formalization.lang.errors.ExecutionError
import de.tuda.consys.formalization.lang.types.ConsistencyType
import de.tuda.stg.consys.core.store.cassandra.CassandraStore

class Interpreter2(storeAddress: String) {
    private type VarEnv = Map[VarId, Value]

    private val store = CassandraStore.fromAddress(storeAddress, 9042, 2181, "datacenter1", initialize = true)

    def run(programDecl: ProgramDecl): Value = {
        val r1 = interpret(programDecl.body, Map.empty)(programDecl.classTable, None)
        val r2 = interpret(programDecl.returnExpr, r1)(programDecl.classTable, None)
        store.close()
        r2
    }

    def stepExpr(e: Expression)(implicit vars: VarEnv): Expression = e match {
        case Var(id) =>
            ValueExpr(vars(id))

        case This =>
            ValueExpr(vars(thisId))

        case Equals(expr1, expr2) => ???

        case Add(ValueExpr(NumV(n1)), ValueExpr(NumV(n2))) => ValueExpr(NumV(n1 + n2))

        case Add(ValueExpr(NumV(n1)), expr2) => Add(ValueExpr(NumV(n1)), stepExpr(expr2))

        case Add(expr1, expr2) => Add(stepExpr(expr1), expr2)
    }

    def stepRhs(rhs: AssignRhs)(implicit vars: VarEnv): AssignRhs = rhs match {
        case rhsExpression(e) => rhsExpression(stepExpr(e))

        case rhsGetField(fieldId) =>
            vars(thisId) match {
                case RefV(objectId, classId, consistencyArgs) => ???

                case ObjV(classId, fields) =>
                    rhsValue(fields(fieldId))

                case _ =>
                    throw ExecutionError("wrong value for <this>")
            }

        case rhsReplicate(location, classId, consistencyArguments, typeArguments, constructor, consistency, mutability) => ???

        case rhsLookup(location, classId, consistencyArguments, typeArguments, consistency, mutability) => ???

        case rhsCallQuery(recvExpr, methodId, argumentExprs) => ???
    }

    def stepRhsQuery(rhs: AssignRhs)(implicit vars: VarEnv): Statement = rhs match {
        case rhsCallQuery(ValueExpr(v0), methodId, argumentExprs) => ???
    }

    def stepStmt(stmt: Statement, vars: VarEnv): (Statement, VarEnv) = stmt match {
        case Skip => (Skip, vars)
        case Error => (Error, vars)

        case Block(s) => ???

        case Sequence(Skip, s2) => (Skip, vars)
        case Sequence(Error, s2) => (Error, vars)
        case Sequence(s1, s2) =>
            val (r1, vars1) = stepStmt(s1, vars)
            (Sequence(r1, s2), vars1)

        case If(conditionExpr, thenStmt, elseStmt) => ???
        case Let(varId, rhs) => ???
        case Assign(varId, rhs) => ???
        case SetField(fieldId, valueExpr) => ???
        case CallUpdate(recvExpr, methodId, argumentExprs) => ???
        case Transaction(body, except) => ???
    }
}

object Interpreter2 {
    private class ReplicatedState(var objectId: String,
                                  var consistency: ConsistencyType,
                                  var fields: Map[FieldId, Value]
                                 ) extends Serializable
}


 */