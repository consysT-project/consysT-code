package de.tuda.consys.formalization

import de.tuda.consys.formalization.lang._
import de.tuda.stg.consys.core.store.cassandra.CassandraStore

class Interpreter(storeAddress: String) {
    private type VarEnv = Map[VarId, Value]

    val store = CassandraStore.fromAddress(storeAddress, 9042, 2181, "datacenter1", initialize = true)

    def run(programDecl: ProgramDecl): Value = {
        interpret(programDecl.body, Map.empty)(programDecl.classTable)
    }

    private def interpret(expr: IRExpr, varEnv: VarEnv)(implicit classTable: ClassTable): Value = expr match {
        case Num(n) => NumV(n)
        case True => BoolV(true)
        case False => BoolV(false)
        case UnitLiteral => UnitV

        case Var(id) => varEnv(id)

        case Let(id, namedExpr, body) =>
            val e = interpret(namedExpr, varEnv)
            interpret(body, varEnv + (id -> e))

        case If(conditionExpr, thenExpr, elseExpr) =>
            val c = interpret(conditionExpr, varEnv)
            c match {
                case BoolV(true) => interpret(thenExpr, varEnv)
                case BoolV(false) => interpret(elseExpr, varEnv)
            }

        case Equals(e1, e2) =>
            val v1 = interpret(e1, varEnv)
            val v2 = interpret(e2, varEnv)
            (v1, v2) match {
                case (NumV(n1), NumV(n2)) => BoolV(n1 == n2)
                case (BoolV(b1), BoolV(b2)) => BoolV(b1 == b2)
                case (StringV(s1), StringV(s2)) => BoolV(s1 == s2)
                case (UnitV, UnitV) => BoolV(true)
                case _ => ???
            }

        case Sequence(exprs) =>
            exprs.foldLeft[Value](UnitV)((r, e) => interpret(e, varEnv))

        case New(objectId, classId, typeArguments, consistency, args) => ???

        case This => varEnv("this")

        case GetField(fieldId) => ???

        case SetField(fieldId, value) => ???

        case CallQuery(recv, methodId, arguments) => ???

        case CallUpdate(recv, methodId, arguments) => ???
    }
}
