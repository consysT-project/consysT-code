package de.tuda.stg.consys.invariants.lang.interpreter

import de.tuda.stg.consys.core.store.akka.levels.Weak
import de.tuda.stg.consys.invariants.lang.Program.Tx
import de.tuda.stg.consys.invariants.lang.ast.Expression._
import de.tuda.stg.consys.invariants.lang.ast.Statement._
import de.tuda.stg.consys.invariants.lang._
import de.tuda.stg.consys.invariants.lang.ast.{Expression, Statement}
import de.tuda.stg.consys.invariants.lang.interpreter.AkkaInterpreter.{StoredObj, TxContext}
import de.tuda.stg.consys.invariants.lang.interpreter.Interpreter.VarEnv

object SimpleInterpreter extends Interpreter {

  case class Obj(c : ClassId, fields : Map[FieldId, Val])

  override type Store = Map[RefId, Obj]
  override type TxContext = Store

  override def interpExpr(env : VarEnv, txContext : TxContext, expr : Expression) : Val = expr match {
    case EField(f) =>
      val VRef(c, ref) = env(thsId)
      txContext(ref).fields(f)

    case _ => super.interpExpr(env, txContext, expr)
  }

  override def interpStmt(ct : ClassTable, env : VarEnv, txContext : TxContext, stmt : Statement) : (Val, Store) = {
    stmt match {
      case DoNew(x, c, fields, body) =>
        val cls = ct(c)

        val store1 = txContext + (x -> Obj(c, cls.fields.zip(fields).map(f => (f._1.name, interpExpr(env, txContext, f._2))).toMap))
        val env1 = env + (x -> VRef(c, x))

        val res = interpStmt(ct, env1, store1, body)
        res


      case DoSetField(x, f, e, body) =>
        val VRef(c, ref) = env(thsId)
        val obj = txContext(ref)

        val newVal = interpExpr(env, txContext, e)
        val newObj = obj.copy(fields = obj.fields + (f -> newVal))

        val env1 = env + (x -> newVal)
        val store1 = txContext + (ref -> newObj)
        interpStmt(ct, env1, store1, body)

      case _ => super.interpStmt(ct, env, txContext, stmt)

    }
  }

  override def interpTx(ct : ClassTable, store : Store, tx : Tx) : Store =
    interpStmt(ct, Map(), store, tx.stmt)._2

}
