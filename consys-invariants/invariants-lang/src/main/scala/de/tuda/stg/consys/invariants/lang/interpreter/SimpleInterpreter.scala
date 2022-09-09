package de.tuda.stg.consys.invariants.lang.interpreter

import de.tuda.stg.consys.invariants.lang.Program.Tx
import de.tuda.stg.consys.invariants.lang.ast.Expression._
import de.tuda.stg.consys.invariants.lang.ast.Statement._
import de.tuda.stg.consys.invariants.lang._
import de.tuda.stg.consys.invariants.lang.ast.Statement
import de.tuda.stg.consys.invariants.lang.interpreter.Interpreter.VarEnv

object SimpleInterpreter extends Interpreter {

  case class Obj(c : ClassId, fields : Map[FieldId, Val])

  override type Store = Map[RefId, Obj]
  override type TxContext = Store

  override def interpStmt(ct : ClassTable, env : VarEnv, txContext : TxContext, stmt : Statement) : (Val, Store) = {
    stmt match {
      case Return(e) => (interpExpr(env, e), txContext)

      case DoNew(x, c, fields, body) =>
        val cls = ct(c)

        val store1 = txContext + (x -> Obj(c, cls.fields.zip(fields).map(f => (f._1.name, interpExpr(env, f._2))).toMap))
        val env1 = env + (x -> VRef(c, x))

        val res = interpStmt(ct, env1, store1, body)
        res

      case DoGetField(x, f, body) =>
        val VRef(c, ref) = env(thsId)
        val obj = txContext(ref)

        val env1 = env + (x -> obj.fields(f))
        interpStmt(ct, env1, txContext, body)

      case DoSetField(x, f, e, body) =>
        val VRef(c, ref) = env(thsId)
        val obj = txContext(ref)

        val newVal = interpExpr(env, e)
        val newObj = obj.copy(fields = obj.fields + (f -> newVal))

        val env1 = env + (x -> newVal)
        val store1 = txContext + (ref -> newObj)
        interpStmt(ct, env1, store1, body)

      case DoCallMethod(x, recv, m, args, body) =>
        val ths@VRef(c, ref) = interpExpr(env, recv)
        val obj = txContext(ref)

        val argVals = args.map(e => interpExpr(env, e))

        val mDef = ct(obj.c).getMethod(m).get
        val mEnv : VarEnv = mDef.parameters.map(vDef => vDef.name).zip(argVals).toMap + (thsId -> ths)

        val mRes = interpStmt(ct, mEnv, txContext, mDef.body)

        val newEnv = env + (x -> mRes._1)
        interpStmt(ct, newEnv, mRes._2, body)
    }
  }

  override def interpTx(ct : ClassTable, store : Store, tx : Tx) : Store =
    interpStmt(ct, Map(), store, tx.stmt)._2

}
