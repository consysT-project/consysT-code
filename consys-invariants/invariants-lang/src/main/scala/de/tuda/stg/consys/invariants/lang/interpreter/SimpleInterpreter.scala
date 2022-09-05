package de.tuda.stg.consys.invariants.lang.interpreter

import de.tuda.stg.consys.invariants.lang.Expr._
import de.tuda.stg.consys.invariants.lang.Prog.Tx
import de.tuda.stg.consys.invariants.lang.Stmt._
import de.tuda.stg.consys.invariants.lang._
import de.tuda.stg.consys.invariants.lang.interpreter.Interpreter.VarEnv

object SimpleInterpreter extends Interpreter {

  case class Obj(c : ClassId, fields : Map[FieldId, Val])

  override type Store = Map[RefId, Obj]
  override type TxContext = Store

  override def interpStmt(ct : ClsTable, env : VarEnv, txContext : TxContext, stmt : Stmt) : (Val, Store) = {
    stmt match {
      case Return(e) => (interpExpr(env, e), txContext)

      case DoNew(x, c, fields, body) =>
        val cls = ct(c)

        val store1 = txContext + (x -> Obj(c, fields.map(t => (t._1, interpExpr(env, t._2)))))
        val env1 = env + (x -> RefVal(c, x))

        val res = interpStmt(ct, env1, store1, body)
        res

      case DoGetField(x, f, body) =>
        val RefVal(c, ref) = env(thsId)
        val obj = txContext(ref)

        val env1 = env + (x -> obj.fields(f))
        interpStmt(ct, env1, txContext, body)

      case DoSetField(x, f, e, body) =>
        val RefVal(c, ref) = env(thsId)
        val obj = txContext(ref)

        val newVal = interpExpr(env, e)
        val newObj = obj.copy(fields = obj.fields + (f -> newVal))

        val env1 = env + (x -> newVal)
        val store1 = txContext + (ref -> newObj)
        interpStmt(ct, env1, store1, body)

      case DoCallMethod(x, recv, m, args, body) =>
        val ths@RefVal(c, ref) = interpExpr(env, recv)
        val obj = txContext(ref)

        val argVals = args.map(e => interpExpr(env, e))

        val mDef = ct(obj.c).methods(m)
        val mEnv : VarEnv = mDef.pars.map(vDef => vDef.x).zip(argVals).toMap + (thsId -> ths)

        val mRes = interpStmt(ct, mEnv, txContext, mDef.stmt)

        val newEnv = env + (x -> mRes._1)
        interpStmt(ct, newEnv, mRes._2, body)
    }
  }

  override def interpTx(ct : ClsTable, store : Store, tx : Tx) : Store =
    interpStmt(ct, Map(), store, tx.stmt)._2

}
