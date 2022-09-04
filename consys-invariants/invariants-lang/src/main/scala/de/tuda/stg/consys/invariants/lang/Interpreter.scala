package de.tuda.stg.consys.invariants.lang

import de.tuda.stg.consys.invariants.lang.Expr._
import de.tuda.stg.consys.invariants.lang.Stmt.{DoCallMethod, DoGetField, DoNew, DoSetField, Return}

object Interpreter {

  def interpExpr(env: VarEnv, expr: Expr): Val = expr match {
    case v: Val => v

    case Var(x) => env(x)

    case LetExpr(x, e, body) =>
      val v1 = interpExpr(env, e)
      interpExpr(env + (x -> v1), body)

    case PairExpr(e1, e2) =>
      val v1 = interpExpr(env, e1)
      val v2 = interpExpr(env, e2)
      PairVal(v1, v2)

    case PlusOp(e1, e2) =>
      val IntVal(i1) = interpExpr(env, e1)
      val IntVal(i2) = interpExpr(env, e2)
      IntVal(i1 + i2)

    case FstOp(e) =>
      val PairVal(v1, v2) = interpExpr(env, e)
      v1

    case SndOp(e) =>
      val PairVal(v1, v2) = interpExpr(env, e)
      v2
  }


  def interpStmt(ct: ClsTable, env: VarEnv, store: Store, stmt: Stmt): (Val, Store) = {
    stmt match {
      case Return(e) => (interpExpr(env, e), store)

      case DoNew(x, c, fields, body) =>
        val cls = ct(c)
        require(cls.fields.keys == fields.keys)
        require(!store.contains(x))

        val store1 = store + (x -> Obj(c, fields.map(t => (t._1, interpExpr(env, t._2)))))
        val env1 = env + (x -> RefVal(c, x))

        val res = interpStmt(ct, env1, store1, body)
        res

      case DoGetField(x, f, body) =>
        val RefVal(c, ref) = env(thsId)
        val obj = store(ref)

        val env1 = env + (x -> obj.fields(f))
        interpStmt(ct, env1, store, body)

      case DoSetField(x, f, e, body) =>
        val RefVal(c, ref) = env(thsId)
        val obj = store(ref)

        val newVal = interpExpr(env, e)
        val newObj = obj.copy(fields = obj.fields + (f -> newVal))

        val env1 = env + (x -> newVal)
        val store1 = store + (ref -> newObj)
        interpStmt(ct, env1, store1, body)

      case DoCallMethod(x, recv, m, args, body) =>
        val ths@RefVal(c, ref) = interpExpr(env, recv)
        val obj = store(ref)

        val argVals = args.map(e => interpExpr(env, e))

        val mDef = ct(obj.c).methods(m)
        val mEnv: VarEnv = mDef.pars.map(vDef => vDef.x).zip(argVals).toMap + (thsId -> ths)

        val mRes = interpStmt(ct, mEnv, store, mDef.stmt)

        val newEnv = env + (x -> mRes._1)
        interpStmt(ct, newEnv, mRes._2, body)
    }
  }

  def interpProg(ct : ClsTable, store: Store, prog: Prog): Store =
    prog.txs.foldLeft(store)((str, tx) => {
      val res = interpStmt(ct, Map(), str, tx.stmt)
      res._2
    })


}
