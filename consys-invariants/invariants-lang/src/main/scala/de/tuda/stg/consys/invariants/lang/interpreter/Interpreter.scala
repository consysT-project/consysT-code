package de.tuda.stg.consys.invariants.lang.interpreter

import de.tuda.stg.consys.invariants.lang.Expr.{FstOp, IntVal, LetExpr, PairExpr, PairVal, PlusOp, SndOp, Val, Var}
import de.tuda.stg.consys.invariants.lang.Prog.Tx
import de.tuda.stg.consys.invariants.lang._
import de.tuda.stg.consys.invariants.lang.interpreter.Interpreter.VarEnv

trait Interpreter {

  type Store
  type TxContext

  def interpExpr(env : VarEnv, expr : Expr) : Val = expr match {
    case v : Val => v

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

  def interpStmt(ct : ClsTable, env : VarEnv, txContext : TxContext, stmt : Stmt) : (Val, TxContext)

  def interpTx(ct : ClsTable, store : Store, tx : Tx) : Store

  def interpTxs(ct : ClsTable, store : Store, txs : Seq[Tx]) : Store =
    txs.foldLeft(store)((str, tx) => interpTx(ct, str, tx) )

  def interpProg(store : Store, prog : Prog) : Store =
    interpTxs(prog.ct, store, prog.txs)

}

object Interpreter {
  type VarEnv = Map[VarId, Val]

}
