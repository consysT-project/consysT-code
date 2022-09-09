package de.tuda.stg.consys.invariants.lang.interpreter


import de.tuda.stg.consys.invariants.lang.Program.Tx
import de.tuda.stg.consys.invariants.lang._
import de.tuda.stg.consys.invariants.lang.ast.Expression._
import de.tuda.stg.consys.invariants.lang.ast.{Expression, Statement}
import de.tuda.stg.consys.invariants.lang.interpreter.Interpreter.VarEnv

trait Interpreter {

  type Store
  type TxContext

  def interpExpr[A <: Expression](env : VarEnv, expr : A) : Val = expr match {
    case v : Val => v

    case e : EVar => env(e.x)

    case ELet(x, namedExpr, body) =>
      val v1 = interpExpr(env, namedExpr)
      interpExpr(env + (x -> v1), body)

    case EPair(e1, e2) =>
      val v1 = interpExpr(env, e1)
      val v2 = interpExpr(env, e2)
      VPair(v1, v2)

    case EPlus(e1, e2) =>
      val VInt(i1) = interpExpr(env, e1)
      val VInt(i2) = interpExpr(env, e2)
      VInt(i1 + i2)

    case EFst(e) =>
      val VPair(v1, v2) = interpExpr(env, e)
      v1

    case ESnd(e) =>
      val VPair(v1, v2) = interpExpr(env, e)
      v2
  }

  def interpStmt(ct : ClassTable, env : VarEnv, txContext : TxContext, stmt : Statement) : (Val, TxContext)

  def interpTx(ct : ClassTable, store : Store, tx : Tx) : Store

  def interpTxs(ct : ClassTable, store : Store, txs : Seq[Tx]) : Store =
    txs.foldLeft(store)((str, tx) => interpTx(ct, str, tx) )

  def interpProg(store : Store, prog : Program) : Store =
    interpTxs(prog.ct, store, prog.txs)

}

object Interpreter {
  type VarEnv = Map[VarId, Val]

}
