package de.tuda.stg.consys.invariants.lang.interpreter


import de.tuda.stg.consys.core.store.akka.levels.Weak
import de.tuda.stg.consys.invariants.lang.Program.Tx
import de.tuda.stg.consys.invariants.lang._
import de.tuda.stg.consys.invariants.lang.ast.Expression._
import de.tuda.stg.consys.invariants.lang.ast.Statement.{DoCallMethod, DoExpr, DoNew, DoSetField, Return}
import de.tuda.stg.consys.invariants.lang.ast.{Expression, Statement}
import de.tuda.stg.consys.invariants.lang.interpreter.AkkaInterpreter.{StoredObj, TxContext, interpExpr}
import de.tuda.stg.consys.invariants.lang.interpreter.Interpreter.VarEnv

import scala.collection.mutable

trait Interpreter {

  type Store
  type TxContext

  def interpExpr(env : VarEnv, txContext : TxContext, expr : Expression) : Val = expr match {
    case v : Val => v

    case EVar(x) => env(x)

    case ELet(x, namedExpr, body) =>
      val v1 = interpExpr(env, txContext, namedExpr)
      interpExpr(env + (x -> v1), txContext, body)

    case EPair(e1, e2) =>
      val v1 = interpExpr(env, txContext, e1)
      val v2 = interpExpr(env, txContext, e2)
      VPair(v1, v2)

    case EPlus(e1, e2) =>
      val VInt(i1) = interpExpr(env, txContext, e1)
      val VInt(i2) = interpExpr(env, txContext, e2)
      VInt(i1 + i2)

    case EFst(e) =>
      val VPair(v1, v2) = interpExpr(env, txContext, e)
      v1

    case ESnd(e) =>
      val VPair(v1, v2) = interpExpr(env, txContext, e)
      v2
  }

  def interpStmt(ct : ClassTable, env : VarEnv, txContext : TxContext, stmt : Statement) : (Val, TxContext) = stmt match {
    case Return(e) => (interpExpr(env, txContext, e), txContext)

    case DoExpr(x, expr, body) =>
      val exprVal = interpExpr(env, txContext, expr)
      interpStmt(ct, env + (x -> exprVal), txContext, body)


    case DoCallMethod(x, recv, m, args, body) =>
      val ths@VRef(_, _) = interpExpr(env, txContext, recv)

      val mDef = ct(ths.clsId).getMethod(m).get

      val argVals = args.map(e => interpExpr(env, txContext, e))
      val mEnv : VarEnv = mDef.parameters.map(vDef => vDef.name).zip(argVals).toMap + (thsId -> ths)

      val mRes = interpStmt(ct, mEnv, txContext, mDef.body)

      val newEnv = env + (x -> mRes._1)
      interpStmt(ct, newEnv, mRes._2, body)
  }


  def interpTx(ct : ClassTable, store : Store, tx : Tx) : Store

  def interpTxs(ct : ClassTable, store : Store, txs : Seq[Tx]) : Store =
    txs.foldLeft(store)((str, tx) => interpTx(ct, str, tx) )

  def interpProg(store : Store, prog : Program) : Store =
    interpTxs(prog.ct, store, prog.txs)

}

object Interpreter {
  type VarEnv = Map[VarId, Val]

}
