package de.tuda.stg.consys.invariants.lang.interpreter
import de.tuda.stg.consys.core.store.akka.levels.Weak
import de.tuda.stg.consys.core.store.akka.{AkkaStore, AkkaTransactionContext}
import de.tuda.stg.consys.invariants.lang.Expr.{RefVal, Val}
import de.tuda.stg.consys.invariants.lang.Stmt.{DoCallMethod, DoGetField, DoNew, Return}
import de.tuda.stg.consys.invariants.lang.interpreter.Interpreter.VarEnv
import de.tuda.stg.consys.invariants.lang.{ClassId, ClsTable, Expr, FieldId, Prog, Stmt}

object AkkaInterpreter extends Interpreter {

  case class Obj(c : ClassId, fields : Map[FieldId, Val]) extends Serializable {

  }


  override type Store = AkkaStore
  override type TxContext = AkkaTransactionContext


  override def interpStmt(ct : ClsTable, env : VarEnv, txContext : TxContext, stmt : Stmt) : (Val, TxContext) = stmt match {
    case Return(e) => (interpExpr(env, e), txContext)

    case DoNew(x, c, fields, body) =>
      val cls = ct(c)
      val objFields : Map[FieldId, Val] = fields.map(t => (t._1, interpExpr(env, t._2)))

      val ref = txContext.replicate[Obj](x, Weak, c, objFields)
      val env1 = env + (x -> RefVal(c, ref.addr))

      interpStmt(ct, env1, txContext, body)

    case DoCallMethod(x, recv, m, args, body) =>
      val ths@RefVal(c, ref) = interpExpr(env, recv)
      val thsRef = txContext.lookup[Obj](ref, Weak)

//      val argVals = args.map(e => interpExpr(env, e))
//
//      val mDef = ct(obj.c).methods(m)
//      val mEnv : VarEnv = mDef.pars.map(vDef => vDef.x).zip(argVals).toMap + (thsId -> ths)
//
//      val mRes = interpStmt(ct, mEnv, txContext, mDef.stmt)
//
//      val newEnv = env + (x -> mRes._1)
//      interpStmt(ct, newEnv, mRes._2, body)

    ???


  }

  override def interpTx(ct : ClsTable, store : Store, tx : Prog.Tx) : Store = ???
}
