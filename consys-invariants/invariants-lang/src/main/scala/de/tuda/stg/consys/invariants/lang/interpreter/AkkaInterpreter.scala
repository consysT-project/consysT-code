package de.tuda.stg.consys.invariants.lang.interpreter
import de.tuda.stg.consys.core.store.akka.levels.Weak
import de.tuda.stg.consys.core.store.akka.{AkkaStore, AkkaTransactionContext}
import de.tuda.stg.consys.invariants.lang.ast.Expression._
import de.tuda.stg.consys.invariants.lang.ast.Statement._
import de.tuda.stg.consys.invariants.lang.interpreter.Interpreter.VarEnv
import de.tuda.stg.consys.invariants.lang._
import de.tuda.stg.consys.invariants.lang.ast.Statement

object AkkaInterpreter extends Interpreter {

  case class Obj(c : ClassId, fields : Map[FieldId, Val]) extends Serializable {
    def getFields : Map[FieldId, Val] = fields

  }


  override type Store = AkkaStore
  override type TxContext = AkkaTransactionContext


  override def interpStmt(ct : ClassTable, env : VarEnv, txContext : TxContext, stmt : Statement) : (Val, TxContext) = stmt match {
    case Return(e) => (interpExpr(env, e), txContext)

    case DoNew(x, c, fields, body) =>
      val cls = ct(c)
      val objFields : Map[FieldId, Val] = cls.fields.zip(fields).map(f => (f._1.name, interpExpr(env, f._2))).toMap

      val ref = txContext.replicate[Obj](x, Weak, c, objFields)
      val env1 = env + (x -> VRef(c, ref.addr))

      interpStmt(ct, env1, txContext, body)

    case DoCallMethod(x, recv, m, args, body) =>
      val ths@VRef(c, ref) = interpExpr(env, recv)
      val thsRef = txContext.lookup[Obj](ref, Weak)

      val argVals = args.map(e => interpExpr(env, e))

      val mDef = ct(c).methods.find(mDef => mDef.name == m).get
//      val mEnv : VarEnv = mDef.parameters.map(vDef => vDef.x).zip(argVals).toMap + (thsId -> ths)
//
//      val mRes = interpStmt(ct, mEnv, txContext, mDef.stmt)
//
//      val newEnv = env + (x -> mRes._1)
//      interpStmt(ct, newEnv, mRes._2, body)

    ???


  }

  override def interpTx(ct : ClassTable, store : Store, tx : Program.Tx) : Store = ???
}
