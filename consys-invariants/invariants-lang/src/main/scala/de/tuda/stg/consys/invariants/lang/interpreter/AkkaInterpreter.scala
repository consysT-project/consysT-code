package de.tuda.stg.consys.invariants.lang.interpreter
import de.tuda.stg.consys.core.store.akka.levels.Weak
import de.tuda.stg.consys.core.store.akka.{AkkaStore, AkkaTransactionContext}
import de.tuda.stg.consys.invariants.lang.ast.Expression._
import de.tuda.stg.consys.invariants.lang.ast.Statement._
import de.tuda.stg.consys.invariants.lang.interpreter.Interpreter.VarEnv
import de.tuda.stg.consys.invariants.lang._
import de.tuda.stg.consys.invariants.lang.ast.Statement
import de.tuda.stg.consys.invariants.lang.interpreter.SimpleInterpreter.{interpExpr, interpStmt}
import de.tuda.stg.consys.logging.Logger

import scala.collection.mutable

object AkkaInterpreter extends Interpreter {

  case class StoredObj(clsId : ClassId, fields : mutable.Map[FieldId, Val]) extends Serializable {

    def getField(f : FieldId) :  Val = fields(f)
    def setField(f : FieldId, value : Val) = fields.put(f, value)


  }


  override type Store = AkkaStore
  override type TxContext = AkkaTransactionContext


  override def interpStmt(ct : ClassTable, env : VarEnv, txContext : TxContext, stmt : Statement) : (Val, TxContext) = stmt match {
    case Return(e) => (interpExpr(env, e), txContext)

    case DoNew(x, c, fields, body) =>
      val cls = ct(c)
      val objFields : mutable.Map[FieldId, Val] = mutable.HashMap.empty

      objFields.addAll(cls.fields.zip(fields).map(f => (f._1.name, interpExpr(env, f._2))))

      val ref = txContext.replicate[StoredObj](x, Weak, c, objFields)
      val env1 = env + (x -> VRef(c, ref.addr))

      interpStmt(ct, env1, txContext, body)

    case DoGetField(x, field, body) =>
      val VRef(c, ref) = env(thsId)
      val obj = txContext.lookup[StoredObj](ref, Weak)

      val fldVal = obj.resolve(txContext).invoke[Val]("getField", Seq(Seq(field)))

      val env1 = env + (x -> fldVal)
      interpStmt(ct, env1, txContext, body)

    case DoSetField(x, f, e, body) =>
      val newVal = interpExpr(env, e)

      val VRef(c, ref) = env(thsId)
      val obj = txContext.lookup[StoredObj](ref, Weak)

      obj.resolve(txContext).invoke[Val]("setField", Seq(Seq(f, newVal)))

      val env1 = env + (x -> newVal)
      interpStmt(ct, env1, txContext, body)


    case DoCallMethod(x, recv, m, args, body) =>
      val ths@VRef(_, _) = interpExpr(env, recv)

      val mDef = ct(ths.clsId).getMethod(m).get

      val argVals = args.map(e => interpExpr(env, e))
      val mEnv : VarEnv = mDef.parameters.map(vDef => vDef.name).zip(argVals).toMap + (thsId -> ths)

      val mRes = interpStmt(ct, mEnv, txContext, mDef.body)

      val newEnv = env + (x -> mRes._1)
      interpStmt(ct, newEnv, txContext, body)



  }

  override def interpTx(ct : ClassTable, store : Store, tx : Program.Tx) : Store = {

    val txResult : Option[Val] = store.transaction { context =>
      try {
        val (value, _) = interpStmt(ct, Map(), context, tx.stmt)
        Some(value)
      } catch {
        case e : Throwable =>
          e.printStackTrace(Logger.err)
          None
      }
    }

    store
  }
}
