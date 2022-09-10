package de.tuda.stg.consys.invariants.lang.interpreter
import de.tuda.stg.consys.core.store.akka.levels.Weak
import de.tuda.stg.consys.core.store.akka.{AkkaStore, AkkaTransactionContext}
import de.tuda.stg.consys.invariants.lang._
import de.tuda.stg.consys.invariants.lang.ast.Expression._
import de.tuda.stg.consys.invariants.lang.ast.{Expression, Statement}
import de.tuda.stg.consys.invariants.lang.ast.Statement._
import de.tuda.stg.consys.invariants.lang.interpreter.Interpreter.VarEnv
import de.tuda.stg.consys.logging.Logger

import scala.collection.mutable

object AkkaInterpreter extends Interpreter {

  case class StoredObj(clsId : ClassId, fields : mutable.Map[FieldId, Val]) extends Serializable {

    def getField(f : FieldId) :  Val = fields(f)
    def setField(f : FieldId, value : Val) : Option[Val] = fields.put(f, value)
  }

  override type Store = AkkaStore
  override type TxContext = AkkaTransactionContext

  override def interpExpr(env : VarEnv, txContext : TxContext, expr : Expression) : Val = expr match {
    case EField(f) =>
      val VRef(c, ref) = env(thsId)
      val obj = txContext.lookup[StoredObj](ref, Weak)
      val fldVal = obj.resolve(txContext).invoke[Val]("getField", Seq(Seq(f)))
      fldVal

    case _ => super.interpExpr(env, txContext, expr)
  }


  override def interpStmt(ct : ClassTable, env : VarEnv, txContext : TxContext, stmt : Statement) : (Val, TxContext) = stmt match {
    case DoNew(x, c, fields, body) =>
      val cls = ct(c)
      val objFields : mutable.Map[FieldId, Val] = mutable.HashMap.empty

      objFields.addAll(cls.fields.zip(fields).map(f => (f._1.name, interpExpr(env, txContext, f._2))))

      val ref = txContext.replicate[StoredObj](x, Weak, c, objFields)
      val env1 = env + (x -> VRef(c, ref.addr))

      interpStmt(ct, env1, txContext, body)

    case DoSetField(x, f, e, body) =>
      val newVal = interpExpr(env, txContext, e)

      val VRef(c, ref) = env(thsId)
      val obj = txContext.lookup[StoredObj](ref, Weak)

      obj.resolve(txContext).invoke[Val]("setField", Seq(Seq(f, newVal)))

      val env1 = env + (x -> newVal)
      interpStmt(ct, env1, txContext, body)


    case _ => super.interpStmt(ct, env, txContext, stmt)
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
