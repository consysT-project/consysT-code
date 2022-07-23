package de.tuda.stg.consys.core.store.akka

import de.tuda.stg.consys.core.store.Handler
import de.tuda.stg.consys.core.store.cassandra.{CassandraRef, CassandraStore}

import scala.reflect.ClassTag

class AkkaHandler[T <: AkkaStore#ObjType : ClassTag](
  val txContext : AkkaStore#TxContext,
  val ref : AkkaRef[T]
) extends Handler[AkkaStore, T] {

  def store : AkkaStore = txContext.store
  def addr : AkkaStore#Addr = ref.addr
  def level : AkkaStore#Level = ref.level

  override def invoke[R](methodId : String, args : Seq[Seq[Any]]) : R = {
    level.toProtocol(store).invoke[T, R](txContext, ref, methodId, args)
  }

  override def getField[R](fieldName : String) : R = {
    level.toProtocol(store).getField[T, R](txContext, ref, fieldName)
  }

  override def setField[R](fieldName : String, value : R) : Unit = {
    level.toProtocol(store).setField[T, R](txContext, ref, fieldName, value)
  }

}
