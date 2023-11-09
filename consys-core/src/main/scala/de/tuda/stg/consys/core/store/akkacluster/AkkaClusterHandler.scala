package de.tuda.stg.consys.core.store.akkacluster

import de.tuda.stg.consys.core.store.Handler

import scala.reflect.ClassTag

class AkkaClusterHandler[T <: AkkaClusterStore#ObjType : ClassTag](
  val txContext : AkkaClusterStore#TxContext,
  val ref : AkkaClusterRef[T]
) extends Handler[AkkaClusterStore, T] {

  def store : AkkaClusterStore = txContext.store
  def addr : AkkaClusterStore#Addr = ref.addr
  def level : AkkaClusterStore#Level = ref.level

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
