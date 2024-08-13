package de.tuda.stg.consys.core.store.akkacluster

import de.tuda.stg.consys.core.store.Ref

import scala.reflect.ClassTag

case class AkkaClusterRef[T <: AkkaClusterStore#ObjType : ClassTag](
  addr : AkkaClusterStore#Addr,
  level : AkkaClusterStore#Level
) extends Ref[AkkaClusterStore, T] with java.io.Serializable {

  def resolve(tx : AkkaClusterStore#TxContext) : AkkaClusterStore#HandlerType[T] =
    new AkkaClusterHandler(tx, this)

  /* This method is for convenience use in transactions or when TxContext is not passed around */
  def resolve() : AkkaClusterStore#HandlerType[T] = AkkaClusterStores.getCurrentTransaction match {
    case None => throw new IllegalStateException(s"can not resolve handler for <$addr>. no active transaction.")
    case Some(tx) => resolve(tx)
  }

}
