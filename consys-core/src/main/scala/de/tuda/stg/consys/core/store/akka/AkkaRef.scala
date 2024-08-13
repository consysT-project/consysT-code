package de.tuda.stg.consys.core.store.akka

import de.tuda.stg.consys.core.store.Ref

import scala.reflect.ClassTag

case class AkkaRef[T <: AkkaStore#ObjType : ClassTag](
  addr : AkkaStore#Addr,
  level : AkkaStore#Level
) extends Ref[AkkaStore, T] with java.io.Serializable {

  def resolve(tx : AkkaStore#TxContext) : AkkaStore#HandlerType[T] =
    new AkkaHandler(tx, this)

  /* This method is for convenience use in transactions or when TxContext is not passed around */
  def resolve() : AkkaStore#HandlerType[T] = AkkaStores.getCurrentTransaction match {
    case None => throw new IllegalStateException(s"can not resolve handler for <$addr>. no active transaction.")
    case Some(tx) => resolve(tx)
  }

}
