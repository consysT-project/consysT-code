package de.tuda.stg.consys.core.store.akka

import de.tuda.stg.consys.core.store.Ref

import scala.reflect.ClassTag

case class AkkaRef[T <: AkkaStore#ObjType : ClassTag](
  addr : AkkaStore#Addr,
  level : AkkaStore#Level
) extends Ref[AkkaStore, T] with java.io.Serializable {

  def resolve(tx : AkkaTransactionContext) : AkkaStore#HandlerType[T] =
    new AkkaHandler(tx, this)

}
