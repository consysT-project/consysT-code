package de.tuda.stg.consys.core.store.akka

import de.tuda.stg.consys.core.store.Ref

case class AkkaRef[T <: AkkaStore#ObjType](
  val addr : AkkaStore#Addr,
  val level : AkkaStore#Level
) extends Ref[AkkaStore, T] {

  def resolve(tx : AkkaTransactionContext) : AkkaStore#HandlerType[T] =
    new AkkaHandler(addr, level)
}
