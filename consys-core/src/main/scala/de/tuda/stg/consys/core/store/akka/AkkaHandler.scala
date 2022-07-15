package de.tuda.stg.consys.core.store.akka

import de.tuda.stg.consys.core.store.Handler

class AkkaHandler[T <: AkkaStore#ObjType] (
   val addr : AkkaStore#Addr,
   val level : AkkaStore#Level
) extends Handler[AkkaStore, T] {
  /** Invokes a method on the stored object. */
  override def invoke[R](methodId: String, args: Seq[Seq[Any]]): R = ???

  /** Reads a field of the stored object. */
  override def getField[R](fieldName: String): R = ???

  /** Writes a field of the stored object */
  override def setField[R](fieldName: String, value: R): Unit = ???
}
