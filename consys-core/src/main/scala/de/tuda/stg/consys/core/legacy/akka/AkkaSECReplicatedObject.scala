package de.tuda.stg.consys.core.legacy.akka

trait AkkaSECReplicatedObject[Addr, T]
  extends AkkaReplicatedObject[Addr, T]
{
  override def internalInvoke[R](tx : Transaction, methodName : String, args : Seq[Seq[Any]]) : R =
  {
    super.internalInvoke[R](tx, methodName, args)
  }
  final override def internalSetField(tx : Transaction, fldName : String, newVal : Any) : Unit =
  {
    throw new UnsupportedOperationException("setting fields not supported on this object")
  }
  override def internalGetField[R](tx : Transaction, fieldName : String) : R =
  {
    super.internalGetField[R](tx, fieldName)
  }
  final override protected def internalSync(): Unit =
  {
    throw new UnsupportedOperationException("sync not supported on this object")
  }
  override protected def transactionStarted(tx : Transaction) : Unit =
  {
    super.transactionStarted(tx)
  }
  override protected def transactionFinished(tx : Transaction) : Unit =
  {
    super.transactionFinished(tx)
  }
}
