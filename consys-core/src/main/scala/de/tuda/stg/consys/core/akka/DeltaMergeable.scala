package de.tuda.stg.consys.core.akka

trait DeltaMergeable[T] {
  /*
  DeltaType is the type of the delta message. If you have a counter and update with numbers, then Integer
  would be the DeltaType.
   */
  type DeltaType
  private[akka] def merge(other:DeltaType) //T ändern zu etwas anderem, dazu neuen Datentyp erstellen,
                                   // "DeltaMessage" mit entsprechendem delta, bei erstellung angeben

}
