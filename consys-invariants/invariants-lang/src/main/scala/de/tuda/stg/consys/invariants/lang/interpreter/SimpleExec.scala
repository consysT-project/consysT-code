package de.tuda.stg.consys.invariants.lang.interpreter

object SimpleExec extends Exec {
  override type Store = SimpleInterpreter.Store
  override type Interp = SimpleInterpreter.type

  override def store : Store = Map()

  override def interp : Interp = SimpleInterpreter
}
