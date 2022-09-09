package de.tuda.stg.consys.invariants.lang.interpreter

import de.tuda.stg.consys.core.store.akka.AkkaStore

class AkkaExec(override val store : AkkaStore) extends Exec {

  override type Store = AkkaInterpreter.Store
  override type Interp = AkkaInterpreter.type

  override def interp : Interp = AkkaInterpreter

}
