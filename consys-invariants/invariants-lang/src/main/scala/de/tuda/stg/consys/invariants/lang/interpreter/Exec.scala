package de.tuda.stg.consys.invariants.lang.interpreter

import de.tuda.stg.consys.invariants.lang.{Prog, TypeSystem}

trait Exec {

  type Store
  type Interp <: Interpreter {type Store = Exec.this.Store}

  def store : Store

  def interp : Interp

  def exec(prog : Prog) : Store = {
    TypeSystem.checkProg(prog)
    interp.interpProg(store, prog)
  }

}
