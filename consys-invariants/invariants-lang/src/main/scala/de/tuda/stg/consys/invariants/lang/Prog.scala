package de.tuda.stg.consys.invariants.lang

import de.tuda.stg.consys.invariants.lang.Prog.Tx

case class Prog(txs : Tx*)

object Prog {

  case class Tx(stmt : Stmt)




}
