package de.tuda.stg.consys.invariants.lang

import de.tuda.stg.consys.invariants.lang.Program.Tx
import de.tuda.stg.consys.invariants.lang.ast.Statement

case class Program(ct : ClassTable, txs : Tx*)

object Program {
  case class Tx(stmt : Statement)
}
