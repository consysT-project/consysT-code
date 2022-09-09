package de.tuda.stg.consys.invariants.lang.syntax

import de.tuda.stg.consys.invariants.lang.TypeSystem
import de.tuda.stg.consys.invariants.lang.ast.{Expression, Statement}
import de.tuda.stg.consys.invariants.lang.interpreter.{SimpleExec, SimpleInterpreter}

object Main {

  def main(args : Array[String]) : Unit = {
    val expr : Expression =
      Let ("x" := Num(42), "y" := Plus("x", 23)) in
        Plus("x", "y")

    val stmt : Statement =
      Do ("x" << New("Counter", 42)) in (
        Do ("y" << Set("f", 23)) in (
          Return("y")
        )
      )

    TypeSystem.checkExpr(Map.empty, expr)
    val result = SimpleInterpreter.interpExpr(Map.empty, expr)
    println(result)
  }
}
