package de.tuda.stg.consys.invariants.lang

import de.tuda.stg.consys.invariants.lang.ClassDef.{FieldDef, MethodDef, VarDef}
import de.tuda.stg.consys.invariants.lang.Program.Tx
import de.tuda.stg.consys.invariants.lang.ast.Expression._
import de.tuda.stg.consys.invariants.lang.ast.Statement._
import de.tuda.stg.consys.invariants.lang.ast.Type._
import de.tuda.stg.consys.invariants.lang.interpreter.SimpleExec

object Main {

	def main(args : Array[String]) : Unit = {


		val tt = TypeSystem.checkValM(VPair(VPair(VInt(42), VInt(23)), VInt(12)))
		println(tt)


		val ct : ClassTable = ClassTable(
			ClassDef(name = "Counter",
				fields = Seq(FieldDef(TInt, "i")),
				methods = Seq(
					MethodDef(TInt, "get", Seq(),
						DoGetField("x", "i",
							Return(EVar("x"))
						)
					),
					MethodDef(TUnit, "inc", Seq(),
						DoGetField("x1", "i",
							DoSetField("x2", "i", EPlus(VInt(1), EVar("x1")),
								Return(VUnit)
							)
						)
					)
				)
			),
			ClassDef(name = "BoxCounter",
				fields = Seq(FieldDef(TRef("Counter"), "v")),
				methods = Seq(
					MethodDef(TRef("Counter"), "get", Seq(),
						DoGetField("x", "v",
							Return(EVar("x"))
						)
					),
					MethodDef(TUnit, "inc", Seq(),
						DoGetField("f1", "v",
							DoCallMethod("x1", EVar("f1"), "inc", Seq(),
								Return(VUnit)
							)
						)
					)
				)
			)
		)

		val program = Program(ct,
			Tx(
				DoNew("counter", "Counter", Seq(VInt(42)),
					DoNew("box", "BoxCounter", Seq(EVar("counter")),
						DoCallMethod("x1", EVar("box"), "inc", Seq(),
							Return(EVar("box"))
						)
					)
				)
			)
		)

		val store = SimpleExec.exec(program)
		println(store)

	}

}
