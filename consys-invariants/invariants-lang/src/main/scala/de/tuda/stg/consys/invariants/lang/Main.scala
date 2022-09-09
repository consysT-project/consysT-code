package de.tuda.stg.consys.invariants.lang

import de.tuda.stg.consys.core.store.akka.AkkaStore
import de.tuda.stg.consys.core.store.akka.levels.Weak
import de.tuda.stg.consys.invariants.lang.ClassDef.{FieldDef, MethodDef, VarDef}
import de.tuda.stg.consys.invariants.lang.Program.Tx
import de.tuda.stg.consys.invariants.lang.ast.Expression
import de.tuda.stg.consys.invariants.lang.ast.Expression._
import de.tuda.stg.consys.invariants.lang.ast.Statement._
import de.tuda.stg.consys.invariants.lang.ast.Type._
import de.tuda.stg.consys.invariants.lang.interpreter.AkkaInterpreter.StoredObj
import de.tuda.stg.consys.invariants.lang.interpreter.{AkkaExec, SimpleExec, SimpleInterpreter}
import de.tuda.stg.consys.logging.Logger

object Main {

	def main(args : Array[String]) : Unit = {



		val ct : ClassTable = ClassTable(
			ClassDef(name = "Counter",
				fields = Seq(FieldDef(TInt, "i")),
				methods = Seq(
					MethodDef(TInt, "get", Seq(),
						DoGetField("x", "i",
							Return(EVar(x = "x")())()
						)()
					),
					MethodDef(TUnit, "inc", Seq(),
						DoGetField("x1", "i",
							DoSetField("x2", "i", EPlus(VInt(1), EVar("x1")())(),
								Return(VUnit)()
							)()
						)()
					)
				)
			),
			ClassDef(name = "BoxCounter",
				fields = Seq(FieldDef(TRef("Counter"), "v")),
				methods = Seq(
					MethodDef(TRef("Counter"), "get", Seq(),
						DoGetField("x", "v",
							Return(EVar("x")())()
						)()
					),
					MethodDef(TUnit, "inc", Seq(),
						DoGetField("f1", "v",
							DoCallMethod("x1", EVar("f1")(), "inc", Seq(),
								Return(VUnit)()
							)()
						)()
					)
				)
			)
		)

		val program = Program(ct,
			Tx(
				DoNew("counter", "Counter", Seq(VInt(42)),
					DoNew("box", "BoxCounter", Seq(EVar("counter")()),
						DoCallMethod("x1", EVar("box")(), "inc", Seq(),
							Return(EVar("box")())()
						)()
					)()
				)()
			)
		)



		val types = TypeSystem.checkProg(program)
		val result1 = SimpleInterpreter.interpProg(Map(), program)

		println(result1)
		println(types)


		val akkaStore1 = AkkaStore.fromAddress("127.0.0.1", 4445, 2181)
		val exec = new AkkaExec(akkaStore1)

		val result2 = exec.exec(program)
		println(result2)



		akkaStore1.transaction { ctx =>
			val ref1 = ctx.lookup[StoredObj]("box", Weak)
			Logger.info(ref1.resolve().invoke[String]("toString", Seq()))

			val ref2 = ctx.lookup[StoredObj]("counter", Weak)
			Logger.info(ref2.resolve().invoke[String]("toString", Seq()))
			Some(42)
		}





	}

}
