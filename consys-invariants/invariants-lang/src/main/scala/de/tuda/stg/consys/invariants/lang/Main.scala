package de.tuda.stg.consys.invariants.lang

import de.tuda.stg.consys.core.store.akka.AkkaStore
import de.tuda.stg.consys.core.store.akka.levels.Weak
import de.tuda.stg.consys.invariants.lang.ClassTable.start
import de.tuda.stg.consys.invariants.lang.ast.Type._
import de.tuda.stg.consys.invariants.lang.interpreter.AkkaInterpreter.StoredObj
import de.tuda.stg.consys.invariants.lang.interpreter.{AkkaExec, SimpleInterpreter}
import de.tuda.stg.consys.logging.Logger

object Main {

	def main(args : Array[String]) : Unit = {
		import syntax._

		Define Class "Counter" as (
			field("i" :: TInt),

			method("get" :: TInt)() {
				Do ("x" << Get("i")) in
					Return("x")
			},

			method("inc" :: TUnit)() {
				Do ("x1" << Get("i")) in (
					Do ("x2" << Set("i", Plus(1, "x1"))) in
						Return ()
				)
			}
		)

		Define Class "BoxCounter" as (
			field("v" :: TRef("Counter")),

			method("get" :: TRef("Counter"))() {
				Do ("x" << Get("v")) in Return ("x")
			},

			method("inc" :: TUnit)() {
				Do ("x1" << Get("v")) in (
					Do ("x2" << Call("x1", "inc")()) in
						Return ()
				)
			}
		)


		val program = start (
			Do ("counter" << New("Counter", 42)) in (
				Do ("box" << New("BoxCounter", "counter")) in (
					Do ("x1" << Call("box", "inc")()) in
						Return("box")
				)
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
