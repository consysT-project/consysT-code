package de.tuda.stg.consys.invariants.lang

import de.tuda.stg.consys.invariants.lang.Cls.{FieldDef, MethodDef}
import de.tuda.stg.consys.invariants.lang.Expr._
import de.tuda.stg.consys.invariants.lang.Stmt.{DoCallMethod, DoGetField, DoNew, DoSetField, Return}
import de.tuda.stg.consys.invariants.lang.Type.{TInt, TUnit}

object Main {

	def main(args : Array[String]) : Unit = {

		val ct : ClsTable = Map(
			"Counter" -> Cls(
				fields = Map("i" -> FieldDef(TInt)),
				methods = Map(
					"get" -> MethodDef(TInt, Seq(),
						DoGetField("x", "i",
							Return(Var("x"))
						)
					),
					"inc" -> MethodDef(TUnit, Seq(),
						DoGetField("x1", "i",
							DoSetField("x2", "i", PlusOp(IntVal(1), Var("x1")),
								Return(UnitVal)
							)
						)
					)
				)
			)
		)

		val stmt =
			DoNew("counter", "Counter" , Map("i" -> IntVal(42)),
				DoCallMethod("x1", Var("counter"), "inc", Seq(),
					Return(Var("counter"))
				)
			)


		val v = Stmt.interp(ct, Map(), Map(), stmt)

		println(v)

	}

}
