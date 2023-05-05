package de.tuda.consys.invariants.solver.next

import de.tuda.consys.invariants.solver.next.ir.IR.{ProgramDecl, SetField}
import de.tuda.consys.invariants.solver.next.ir.Natives
import de.tuda.consys.invariants.solver.next.ir.Natives.{BOOL_TYPE, INT_TYPE, STRING_TYPE}
import de.tuda.consys.invariants.solver.next.translate.{ProgramModel, Z3Env}
import de.tuda.stg.consys.logging.Logger

import java.nio.file.{Path, Paths}

object Exec {

	{
		loadZ3Libs()
	}

	private def loadLib(lib : Path) : Unit = {
		val libAbsolute = lib.toAbsolutePath
		Logger.info("load lib: " + libAbsolute)
		System.load(libAbsolute.toString)
	}

	private def loadZ3Libs() : Unit = { // Set the correct lib folder
		val libFolder = Paths.get("consys-invariants", "invariants-solver", "lib")
		// Load the correct libs depending on OS
		val osname = System.getProperty("os.name").toLowerCase
		if (osname.contains("mac")) {
			loadLib(libFolder.resolve("libz3.dylib"))
			loadLib(libFolder.resolve("libz3java.dylib"))
		}
		else if (osname.contains("linux")) {
			loadLib(libFolder.resolve("libz3.so"))
			loadLib(libFolder.resolve("libz3java.so"))
		}
		else throw new RuntimeException("unsupported OS: " + osname)
	}

	def exampleProgram1() : ProgramDecl = {
		import ir.IR._

		val boxCls = ObjectClassDecl(
			"Box",
			Seq(),
			Equals(GetField("value"), Num(0)),
			Map(
				"value" -> FieldDecl("value", INT_TYPE),
				"name" -> FieldDecl("name", STRING_TYPE)
			),
			Map(
				"setVal" -> ObjectUpdateMethodDecl("setVal", Seq(VarDecl("x", INT_TYPE)),
					Let("a0", SetField("value", Var("x")),
						UnitLiteral
					)
				),
				"nameLength" -> ObjectUpdateMethodDecl("nameLength", Seq(),
					Let("a0",
						SetField("value",
							If(Equals(CallQuery(GetField("name"), "length", Seq()), Num(0)),
								CallQuery(GetField("name"), "length", Seq()),
								Num(0)
							)
						),
						UnitLiteral
					)
				),
				"foo2" -> ObjectUpdateMethodDecl("foo2", Seq(),
					Let("a0", CallUpdateThis("setVal", Seq(Num(42))),
						UnitLiteral
					)
				),
				"foo3" -> ObjectUpdateMethodDecl("foo3", Seq(),
					Let("a0", CallUpdateThis("setVal", Seq(Num(0))),
						UnitLiteral
					)
				),
				"getVal" -> ObjectQueryMethodDecl("getVal", Seq(), INT_TYPE, GetField("value")),
				"getVal2" -> ObjectQueryMethodDecl("getVal2", Seq(), INT_TYPE, CallQuery(This, "getVal", Seq()))
			)
		)

		val box2Cls = ObjectClassDecl(
			"Box2",
			Seq(),
			Equals(CallQuery(GetField("box"), "getVal", Seq()), Num(0)),
			Map(
				"box" -> FieldDecl("box", boxCls.toType(Seq()))
			),
			Map(
				"setVal" -> ObjectUpdateMethodDecl("setVal", Seq(VarDecl("x", INT_TYPE)),
					CallUpdateField("box", "setVal", Seq(Num(3)))
				)
			)
		)

		ProgramDecl(Map(
			"Int" -> Natives.INT_CLASS,
			"Bool" -> Natives.BOOL_CLASS,
			"String" -> Natives.STRING_CLASS,
			"Unit" -> Natives.UNIT_CLASS,
			"Box" -> boxCls,
			"Box2" -> box2Cls
		))
	}

	def exampleProgram2() : ProgramDecl = {
		import ir.IR._

		val boxCls = ObjectClassDecl(
			"Box",
			Seq(TypeVar("A")),
			True,
			Map(
				"value" -> FieldDecl("value", TypeVar("A"))
			),
			Map(
				"setVal" -> ObjectUpdateMethodDecl("setVal", Seq(VarDecl("x", TypeVar("A"))),
					Let("a0", SetField("value", Var("x")),
						UnitLiteral
					)
				),
				"getVal" -> ObjectQueryMethodDecl("getVal", Seq(), TypeVar("A"), GetField("value")),
			)
		)

		val userCls = ObjectClassDecl(
			"User",
			Seq(TypeVar("B"), TypeVar("A")),
			True,
			Map(
				"name" -> FieldDecl("name", ClassType("Box", Seq(TypeVar("B")))),
				"friends" -> FieldDecl("friends", ClassType("Set", Seq(TypeVar("A"))))
			),
			Map(
				"setName" -> ObjectUpdateMethodDecl("setName", Seq(VarDecl("x", TypeVar("B"))),
					Let("a0", CallUpdateField("name", "setVal", Seq(Var("x"))),
						UnitLiteral
					)
				),
				"getName" -> ObjectQueryMethodDecl("getName", Seq(), TypeVar("B"),
					CallQuery(GetField("name"), "getVal", Seq())
				),
				"hasFriend" -> ObjectQueryMethodDecl("hasFriend", Seq(VarDecl("x", TypeVar("A"))), BOOL_TYPE,
					CallQuery(GetField("friends"), "contains", Seq(Var("x")))
				)
			)
		)


		ProgramDecl(Map(
			"Int" -> Natives.INT_CLASS,
			"Bool" -> Natives.BOOL_CLASS,
			"String" -> Natives.STRING_CLASS,
			"Unit" -> Natives.UNIT_CLASS,
			"Set" -> Natives.SET_CLASS,
			"Box" -> boxCls,
			"User" -> userCls
		))
	}


	def main(args : Array[String]) : Unit = {
		val prog = exampleProgram2()

		val env = new Z3Env()
		val model = new ProgramModel(env, prog)
		model.create()
	}

}
