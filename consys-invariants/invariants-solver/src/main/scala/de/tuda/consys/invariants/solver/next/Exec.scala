package de.tuda.consys.invariants.solver.next

import de.tuda.consys.invariants.solver.next.ir.Classes.{ClassType, FieldDecl, ObjectClassDecl, ObjectQueryMethodDecl, ObjectUpdateMethodDecl, ProgramDecl, TypeVar, VarDecl}
import de.tuda.consys.invariants.solver.next.ir.{ClassTable, Natives}
import de.tuda.consys.invariants.solver.next.ir.Natives.{BOOL_TYPE, INT_TYPE, SET_CLASS, STRING_TYPE}
import de.tuda.consys.invariants.solver.next.translate.{ProgramModel, Z3Env}
import de.tuda.stg.consys.logging.Logger

import java.nio.file.{Path, Paths}
import ir.Expressions.UntypedLang

import scala.collection.immutable.Seq
import scala.util.Right

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


	def exampleProgram0() : ProgramDecl[UntypedLang.Expr] = {
		import UntypedLang._

		val boxCls = ObjectClassDecl[UntypedLang.Expr](
			"Box",
			Seq(),
			IRTrue,
			Map(
				"value" -> FieldDecl("value", INT_TYPE)
			),
			Map(
				"getVal" -> ObjectQueryMethodDecl("getVal", Seq(), INT_TYPE, IRGetField("value"))
			)
		)

		ProgramDecl(ClassTable(
			"Int" -> Left(Natives.INT_CLASS),
			"Bool" -> Left(Natives.BOOL_CLASS),
			"String" -> Left(Natives.STRING_CLASS),
			"Unit" -> Left(Natives.UNIT_CLASS),
			"Box" -> Right(boxCls)
		),
			IRUnit
		)
	}


	def exampleProgram1() : ProgramDecl[UntypedLang.Expr] = {
		import UntypedLang._

		val boxCls = ObjectClassDecl[UntypedLang.Expr](
			"Box",
			Seq(),
			IREquals(IRGetField("value"), IRNum(0)),
			Map(
				"value" -> FieldDecl("value", INT_TYPE),
				"name" -> FieldDecl("name", STRING_TYPE)
			),
			Map(
				"setVal" -> ObjectUpdateMethodDecl("setVal", Seq(VarDecl("x", INT_TYPE)),
					IRLet("a0", IRSetField("value", IRVar("x")),
						IRUnit
					)
				),
				"nameLength" -> ObjectUpdateMethodDecl("nameLength", Seq(),
					IRLet("a0",
						IRSetField("value",
							IRIf(IREquals(IRCallQuery(IRGetField("name"), "length", Seq()), IRNum(0)),
								IRCallQuery(IRGetField("name"), "length", Seq()),
								IRNum(0)
							)
						),
						IRUnit
					)
				),
				"foo2" -> ObjectUpdateMethodDecl("foo2", Seq(),
					IRLet("a0", IRCallUpdateThis("setVal", Seq(IRNum(42))),
						IRUnit
					)
				),
				"foo3" -> ObjectUpdateMethodDecl("foo3", Seq(),
					IRLet("a0", IRCallUpdateThis("setVal", Seq(IRNum(0))),
						IRUnit
					)
				),
				"getVal" -> ObjectQueryMethodDecl("getVal", Seq(), INT_TYPE, IRGetField("value")),
				"getVal2" -> ObjectQueryMethodDecl("getVal2", Seq(), INT_TYPE, IRCallQuery(IRThis, "getVal", Seq()))
			)
		)

		val box2Cls = ObjectClassDecl[UntypedLang.Expr](
			"Box2",
			Seq(),
			IREquals(IRCallQuery(IRGetField("box"), "getVal", Seq()), IRNum(0)),
			Map(
				"box" -> FieldDecl("box", boxCls.toType(Seq()))
			),
			Map(
				"setVal" -> ObjectUpdateMethodDecl("setVal", Seq(VarDecl("x", INT_TYPE)),
					IRCallUpdateField("box", "setVal", Seq(IRNum(3)))
				)
			)
		)

		ProgramDecl(ClassTable(
			"Int" -> Left(Natives.INT_CLASS),
			"Bool" -> Left(Natives.BOOL_CLASS),
			"String" -> Left(Natives.STRING_CLASS),
			"Unit" -> Left(Natives.UNIT_CLASS),
			"Box" -> Right(boxCls),
			"Box2" -> Right(box2Cls)
		),
			IRNew("Box", Seq(ClassType("Int", Seq())), Seq(IRNum(42)))
		)
	}

	def exampleProgram2() : ProgramDecl[UntypedLang.Expr] = {
		import ir.Expressions.UntypedLang._

		val boxCls = ObjectClassDecl[UntypedLang.Expr](
			"Box",
			Seq(TypeVar("A")),
			IRTrue,
			Map(
				"value" -> FieldDecl("value", TypeVar("A"))
			),
			Map(
				"setVal" -> ObjectUpdateMethodDecl("setVal", Seq(VarDecl("x", TypeVar("A"))),
					IRLet("a0", IRSetField("value", IRVar("x")),
						IRUnit
					)
				),
				"getVal" -> ObjectQueryMethodDecl("getVal", Seq(), TypeVar("A"), IRGetField("value")),
			)
		)

		val userCls = ObjectClassDecl[UntypedLang.Expr](
			"User",
			Seq(TypeVar("B"), TypeVar("A")),
			IRTrue,
			Map(
				"name" -> FieldDecl("name", ClassType("Box", Seq(TypeVar("B")))),
				"friends" -> FieldDecl("friends", ClassType("Set", Seq(TypeVar("A"))))
			),
			Map(
				"setName" -> ObjectUpdateMethodDecl("setName", Seq(VarDecl("x", TypeVar("B"))),
					IRLet("a0", IRCallUpdateField("name", "setVal", Seq(IRVar("x"))),
						IRUnit
					)
				),
				"getName" -> ObjectQueryMethodDecl("getName", Seq(), TypeVar("B"),
					IRCallQuery(IRGetField("name"), "getVal", Seq())
				),
				"hasFriend" -> ObjectQueryMethodDecl("hasFriend", Seq(VarDecl("x", TypeVar("A"))), BOOL_TYPE,
					IRCallQuery(IRGetField("friends"), "contains", Seq(IRVar("x")))
				)
			)
		)

		val nameCls = ObjectClassDecl[UntypedLang.Expr](
			"Name",
			Seq(),
			IRTrue,
			Map(
				"value" -> FieldDecl("value", STRING_TYPE)
			),
			Map(
				"getValue" -> ObjectQueryMethodDecl("getValue", Seq(), STRING_TYPE,
					IRGetField("value")
				)
			)
		)


		ProgramDecl(ClassTable(
			"Int" -> Left(Natives.INT_CLASS),
			"Bool" -> Left(Natives.BOOL_CLASS),
			"String" -> Left(Natives.STRING_CLASS),
			"Unit" -> Left(Natives.UNIT_CLASS),
			"Set" -> Left(Natives.SET_CLASS),
			"Box" -> Right(boxCls),
			"User" -> Right(userCls),
			"Name" -> Right(nameCls)
		),
			IRNew("Box", Seq(ClassType("Int", Seq())), Seq(IRNum(42)))
		)
	}


	def main(args : Array[String]) : Unit = {
		val prog = exampleProgram2()

		val env = new Z3Env()
		val model = new ProgramModel(env, prog)
		model.create()
	}

}
