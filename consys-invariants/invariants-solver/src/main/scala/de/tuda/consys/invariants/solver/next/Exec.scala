package de.tuda.consys.invariants.solver.next

import de.tuda.consys.invariants.solver.next.ir.Natives
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


	def main(args : Array[String]) : Unit = {
		import ir.IR._

		val cls = ObjectClassDecl(
			"Box",
			Equals(GetField("value"), Num(0)),
			Map("value" -> FieldDecl("value",TClass("Int"))),
			Map("return" -> MethodDecl("return", Seq(VarDecl("x", TClass("Int"))), TClass("Int"), Var("x")))
		)

		val prog = ProgramDecl(Map(
			"Int" -> Natives.INT_CLASS,
			"Box" -> cls
		))

		val env = new Z3Env()
		val model = new ProgramModel(env, prog)
		model.create()
	}

}
