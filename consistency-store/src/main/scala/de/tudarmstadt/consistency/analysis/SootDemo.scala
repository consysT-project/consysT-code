package de.tudarmstadt.consistency.analysis

import java.io._
import java.util

import soot.dava.{Dava, DavaPrinter}
import soot.grimp.Grimp
import soot.jimple.{JasminClass, Jimple, JimpleBody, StringConstant}
import soot.options.Options
import soot.util.JasminOutputStream
import soot.{ArrayType, Modifier, Printer, RefType, Scene, SootClass, SootMethod, SourceLocator, VoidType}

/**
	* Created on 17.12.18.
	*
	* @author Mirko Köhler
	*/
object SootDemo {




	def main(args : Array[String]) : Unit = {
		System.out.println("Generating class...")
		val sClass = generateClass

		System.out.println("Writing class file...")
		write(sClass, Options.output_format_class)

		System.out.println("Writing jimple file...")
		write(sClass, Options.output_format_jimple)

		System.out.println("Writing java file...")
		// Need to convert the jimple body to grimp before I can convert to dava
		val gBody = Grimp.v.newBody(sClass.getMethodByName("main").getActiveBody, "gb")
		val davaBody = Dava.v.newBody(gBody)
		sClass.getMethodByName("main").setActiveBody(davaBody)
		write(sClass, Options.output_format_dava)

		System.out.println("Done")
	}


	def generateClass : SootClass = {
		// Load dependencies
		Scene.v.loadClassAndSupport("java.lang.Object")
		Scene.v.loadClassAndSupport("java.lang.System")

		// Create the class HelloWorld as a public class that extends Object
		val sClass = new SootClass("HelloWorld", Modifier.PUBLIC)
		sClass.setSuperclass(Scene.v.getSootClass("java.lang.Object"))
		Scene.v.addClass(sClass)

		// Create: public static void main(String[])
		val mainMethod = new SootMethod(
			"main",
			util.Arrays.asList(ArrayType.v(RefType.v("java.lang.String"), 1)),
			VoidType.v,
			Modifier.PUBLIC | Modifier.STATIC
		)
		sClass.addMethod(mainMethod)

		// Generate dava body from the jimple body
		val jimpleBody = createJimpleBody(mainMethod)

		// Set the jimple body as the active one
		mainMethod.setActiveBody(jimpleBody)

		sClass
	}



	private def createJimpleBody(method : SootMethod) : JimpleBody = {
		// Create a body for the main method and set it as the active body
		val body = Jimple.v.newBody(method)

		// Create a local to hold the main method argument
		// Note: In general for any use of objects or basic-types, must generate a local to
		// hold that in the method body
		val frm1 = Jimple.v.newLocal("frm1", ArrayType.v(RefType.v("java.lang.String"), 1))
		body.getLocals.add(frm1)

		// Create a local to hold the PrintStream System.out
		val tmpRef = Jimple.v.newLocal("tmpRef", RefType.v("java.io.PrintStream"))
		body.getLocals.add(tmpRef)

		// Create a unit (or statement) that assigns main's formal param into the local arg
		val units = body.getUnits
		units.add(Jimple.v.newIdentityStmt(frm1, Jimple.v.newParameterRef(ArrayType.v(RefType.v("java.lang.String"), 1), 0)))

		// Create a unit that assigns System.out to the local tmpRef
		units.add(Jimple.v.newAssignStmt(tmpRef, Jimple.v.newStaticFieldRef(Scene.v.getField("<java.lang.System: java.io.PrintStream out>").makeRef)))

		// Create the call to tmpRef.println("Hello world!")
		val toCall = Scene.v.getMethod("<java.io.PrintStream: void println(java.lang.String)>")
		units.add(Jimple.v.newInvokeStmt(Jimple.v.newVirtualInvokeExpr(tmpRef, toCall.makeRef, StringConstant.v("Hello world!"))))

		// Add an empty return statement
		units.add(Jimple.v.newReturnVoidStmt)

		body
	}




	private def write(sClass : SootClass, output_format : Int) : Unit = {
		var streamOut : OutputStream = null
		try {
			val filename = SourceLocator.v.getFileNameFor(sClass, output_format)

			if (output_format == Options.output_format_class)
				streamOut = new JasminOutputStream(new FileOutputStream(filename))
			else
				streamOut = new FileOutputStream(filename)

			val writerOut = new PrintWriter(new OutputStreamWriter(streamOut))

			if (output_format == Options.output_format_class)
				new JasminClass(sClass).print(writerOut)
			else if (output_format == Options.output_format_jimple)
				Printer.v.printTo(sClass, writerOut)
			else if
				(output_format == Options.output_format_dava) DavaPrinter.v.printTo(sClass, writerOut)

			writerOut.flush()
			writerOut.close()
		} catch {
			case e : FileNotFoundException =>
				System.out.println(e.getMessage)
				e.printStackTrace()
		} finally {
			if (streamOut != null) try streamOut.close() catch {
				case e : IOException =>
					System.out.println(e.getMessage)
					e.printStackTrace()
			}
		}
	}


}
