package de.tudarmstadt.stg.consistencytypes.preprocessor

import java.io._
import java.util.regex.Matcher

/**
	* Created on 15.02.19.
	*
	* @author Mirko Köhler
	*/
object Preprocessor {

	private val mthdInvokeRegex = "(?<inv>(\\w+)\\.remote\\.(\\w+)\\((.*)\\))".r
	private	val fldSetRegex = "(?<fldset>(\\w+)\\.remote\\.(\\w+)\\s*=([^\n;]*))".r
	private val fldGetRegex = "(?<fldget>(\\w+)\\.remote\\.(\\w+))".r


	def preprocess(text : String) : String = {
		/*TODO: we have to do three passes over the string because we cannot differentiate between capturing groups*/

		val s0 = text

		val s1 = mthdInvokeRegex.replaceAllIn(s0, matched => {
			val List(_, recv, mthd, args) = matched.subgroups
			if (args.isEmpty)	s"""$recv.<=("$mthd")"""
			else s"""$recv.<=("$mthd", $args)"""
		})


		//Important: fldset before fldget
		val s2 = fldSetRegex.replaceAllIn(s1, matched => {
			val List(_, recv, fld, value) = matched.subgroups
			s"""$recv.update("$fld", $value)"""
		})

		val s3 = fldGetRegex.replaceAllIn(s2, matched => {
			val List(_, recv, fld) = matched.subgroups
			s"""$recv("$fld")"""
		})

		s3
	}


	def preprocessFile(file : File) : Unit = {
		val reader = new BufferedReader(new InputStreamReader(new FileInputStream(file)))

	}


	def main(args : Array[String]) : Unit = {
		println(preprocess(
			"""b.remote.f = 3
				|println(a.remote.foo)
				|
				|c.remote.max(4, 3, 2)
				|a.remote.inc()
				|
				|println(42)""".stripMargin)
		)
	}

}
