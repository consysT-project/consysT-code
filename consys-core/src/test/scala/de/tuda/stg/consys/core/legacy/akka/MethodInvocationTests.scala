package de.tuda.stg.consys.core.legacy.akka

import de.tuda.stg.consys.core.legacy.ConsistencyLabel.Strong
import org.scalatest.fixture

/**
	* Created on 03.07.19.
	*
	* @author Mirko Köhler
	*/
class MethodInvocationTests extends fixture.FunSuite with AkkaReplicaSystemSuite {

	import MethodInvocationTests._

	override def numOfReplicas : Int = 2

	test("testOverloadedMethodsWithPrimitives") { F =>
		val a0 = F(0).replicate("a", A(33), Strong)
		val a1 = F(1).lookup[A]("a", Strong)

		//Invoke overloaded methods on master
		a0.invoke("inc", Seq(Seq())) //empty parameter list
		a0.invoke("inc", Seq(Seq(43)))
		a0.invoke("incAndGet", Seq()) //no parameter list
		a0.invoke("incAndGet", Seq(Seq(123)))

		//Invoke overloaded methods on follower
		a1.invoke("inc", Seq(Seq()))
		a1.invoke("inc", Seq(Seq(7654)))
		a1.invoke("incAndGet", Seq())
		a1.invoke("incAndGet", Seq(Seq(7652)))

		//Check correct results
		assertResult(15509)(a0.getField("i"))
	}


	test("testOverloadedMethodsWithStrings") { F =>
		val b0 = F(0).replicate("b", B("one"), Strong)
		val b1 = F(1).lookup[B]("b", Strong)

		//Invoke overloaded methods on master
		b0.invoke("add", Seq(Seq()))
		b0.invoke("add", Seq(Seq("two")))
		b0.invoke("add", Seq(Seq("three")))

		//Invoke overloaded methods on follower
		b1.invoke("add", Seq(Seq()))
		b1.invoke("add", Seq(Seq("four")))
		b1.invoke("add", Seq(Seq("five")))

		//Check correct results
		assertResult("onewowtwothreewowfourfive")(b0.getField("s"))
	}
}

object MethodInvocationTests {

	case class A(var i : Int) {
		def inc() : Unit = {
			i += 1
		}
		def incAndGet : Int = {
			i += 1
			i
		}
		def inc(amount : Int) : Unit = {
			i += amount
		}
		def incAndGet(amount : Int) : Int = {
			i += amount
			i
		}
	}

	case class B(var s : String) {

		def add(x : String) : Unit = {
			s = s + x
		}

		def add(x : String, y : String) : Unit = {
			s = s + x + y
		}

		def add() : Unit = {
			s = s + "wow"
		}

	}
}
