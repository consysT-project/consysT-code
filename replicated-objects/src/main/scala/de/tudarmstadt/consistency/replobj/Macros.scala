package de.tudarmstadt.consistency.replobj

import akka.actor.{ActorPath, ActorSystem}
import de.tudarmstadt.consistency.replobj.actors.ActorStore
import de.tudarmstadt.consistency.replobj.actors.ConsistencyLevels.Weak

import scala.language.experimental.macros
import scala.reflect.macros.whitebox

/**
	* Created on 05.02.19.
	*
	* @author Mirko Köhler
	*/
object Macros {

	def m(arg : Int) : String = macro mImpl

	def mImpl(c : whitebox.Context)(arg : c.Expr[Int]) : c.Expr[String] = {
		import c.universe._
		val s = arg.tree.toString()

		c.Expr[String](Literal(Constant(s)))
	}


	class R {
		def remote : Any = sys.error("Oops!")
	}

	def distribute(body : Unit) : Unit = macro distributeImpl


	def distributeImpl()(c : whitebox.Context)(body : c.Tree) : c.Tree = {
		import c.universe._

		val transformer = new Transformer {
			override def transform(tree : Tree) : Tree = tree match {
				case q"$recv.$mthd(..$args)" if args.length == 1 =>
					q"$recv.$mthd(..$args)"
			}
		}

		transformer.transform(body)
	}


	class C { var f : Int = 0}

	val store : DistributedStore[String, ActorPath] = new ActorStore()(actorSystem = ActorSystem.create("test"))


	val a : store.Ref[C, Weak] = store.distribute("x", new C)
	distribute {
		a.remote.f = 3
		println(a.remote.f)
	}

}

