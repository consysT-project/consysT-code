package de.tuda.stg.consys.invariants.lang.test

import de.tuda.stg.consys.invariants.lang.ast.Type.TInt

object Test {

	trait Expr {
		def children : Seq[Expr]

		def unapply(arg : Expr) : Option[Seq[Expr]] = Some(children)
	}

	case class N(i : Int) extends Expr {
		override def children = Seq.empty[Expr]
	}

	case class Plus(e1 : Expr, e2 : Expr) extends Expr {
		override def children : Seq[Expr] = Seq(e1, e2)
	}


	trait Typ

	case object IntTyp extends Typ


	trait Typed { Expr =>
		def typ : Typ
	}


	def main(args : Array[String]) : Unit = {
		val x : Expr with Typed = new N(1) with Typed {
			override def typ : Typ = IntTyp
		}

		x match {
			case n : N with Typed => println(s"${n.typ} ${n.i}")
		}


		println(x)
	}






}
