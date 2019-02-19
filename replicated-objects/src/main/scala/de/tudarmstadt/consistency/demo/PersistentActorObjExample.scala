package de.tudarmstadt.consistency.demo

/**
	* Created on 18.02.19.
	*
	* @author Mirko Köhler
	*/
import akka.actor._
import akka.persistence._
import de.tudarmstadt.consistency.replobj.typeToClassTag

import scala.collection.SortedSet
import scala.reflect.ClassTag
import scala.reflect.runtime.universe._

object PersistentActorObjExample extends App {


	trait Cmd
	case class SetFieldCmd(fldName : String, value : Any) extends Cmd
	case class GetFieldCmd(fldName : String) extends Cmd
	case class InvokeCmd(mthdName : String, args : Seq[Any]) extends Cmd


	trait Op
	case class SetFieldOp(fldName : String, value : Any, currentTime : Long = System.currentTimeMillis()) extends Op
	case class InvokeOp(mthdName : String, args : Seq[Any], currentTime : Long = System.currentTimeMillis()) extends Op


	class ExampleObjPersistentActor[T](val name : String, val obj : T, protected implicit val objtag : TypeTag[T]) extends PersistentActor {
		override def persistenceId : String = name

		private var unapplied: SortedSet[Op] = SortedSet.empty[Op] // state


		private implicit lazy val ct : ClassTag[T]  = typeToClassTag[T] //used as implicit argument
		private lazy val objMirror : InstanceMirror = runtimeMirror(ct.runtimeClass.getClassLoader).reflect(obj)


		def receiveCommand: Receive = {
			case SetFieldCmd(fldName, value) =>

				saveSnapshot()

				persist(SetFieldOp(fldName, value)) { op =>
					unapplied = unapplied + op
				}

			case GetFieldCmd(fldName) =>
				if (unapplied.isEmpty) {
					sender() ! getField(fldName)
				}

				unapplied.foldLeft[Option[Op]](None)((acc, op ) => op match {
					case setField@SetFieldOp(fldName2, _) if (fldName == =>
				})

			case "boom"  => throw new Exception("boom")
			case payload: String =>
				persist(payload) { p => received = p :: received }

		}

		def receiveRecover: Receive = {
			case s: String => received = s :: received
		}



		private def produceObj() : T = {
			var res = obj
		}


		private def invoke[R](methodName : String, args : Any*) : R = {
			val methodSymbol = typeOf[T].decl(TermName(methodName)).asMethod
			val methodMirror = objMirror.reflectMethod(methodSymbol)

			val result = methodMirror.apply(args : _*)

			result.asInstanceOf[R]
		}

		private def getField[R](fieldName : String) : R = {
			val fieldSymbol = typeOf[T].decl(TermName(fieldName)).asTerm
			val fieldMirror = objMirror.reflectField(fieldSymbol)

			val result = fieldMirror.get

			result.asInstanceOf[R]
		}

		private def setField[R](fieldName : String, value : R) : Unit = {
			val fieldSymbol = typeOf[T].decl(TermName(fieldName)).asTerm
			val fieldMirror = objMirror.reflectField(fieldSymbol)

			fieldMirror.set(value)
		}




	}

	val system = ActorSystem("example")
	val persistentActor = system.actorOf(Props(classOf[ExampleObjPersistentActor]), "persistentActor-2")

	persistentActor ! "a"
	persistentActor ! "print"
	persistentActor ! "boom" // restart and recovery
	persistentActor ! "print"
	persistentActor ! "b"
	persistentActor ! "print"
	persistentActor ! "c"
	persistentActor ! "print"

	// Will print in a first run (i.e. with empty journal):

	// received List(a)
	// received List(a, b)
	// received List(a, b, c)

	// Will print in a second run:

	// received List(a, b, c, a)
	// received List(a, b, c, a, b)
	// received List(a, b, c, a, b, c)

	// etc ...

	Thread.sleep(10000)
	system.terminate()
}
