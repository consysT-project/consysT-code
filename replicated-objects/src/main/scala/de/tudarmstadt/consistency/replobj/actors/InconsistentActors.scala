package de.tudarmstadt.consistency.replobj.actors

import akka.actor.ActorRef
import de.tudarmstadt.consistency.replobj.actors.ConsistencyLevels.{Inconsistent, Weak}
import de.tudarmstadt.consistency.replobj.actors.ObjActor._

import scala.reflect.runtime.universe._


/**
	* Inconsistent actors do not coordinate any updates.
	*
	* @author Mirko Köhler
	*/
private[actors] object InconsistentActors {

	class LeaderActor[T <: AnyRef](protected var obj : T, protected implicit val objtag : TypeTag[T]) extends LeaderObjActor[T, Inconsistent] {

		override protected def consistencytag : TypeTag[Inconsistent] = typeTag[Inconsistent]

		override def receive : Receive = {
			/*object operations*/
			case MethodInv(mthdName, args) =>
				val res = invoke[Any](mthdName, args : _*)
				sender() ! res


			case FieldGet(fldName) => //No coordination needed in the get case
				val res = getField[Any](fldName)
				sender() ! res

			case FieldSet(fldName, value) =>
				setField[Any](fldName, value)
				val msg = Set(fldName, value)

			case msg => super.receive(msg)
		}

	}


	class FollowerActor[T <: AnyRef](protected val leader : ActorRef, protected implicit val objtag : TypeTag[T]) extends FollowerObjActor[T, Inconsistent] {

		var obj : T = _

		override protected def consistencytag : TypeTag[Inconsistent] = typeTag[Inconsistent]

		override def receive : Receive = {
			/*object operations*/
			case MethodInv(mthdName, args) =>
				val res = invoke[Any](mthdName, args : _*)
				sender() ! res



			case FieldGet(fldName) => //No coordination needed in the get case
				val res = getField[Any](fldName)
				sender() ! res

			case FieldSet(fldName, value) =>
				setField[Any](fldName, value)

			case msg => super.receive(msg)
		}
	}



}
