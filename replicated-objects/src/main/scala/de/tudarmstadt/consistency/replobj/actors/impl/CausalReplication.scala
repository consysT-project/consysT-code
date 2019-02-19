package de.tudarmstadt.consistency.replobj.actors.impl

import akka.actor.ActorRef
import de.tudarmstadt.consistency.replobj.ConsistencyLevels.Inconsistent
import de.tudarmstadt.consistency.replobj.actors.impl.ObjectActor.{FieldGet, FieldSet, MethodInv}

import scala.reflect.runtime.universe._

/**
	* Created on 18.02.19.
	*
	* @author Mirko Köhler
	*/
object CausalReplication extends SingleLeaderReplication {

	class LeaderActor[T <: AnyRef](protected var obj : T, protected implicit val objtag : TypeTag[T])
		extends super.LeaderActor[T, Inconsistent] {

		override protected def consistencyTag : TypeTag[Inconsistent] = typeTag[Inconsistent]




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

	class FollowerActor[T <: AnyRef](protected val leader : ActorRef, protected implicit val objtag : TypeTag[T])
		extends super.FollowerActor[T, Inconsistent] {

		var obj : T = _

		override protected def consistencyTag : TypeTag[Inconsistent] = typeTag[Inconsistent]

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
