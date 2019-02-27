package de.tudarmstadt.consistency.replobj.actors.impl

import akka.actor.ActorRef
import de.tudarmstadt.consistency.replobj.ConsistencyLevels.Weak
import de.tudarmstadt.consistency.replobj.actors.impl.ObjectActor._

import scala.reflect.runtime.universe._

/**
	* Weak consistent actors propagate their changes to other actors, but
	* the updates can be applied in a different order on each replica and
	* thus leading to inconsistent replicas.
	*
	* @author Mirko Köhler
	*/
private[actors] object StrongReplication extends SingleLeaderReplication {

	class LeaderActor[T <: AnyRef](protected var obj : T, protected implicit val objtag : TypeTag[T])
		extends super.LeaderActor[T, Weak] {

		override protected def consistencyTag : TypeTag[Weak] = typeTag[Weak]




		override def receiveCommand : PartialFunction[Command, Unit] = {
			/*object operations*/
			case MethodInv(mthdName, args) =>


			case FieldGet(fldName) => //No coordination needed in the get case


			case FieldSet(fldName, value) =>


			case cmd => super.receiveCommand(cmd)
		}

		override def receiveEvent : PartialFunction[Event, Unit] = {
			/*Coordination with other actors*/
			case msg@Invoked(mthdName, args) =>
				invoke[Any](mthdName, args : _*)

				followers.foreach { ref =>
					ref ! Merge(Invoked)
				}

			case msg@Set(fldName, value) =>
				setField[Any](fldName, value)
				followers.foreach { ref =>
					if (ref != sender()) ref ! msg
				}

			case evt => super.receiveEvent(evt)
		}

	}


	class FollowerActor[T <: AnyRef](protected val leader : ActorRef, protected implicit val objtag : TypeTag[T])
		extends super.FollowerActor[T, Weak] {

		var obj : T = _

		override protected def consistencyTag : TypeTag[Weak] = typeTag[Weak]

		override def receiveCommand : PartialFunction[Command, Unit] = {
			/*object operations*/
			case MethodInv(mthdName, args) =>
				val res = invoke[Any](mthdName, args : _*)
				sender() ! res
				leader ! Invoked(mthdName, args) //TODO: Only send invoked when method mutates object


			case FieldGet(fldName) => //No coordination needed in the get case
				val res = getField[Any](fldName)
				sender() ! res

			case FieldSet(fldName, value) =>
				setField[Any](fldName, value)
				leader ! Set(fldName, value)

			case cmd => super.receiveCommand(cmd)
		}


		override def receiveEvent : PartialFunction[Event, Unit] = {
			/*Coordination with other actors*/
			case Invoked(mthdName, args) =>
				invoke[Any](mthdName, args : _*)

			case Set(fldName, value) =>
				setField[Any](fldName, value)

			case evt => super.receiveEvent(evt)
		}
	}


	case class Merge(op : Operation) extends Event


	case class Invoked(methodName : String, args : Seq[Any]) extends Event
	case class Set(fieldName : String, newVal : Any) extends Event
}
