package de.tudarmstadt.consistency.replobj.actors

import akka.actor.ActorRef
import de.tudarmstadt.consistency.replobj.actors.ConsistencyLevels.Weak
import de.tudarmstadt.consistency.replobj.actors.ObjActor._

import scala.reflect.runtime.universe._


/**
	* Weak consistent actors propagate their changes to other actors, but
	* the updates can be applied in a different order on each replica and
	* thus leading to inconsistent replicas.
	*
	* @author Mirko Köhler
	*/
private[actors] object WeakActors {

	class LeaderActor[T <: AnyRef](protected var obj : T, protected implicit val objtag : TypeTag[T]) extends LeaderObjActor[T, Weak] {

		override protected def consistencytag : TypeTag[Weak] = typeTag[Weak]

		override def receive : Receive = {
			/*object operations*/
			case MethodInv(mthdName, args) =>
				val res = invoke[Any](mthdName, args : _*)
				sender() ! res
				val msg = Invoked(mthdName, args) //TODO: Only send invoked when method mutates object
				followers.foreach { ref =>
					ref ! msg
				}

			case FieldGet(fldName) => //No coordination needed in the get case
				val res = getField[Any](fldName)
				sender() ! res

			case FieldSet(fldName, value) =>
				setField[Any](fldName, value)
				val msg = Set(fldName, value)
				followers.foreach { ref =>
					ref ! msg
				}

			/*Coordination with other actors*/
			case msg@Invoked(mthdName, args) =>
				invoke[Any](mthdName, args : _*)
				followers.foreach { ref =>
					if (ref != sender()) ref ! msg
				}

			case msg@Set(fldName, value) =>
				setField[Any](fldName, value)
				followers.foreach { ref =>
					if (ref != sender()) ref ! msg
				}

			case msg => super.receive(msg)

		}

	}


	class FollowerActor[T <: AnyRef](protected val leader : ActorRef, protected implicit val objtag : TypeTag[T]) extends FollowerObjActor[T, Weak] {

		var obj : T = _

		override protected def consistencytag : TypeTag[Weak] = typeTag[Weak]

		override def receive : Receive = {
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

			/*Coordination with other actors*/
			case Invoked(mthdName, args) =>
				invoke[Any](mthdName, args : _*)

			case Set(fldName, value) =>
				setField[Any](fldName, value)

			case msg => super.receive(msg)

		}
	}



}
