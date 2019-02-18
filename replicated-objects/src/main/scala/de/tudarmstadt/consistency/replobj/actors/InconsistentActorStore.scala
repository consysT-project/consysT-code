package de.tudarmstadt.consistency.replobj.actors

import akka.actor.{ActorPath, Props}
import de.tudarmstadt.consistency.replobj.{ConsistencyLevels, Ref}
import de.tudarmstadt.consistency.replobj.actors.impl.SingleLeaderReplication.Init

import scala.reflect.runtime.universe._


/**
	* Created on 15.02.19.
	*
	* @author Mirko Köhler
	*/
trait InconsistentActorStore extends ActorStore {
	import de.tudarmstadt.consistency.replobj.actors.impl.InconsistentReplication._


	override def distribute[T : TypeTag, L : TypeTag](addr : String, value : T) : Ref[T, L] = {
		if (implicitly[TypeTag[L]] == typeTag[ConsistencyLevels.Inconsistent]) {
			new ObjRef[T, L](actorSystem.actorOf(Props(classOf[LeaderActor[T]], value, typeTag[T]), addr))
		} else {
			super.distribute[T, L](addr, value)
		}
	}


	override def replicate[T : TypeTag,	L : TypeTag](path : ActorPath) : Ref[T, L] = {
		if (implicitly[TypeTag[L]] == typeTag[ConsistencyLevels.Inconsistent]) {
			val localActor = actorSystem.actorOf(Props(classOf[FollowerActor[T]], getMaster(path), typeTag[T]))
			localActor ! Init
			new ObjRef[T, L](localActor)
		} else {
			super.replicate[T, L](path)
		}
	}

}
