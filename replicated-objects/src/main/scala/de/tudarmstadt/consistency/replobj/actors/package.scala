package de.tudarmstadt.consistency.replobj

import akka.actor.{ActorPath, ActorSystem}

/**
	* Created on 15.02.19.
	*
	* @author Mirko Köhler
	*/
package object actors {

	def store(implicit system : ActorSystem) : DistributedStore[String, ActorPath] = new ActorStore
		with WeakActorStore
		with InconsistentActorStore {
			override implicit val actorSystem : ActorSystem = system
		}
}
