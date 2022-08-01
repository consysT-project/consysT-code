package de.tuda.stg.consys.core.store.akka.utils

import akka.actor.{ActorSystem, ExtendedActorSystem}

object AkkaUtils {

	type AkkaAddress = akka.actor.Address

	def getActorSystemAddress(system : ActorSystem) : AkkaAddress =
		system.asInstanceOf[ExtendedActorSystem].provider.getDefaultAddress

}
