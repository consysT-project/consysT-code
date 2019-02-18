package de.tudarmstadt.consistency.replobj.actors

import akka.actor.{ActorPath, ActorRef, ActorSystem, Props}
import akka.util.Timeout
import de.tudarmstadt.consistency.replobj.{DistributedStore, Ref}
import de.tudarmstadt.consistency.replobj.actors.impl.ObjActor.{FieldGet, FieldSet, MethodInv, Print}

import scala.concurrent.Await
import scala.concurrent.duration._
import scala.language.postfixOps
import scala.reflect.runtime.universe._

/**
	* Created on 13.02.19.
	*
	* @author Mirko Köhler
	*/
trait ActorStore extends DistributedStore[String, ActorPath] {

	implicit val actorSystem : ActorSystem


	override def distribute[T : TypeTag, L : TypeTag](addr : String, value : T) : Ref[T, L] =
		throw new UnsupportedOperationException("unknown consistency level: " + implicitly[TypeTag[L]])


		//TODO: replicate can return even though the state replication has not finished yet. Thus it can include "future updates" that happened after the call
	override def replicate[T : TypeTag, L : TypeTag](path : ActorPath) : Ref[T, L] =
		throw new UnsupportedOperationException("unknown consistency level: " + implicitly[TypeTag[L]])


	protected def getMaster(path : ActorPath) : ActorRef = {
		Await.result(actorSystem.actorSelection(path).resolveOne(10 seconds), 12 seconds)
	}



}
