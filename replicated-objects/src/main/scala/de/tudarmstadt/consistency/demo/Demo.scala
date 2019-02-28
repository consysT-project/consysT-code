package de.tudarmstadt.consistency.demo

import java.io.{ByteArrayOutputStream, ObjectOutputStream, OutputStream}

import akka.actor.ActorSystem
import de.tudarmstadt.consistency.replobj.ConsistencyLevels.Weak
import de.tudarmstadt.consistency.replobj.{ConsistencyLevels, ReplicaSystem, ReplicatedObject}
import de.tudarmstadt.consistency.replobj.actors.{AkkaReplicaSystem, NewObject}

import scala.reflect.runtime.universe._

/**
	* Created on 27.02.19.
	*
	* @author Mirko Köhler
	*/
object Demo extends App {


	val system = ActorSystem.create("demo")

	val replica : ReplicaSystem[String] = AkkaReplicaSystem.create[String](system, "replica1")

	val ref  = replica.replicate[A, Weak]("a", A(3))

	ref("i") = 55
	println(ref("i"))

}

case class A(i : Int)