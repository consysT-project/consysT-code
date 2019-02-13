package de.tudarmstadt.consistency.multinode

import akka.actor.{Actor, Props}
import akka.remote.testkit.MultiNodeSpec
import akka.testkit.ImplicitSender
import akka.util.Timeout
import de.tudarmstadt.consistency.multinode.schema.A
import de.tudarmstadt.consistency.replobj.actors.ActorStore

import scala.concurrent.Await
import scala.concurrent.duration._


/**
	* Created on 08.02.19.
	*
	* @author Mirko Köhler
	*/
class ConsistencyActorDemo extends MultiNodeSpec(ConsistencyActorDemoConfig)
  with STMultiNodeSpec with ImplicitSender {

  import ConsistencyActorDemoConfig._

  def initialParticipants : Int = roles.size


  runOn(node1) {
    println("started node1...")

    implicit val timeout : Timeout = Timeout(5 seconds)
	  val store = new ActorStore

	  enterBarrier("init")

	  val a = store.distribute("a", A())

	  enterBarrier("deployed")

	  a("f") = 4
	  val f : Int = a("f")
    println("node1: " + f)

//    val ponger = system.actorSelection(node(node2) / "user" / "ponger")
//    val response = Await.result(ponger ? "ping", 5 seconds)

    enterBarrier("finished")
  }



  runOn(node2) {

    println("started node2...")

	  val store = new ActorStore

	  enterBarrier("init")

//    system.actorOf(Props[Ponger], "ponger")

    enterBarrier("deployed")

	  val replica = store.replicate[A, Nothing](node(node1) / "user" / "a")
	  val f : Int = replica("f")

	  println("node2: " + f)

    enterBarrier("finished")
  }

}