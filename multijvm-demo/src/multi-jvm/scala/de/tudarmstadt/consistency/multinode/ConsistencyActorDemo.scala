package de.tudarmstadt.consistency.multinode

import akka.actor.{Actor, Props}
import akka.remote.testkit.MultiNodeSpec
import akka.testkit.ImplicitSender
import akka.util.Timeout

import scala.concurrent.Await
import scala.concurrent.duration._


/**
	* Created on 08.02.19.
	*
	* @author Mirko Köhler
	*/
class ConsistencyActorDemo extends MultiNodeSpec(ConsistencyActorDemoConfig)
  with STMultiNodeSpec with ImplicitSender {

  import ConsistencyActorDemo._
  import ConsistencyActorDemoConfig._

  def initialParticipants : Int = roles.size


  runOn(node1) {
    import akka.pattern.ask

    println("started node1...")

    implicit val timeout : Timeout = Timeout(5 seconds)

    enterBarrier("deployed")

    val ponger = system.actorSelection(node(node2) / "user" / "ponger")
    val response = Await.result(ponger ? "ping", 5 seconds)

    println(response)

    enterBarrier("finished")
  }



  runOn(node2) {

    println("started node2...")


    system.actorOf(Props[Ponger], "ponger")

    enterBarrier("deployed")

    enterBarrier("finished")
  }

}

object ConsistencyActorDemo {
  class Ponger extends Actor {
    def receive : Receive = {
      case "ping" => sender() ! "pong"
    }
  }
}