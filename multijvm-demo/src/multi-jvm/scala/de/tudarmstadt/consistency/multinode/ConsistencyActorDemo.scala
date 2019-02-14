package de.tudarmstadt.consistency.multinode

import akka.remote.testkit.MultiNodeSpec
import akka.testkit.ImplicitSender
import de.tudarmstadt.consistency.multinode.schema.A
import de.tudarmstadt.consistency.replobj.actors.{ActorStore, ConsistencyLevels}


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
	  val store = new ActorStore
	  enterBarrier("init")

	  val a = store.distribute[A, ConsistencyLevels.Inconsistent]("a", new A)
	  enterBarrier("deployed")

	  enterBarrier("replicated")

	  a("f") = 4
	  a("f") = 32
	  a <= "inc"

	  Thread.sleep(2000)

	  enterBarrier("fieldset")

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

	  val replica = store.replicate[A, ConsistencyLevels.Inconsistent](node(node1) / "user" / "a")
	  Thread.sleep(2000)

	  replica.remote.f
	  replica.remote.inc()

	  enterBarrier("replicated")

	  enterBarrier("fieldset")

	  val f : Int = replica("f")
	  println("node2: " + f)

    enterBarrier("finished")
  }

}