package de.tudarmstadt.consistency.multinode

import akka.actor.ActorSystem
import akka.remote.testkit.MultiNodeSpec
import akka.testkit.ImplicitSender
import de.tudarmstadt.consistency.multinode.schema.{A, B}
import de.tudarmstadt.consistency.replobj.actors.AkkaReplicaSystem
import de.tudarmstadt.consistency.replobj.{ConsistencyLevels, Ref, actors}

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

	  val replica = new AkkaReplicaSystem[String] {
		  override def actorSystem : ActorSystem = system
		  override def name : String = "replica1"
	  }


	  enterBarrier("setup")


	  enterBarrier("init")

	  val a = replica.replicate[A, ConsistencyLevels.Weak]("a", new A)
	  val b = replica.replicate[B, ConsistencyLevels.Weak]("b", new B(a))

	  enterBarrier("deployed")

	  enterBarrier("replicated")


	  enterBarrier("fieldset")

	  val x : Int = b("x")
	  val f : Int = (b("a") : Ref[A, ConsistencyLevels.Weak])("f")
	  val af : Int = a("f")
	  println(s"b.x = $x, b.a.f = $f, a.f = $af")

    enterBarrier("finished")
  }



  runOn(node2) {
    println("started node2...")
	  val replica = new AkkaReplicaSystem[String] {
		  override def actorSystem : ActorSystem = system
		  override def name : String = "replica2"
	  }

	  enterBarrier("setup")




	  enterBarrier("init")

//    system.actorOf(Props[Ponger], "ponger")

    enterBarrier("deployed")

	  val ref = replica.ref[B, ConsistencyLevels.Weak]("b")
	  Thread.sleep(2000)

	  enterBarrier("replicated")

	  ref("x") = 3
	  Thread.sleep(500)
	  val i : Int = ref <= "incAndGet"
		println(s"i = $i")
	  Thread.sleep(500)

	  enterBarrier("fieldset")

	  val x : Int = ref("x")
	  val f : Int = (ref("a") : Ref[A, ConsistencyLevels.Weak])("f")
	  println(s"x = $x, a.f = $f")

    enterBarrier("finished")
  }

}