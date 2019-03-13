package de.tudarmstadt.consistency.multinode

import akka.actor.{ActorSelection, ActorSystem}
import akka.remote.testkit.MultiNodeSpec
import akka.testkit.ImplicitSender
import de.tudarmstadt.consistency.multinode.schema.{A, B}
import de.tudarmstadt.consistency.replobj.ConsistencyLevels.{Strong, Weak}
import de.tudarmstadt.consistency.replobj.actors.AkkaReplicaSystem
import de.tudarmstadt.consistency.replobj.{ConsistencyLevels, Ref, ReplicaSystem, actors}

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

	  val replica : AkkaReplicaSystem[String] = actors.createReplicaSystem(system)

	  enterBarrier("setup")

	  replica.addOtherReplica(node(node2).address)

	  enterBarrier("init")

	  val a = replica.replicate[A, Weak]("a", new A)
	  val b = replica.replicate[B, Strong]("b", new B(a))

	  Thread.sleep(3000)

	  enterBarrier("deployed")


	  enterBarrier("replicated")


	  enterBarrier("unsynchronized")


	  enterBarrier("synchronize")

	  {
		  val x : Int = b("x")
		  val f : Int = (b("a") : Ref[String, A, ConsistencyLevels.Weak]) ("f")
		  val af : Int = a("f")
		  println(s"b.x = $x, b.a.f = $f, a.f = $af")
		  println(s"b = ${b <= "toString"}")
	  }

	  enterBarrier("synchronized")

	  {
		  val x : Int = b("x")
		  val f : Int = (b("a") : Ref[String, A, ConsistencyLevels.Weak]) ("f")
		  val af : Int = a("f")
		  println(s"b.x = $x, b.a.f = $f, a.f = $af")
		  println(s"b = ${b <= "toString"}")
	  }

    enterBarrier("finished")
  }



  runOn(node2) {
    println("started node2...")
	  val replica : AkkaReplicaSystem[String] =  actors.createReplicaSystem(system)

	  enterBarrier("setup")

	  println(node(node1).root)

	  replica.addOtherReplica(node(node1).address)

	  enterBarrier("init")

    enterBarrier("deployed")


		val refA = replica.ref[A, Weak]("a")
	  val refB = replica.ref[B, Strong]("b")
	  Thread.sleep(2000)

	  enterBarrier("replicated")

	  refB("x") = 3
	  Thread.sleep(500)
	  val i : Int = refB <= "incAndGet"
		println(s"i = $i")

	  enterBarrier("unsynchronized")


	  enterBarrier("synchronize")

	  refA.sync()
	  Thread.sleep(500)

	  enterBarrier("synchronized")

	  val x : Int = refB("x")
	  val f : Int = (refB("a") : Ref[String, A, ConsistencyLevels.Weak])("f")
	  println(s"x = $x, a.f = $f")
	  println(s"b = ${refB <= "toString"}")

    enterBarrier("finished")
  }

}