package de.tudarmstadt.consistency.multinode

import akka.remote.testkit.MultiNodeSpec
import akka.testkit.ImplicitSender
import de.tudarmstadt.consistency.multinode.schema.{A, B}
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
	  val store = actors.store
	  enterBarrier("init")

	  val a = store.distribute[A, ConsistencyLevels.Weak]("a", new A)
	  val b = store.distribute[B, ConsistencyLevels.Weak]("b", new B(a))
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
	  val store = actors.store
	  enterBarrier("init")

//    system.actorOf(Props[Ponger], "ponger")

    enterBarrier("deployed")

	  val replica = store.replicate[B, ConsistencyLevels.Weak](node(node1) / "user" / "b")
	  Thread.sleep(2000)

	  enterBarrier("replicated")

	  replica("x") = 3
	  Thread.sleep(500)
	  val i : Int = replica <= "incAndGet"
		println(s"i = $i")
	  Thread.sleep(500)

	  enterBarrier("fieldset")

	  val x : Int = replica("x")
	  val f : Int = (replica("a") : Ref[A, ConsistencyLevels.Weak])("f")
	  println(s"x = $x, a.f = $f")

    enterBarrier("finished")
  }

}