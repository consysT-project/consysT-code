package de.tuda.stg.consys.core.legacy.akka

import java.util.concurrent.{Executors, TimeUnit}

import de.tuda.stg.consys.core.legacy.{ConsistencyLabel, Ref}
import org.scalatest.{Outcome, fixture}

import scala.concurrent.duration.Duration
import scala.concurrent.{Await, ExecutionContext, Future}
import scala.reflect.runtime.universe._

/**
	* Created on 09.04.19.
	*
	* @author Mirko Köhler
	*/
trait AkkaReplicaSystemSuite { this: fixture.FunSuite =>

	override type FixtureParam = F

	type System = AkkaReplicaSystem {type Addr = String}

	case class F(replicas : Seq[System]) {
		def apply(index : Int) : System = replicas(index)

		def refs[A <: System#Obj : TypeTag](name : String, consistencyLevel : ConsistencyLabel) : Seq[Ref[String, A]] = {
			val x = replicas.map(replica => replica.lookup[A](name, consistencyLevel))
			x
		}

	}

	def numOfReplicas : Int

	def populate(replica : System, index : Int) : Unit = { }

	override def withFixture(testCode : OneArgTest) : Outcome = {
		var replicaSystems : Seq[System] = null

		try {
			replicaSystems = AkkaReplicaSystemFactory.createForTesting(numOfReplicas)

			for (i <- replicaSystems.indices) {
				populate(replicaSystems(i), i)
			}

			testCode(F(replicaSystems))
		} finally {
			if (replicaSystems != null) replicaSystems.foreach { replica => if (replica != null) replica.close() }
		}
	}


	protected def concurrent(fixture : F)(f : Int => Any) : Unit = {
		val service = Executors.newFixedThreadPool(numOfReplicas)
		implicit val exec : ExecutionContext = ExecutionContext.fromExecutorService(service)

		try {
			val futures = new Array[Future[_]](numOfReplicas)
			for (i <- fixture.replicas.indices) {
				futures(i) = Future {	f(i) }
			}

			for (i <- fixture.replicas.indices) {
				Await.result(futures(i), Duration(180, TimeUnit.SECONDS))
			}
		} finally {
			service.shutdown()
			service.awaitTermination(20, TimeUnit.SECONDS)
		}
	}

}
