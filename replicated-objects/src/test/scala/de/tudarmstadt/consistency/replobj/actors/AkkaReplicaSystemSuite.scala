package de.tudarmstadt.consistency.replobj.actors

import java.util.concurrent.{Executors, TimeUnit}

import de.tudarmstadt.consistency.replobj.ConsistencyLevel.Strong
import de.tudarmstadt.consistency.replobj.actors.Data.A
import de.tudarmstadt.consistency.replobj.{ConsistencyLevel, Ref, actors}
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

	case class F(replicas : Array[AkkaReplicaSystem[String]]) {
		def apply(index : Int) : AkkaReplicaSystem[String] = replicas(index)

		def refs[T <: AnyRef : TypeTag](name : String, consistencyLevel : ConsistencyLevel) : Array[Ref[String, T]] =
			replicas.map(replica => replica.ref[T]("a", consistencyLevel))

	}

	def numOfReplicas : Int

	def populate(replica : AkkaReplicaSystem[String], index : Int) : Unit = { }

	override def withFixture(testCode : OneArgTest) : Outcome = {
		val replicaSystems : Array[AkkaReplicaSystem[String]] = new Array(numOfReplicas)

		try {
			for (i <- replicaSystems.indices) {
				replicaSystems(i) = actors.createReplicaSystem(2552 + i)
			}

			for (i <- replicaSystems.indices; j <- replicaSystems.indices) {
				if (i != j) replicaSystems(i).addOtherReplica("127.0.0.1", 2552 + j)
			}

			for (i <- replicaSystems.indices) {
				populate(replicaSystems(i), i)
			}

			val result = testCode(F(replicaSystems))
			result
		} finally {
			replicaSystems.foreach { replica => if (replica != null) replica.close() }
		}
	}


	protected def concurrent(fixture : F)(f : Int => Any) : Unit = {
		val service = Executors.newFixedThreadPool(numOfReplicas)
		implicit val exec : ExecutionContext = ExecutionContext.fromExecutorService(service)

		val futures = new Array[Future[_]](numOfReplicas)
		for (i <- fixture.replicas.indices) {
			futures(i) = Future {	f(i) }
		}

		for(i <- fixture.replicas.indices) {
			Await.result(futures(i), Duration(20, TimeUnit.SECONDS))
		}

		service.awaitTermination(3, TimeUnit.SECONDS)
	}

}
