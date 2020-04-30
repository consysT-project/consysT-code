package de.tuda.stg.consys.core.akka

import de.tuda.stg.consys.core.akka.AkkaReplicaSystemFactory.{AkkaReplicaSystemBinding, AkkaReplicaSystemImpl}

import scala.concurrent.{ExecutionContext, Future}
import scala.util.DynamicVariable

object AkkaReplicaSystems {
	private val currentSystem : DynamicVariable[AkkaReplicaSystemBinding] = new DynamicVariable[AkkaReplicaSystemBinding](null)

	def system : AkkaReplicaSystemBinding = currentSystem.value

	def setSystem(newSys : AkkaReplicaSystemBinding) : Unit =
		currentSystem.value = newSys

	def withValue[S](newSys : AkkaReplicaSystemBinding)(thunk : => S) : S =
		currentSystem.withValue(newSys)(thunk)

	def spawn[T](configPath : String)(f : => T)(implicit executor : ExecutionContext) : Unit = {
		Future {
			val replicaSystem = AkkaReplicaSystemFactory.create(configPath)
			currentSystem.withValue(replicaSystem) {
				try {
					f
				} catch {
					case e : Exception => e.printStackTrace()
				} finally {
					replicaSystem.close()
				}
			}
		}
	}

}
