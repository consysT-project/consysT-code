package de.tuda.stg.consys.core.legacy.akka

import scala.concurrent.{ExecutionContext, Future}
import scala.util.DynamicVariable

object AkkaReplicaSystems {
	private val currentSystem : DynamicVariable[AkkaReplicaSystem] = new DynamicVariable[AkkaReplicaSystem](null)

	def system : AkkaReplicaSystem = currentSystem.value

	def setSystem(newSys : AkkaReplicaSystem) : Unit =
		currentSystem.value = newSys

	def withValue[S](newSys : AkkaReplicaSystem)(thunk : => S) : S =
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
