package de.tuda.stg.consys.core.store.akka

import akka.actor.ActorSystem
import de.tuda.stg.consys.core.store.DistributedStore

import scala.concurrent.duration.FiniteDuration
import scala.language.higherKinds
import scala.reflect.ClassTag

/**
 * Created on 25.02.20.
 *
 * @author Mirko Köhler
 */
trait AkkaStore extends DistributedStore {
	override type Id = AkkaStoreId

	override type Addr = String
	override type ObjType = java.io.Serializable

	override type TxContext = AkkaTransactionContext

	override type RawType[T <: ObjType] = AkkaObject[T]
	override type RefType[T <: ObjType] = AkkaHandler[T]


	protected[akka]	def actorSystem : ActorSystem

	override def id : Id = AkkaStoreId(s"node@${actorSystem.name}")

	override def transaction[T](code : TxContext => Option[T]) : Option[T] = {
		AkkaStores.currentStore.withValue(this) {
			val tx = AkkaTransactionContext(this)
			AkkaStores.currentTransaction.withValue(tx) {
				try {
					code(tx) match {
						case None => None
						case res@Some(_) =>
							res
					}
				} finally {
					tx.commit()
				}
			}
		}

	}

	override protected[store] def enref[T <: ObjType : ClassTag](obj : RawType[T]) : RefType[T] = ???
}
