package de.tuda.stg.consys.core.store.akka

import de.tuda.stg.consys.core.store.{Handler, StoreConsistencyLevel}

import scala.reflect.ClassTag

/**
 * Created on 25.02.20.
 *
 * @author Mirko Köhler
 */
class AkkaHandler[T <: java.io.Serializable : ClassTag](
	val addr : String,
	val level : StoreConsistencyLevel {type StoreType = AkkaStore}
) extends Handler[AkkaStore, T] with Serializable {

	override def resolve(tx : => AkkaStore#TxContext) : AkkaStore#RawType[T] = {
		tx.lookupRaw[T](addr, level)
	}

	/* This method is for convenience use in transactions */
	def resolve() : AkkaStore#RawType[T] = AkkaStores.getCurrentTransaction match {
		case None => throw new IllegalStateException(s"can not resolve handler for <$addr>. no active transaction.")
		case Some(tx) => resolve(tx)
	}

}