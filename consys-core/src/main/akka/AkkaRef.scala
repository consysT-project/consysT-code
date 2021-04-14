package de.tuda.stg.consys.core.store.akka

import de.tuda.stg.consys.core.store.{Ref, ConsistencyLevel}

import scala.reflect.ClassTag

/**
 * Created on 25.02.20.
 *
 * @author Mirko Köhler
 */
class AkkaRef[T <: java.io.Serializable : ClassTag](
	val addr : String,
	val level : AkkaStore#Level
) extends Ref[AkkaStore, T] with Serializable {

	override def resolve(tx : => AkkaStore#TxContext) : AkkaStore#HandlerType[T] = {
		tx.lookupRaw[T](addr, level)
	}

	/* This method is for convenience use in transactions */
	def resolve() : AkkaStore#HandlerType[T] = AkkaStores.getCurrentTransaction match {
		case None => throw new IllegalStateException(s"can not resolve handler for <$addr>. no active transaction.")
		case Some(tx) => resolve(tx)
	}

}