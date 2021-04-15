package de.tuda.stg.consys.core.store.cassandra

import de.tuda.stg.consys.core.store.Ref
import scala.reflect.ClassTag

/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
case class CassandraRef[T <: CassandraStore#ObjType : ClassTag](
	addr : CassandraStore#Addr,
	level : CassandraStore#Level
) extends Ref[CassandraStore, T] with Serializable {

	override def resolve(tx : CassandraStore#TxContext) : CassandraStore#HandlerType[T] = {
		new CassandraHandler(tx, this)
	}

	/* This method is for convenience use in transactions or when TxContext is not passed around */
	def resolve() : CassandraStore#HandlerType[T] = CassandraStores.getCurrentTransaction match {
		case None => throw new IllegalStateException(s"can not resolve handler for <$addr>. no active transaction.")
		case Some(tx) => resolve(tx)
	}

}
