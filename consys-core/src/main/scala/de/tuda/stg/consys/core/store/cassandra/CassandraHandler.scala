package de.tuda.stg.consys.core.store.cassandra

import de.tuda.stg.consys.core.store.Handler
import scala.reflect.ClassTag

class CassandraHandler[T <: CassandraStore#ObjType : ClassTag](
	val txContext : CassandraStore#TxContext,
	val ref : CassandraRef[T]
)	extends Handler[CassandraStore, T] {
	def store : CassandraStore = txContext.store
	def addr : CassandraStore#Addr = ref.addr
	def level : CassandraStore#Level = ref.level

	override def invoke[R](methodId : String, args : Seq[Seq[Any]]) : R = {
		level.toProtocol(store).invoke[T, R](txContext, ref, methodId, args)
	}

	override def getField[R](fieldName : String) : R = {
		level.toProtocol(store).getField[T, R](txContext, ref, fieldName)
	}

	override def setField[R](fieldName : String, value : R) : Unit = {
		level.toProtocol(store).setField[T, R](txContext, ref, fieldName, value)
	}
}
