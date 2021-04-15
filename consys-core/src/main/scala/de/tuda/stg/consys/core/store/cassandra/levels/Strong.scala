package de.tuda.stg.consys.core.store.cassandra.levels

import com.datastax.oss.driver.api.core.{ConsistencyLevel => CassandraLevel}
import de.tuda.stg.consys.core.store.cassandra.{CassandraObject, CassandraRef, CassandraStore}
import de.tuda.stg.consys.core.store.{ConsistencyLevel, ConsistencyProtocol}
import scala.reflect.ClassTag

/** Consistency level for strong, sequential consistency. */
case object Strong extends ConsistencyLevel[CassandraStore] {
	override def toProtocol(store : CassandraStore) : ConsistencyProtocol[CassandraStore, Strong.type] =
		new StrongProtocol(store)

	private class StrongProtocol(val store : CassandraStore) extends ConsistencyProtocol[CassandraStore, Strong.type] {
		override def toLevel : Strong.type = Strong

		override def replicate[T <: CassandraStore#ObjType : ClassTag](
			txContext : CassandraStore#TxContext,
			addr : CassandraStore#Addr,
			obj : T
		) : CassandraStore#RefType[T] = {
			txContext.acquireLock(addr)
			val cassObj = new StrongCassandraObject[T](addr, obj)
			txContext.Cache.put(addr, cassObj)
			new CassandraRef[T](addr, Strong)
		}

		override def lookup[T <: CassandraStore#ObjType : ClassTag](
			txContext : CassandraStore#TxContext,
			addr : CassandraStore#Addr
		) : CassandraStore#RefType[T] = {
			CassandraRef(addr, Strong)
//			txContext.acquireLock(addr)
//			txContext.Cache.get(addr) match {
//				case None =>
//					val cassObj = strongRead[T](addr)
//					txContext.Cache.put(addr, cassObj)
//					cassObj.toRef
//				case Some(cached : StrongCassandraObject[T]) if cached.getClassTag == implicitly[ClassTag[T]] =>
//					new CassandraRef[T](addr, Strong)
//				case Some(cached) =>
//					throw new IllegalStateException(s"lookup with wrong consistency level. level: $Strong, obj: $cached")
//			}
		}

		override def invoke[T <: CassandraStore#ObjType : ClassTag, R](
			txContext : CassandraStore#TxContext,
			receiver : CassandraStore#RefType[T],
			methodId : String,
			args : Seq[Seq[Any]]
		) : R = {
			val addr = receiver.addr
			txContext.acquireLock(addr)
			val cached = txContext.Cache.getOrElseUpdate(addr, strongRead[T](addr))
			val result = cached.invoke[R](methodId, args)
			result
		}

		override def getField[T <: CassandraStore#ObjType : ClassTag, R](
			txContext : CassandraStore#TxContext,
			receiver : CassandraStore#RefType[T],
			fieldName : String
		) : R = {
			val addr = receiver.addr
			txContext.acquireLock(addr)
			val cached = txContext.Cache.getOrElseUpdate(addr, strongRead[T](addr))
			val result = cached.getField[R](fieldName)
			result
		}

		override def setField[T <: CassandraStore#ObjType : ClassTag, R](
			txContext : CassandraStore#TxContext,
			receiver : CassandraStore#RefType[T],
			fieldName : String, value : R
		) : Unit = {
			val addr = receiver.addr
			txContext.acquireLock(addr)
			val cached = txContext.Cache.getOrElseUpdate(addr, strongRead[T](addr))
			cached.setField[R](fieldName, value)
		}

		override def commit(
			txContext : CassandraStore#TxContext,
			ref : CassandraStore#RefType[_ <: CassandraStore#ObjType]
		) : Unit = txContext.Cache.get(ref.addr) match {
			case None =>
				throw new IllegalStateException(s"cannot commit $ref. Object not available.")
			case Some(cassObj : StrongCassandraObject[_]) =>
				val builder = txContext.getCommitStatementBuilder
				builder.addStatement(store.CassandraBinding.writeObjectStatement(cassObj.addr, cassObj.state, CassandraLevel.ALL))
			case cached =>
				throw new IllegalStateException(s"cannot commit $ref. Object has wrong level, was $cached.")
		}

		override def postCommit(txContext : CassandraStore#TxContext, ref : CassandraStore#RefType[_ <: CassandraStore#ObjType]) : Unit = {
			txContext.releaseLock(ref.addr)
		}

		private def strongRead[T <: CassandraStore#ObjType : ClassTag](addr : CassandraStore#Addr) : StrongCassandraObject[T] = {
			val obj : T = store.CassandraBinding.readObject[T](addr, CassandraLevel.ALL)
			val cassObj = new StrongCassandraObject[T](addr, obj)
			cassObj
		}

	}

	private class StrongCassandraObject[T <: CassandraStore#ObjType : ClassTag](addr : CassandraStore#Addr, obj : T)
		extends CassandraObject[T, Strong.type](addr, obj, Strong)


}