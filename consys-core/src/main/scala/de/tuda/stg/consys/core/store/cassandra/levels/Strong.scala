package de.tuda.stg.consys.core.store.cassandra.levels

import com.datastax.oss.driver.api.core.{ConsistencyLevel => CassandraLevel}
import de.tuda.stg.consys.core.store.cassandra.{CassandraObject, CassandraRef, CassandraStore, CassandraTransactionContext}
import de.tuda.stg.consys.core.store.{ConsistencyLevel, ConsistencyProtocol, Store}
import java.io
import scala.reflect.ClassTag

/**
 * Created on 11.12.19.
 *
 * @author Mirko Köhler
 */
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
			txContext.acquireLock(addr)
			txContext.Cache.get(addr) match {
				case None =>
					val obj : T = store.CassandraBinding.readObject[T](addr, CassandraLevel.ALL)
					val cassObj = new StrongCassandraObject[T](addr, obj)
					txContext.Cache.put(addr, cassObj)
					cassObj.toRef
				case Some(cached : StrongCassandraObject[T]) if cached.getClassTag == implicitly[ClassTag[T]] =>
					new CassandraRef[T](addr, Strong)
				case Some(cached) =>
					throw new IllegalStateException(s"lookup with wrong consistency level. level: $Strong, obj: $cached")
			}
		}

		def invoke[T <: CassandraStore#ObjType : ClassTag, R](
			txContext : CassandraStore#TxContext,
			receiver : CassandraStore#RefType[T],
			methodId : String,
			args : Seq[Seq[Any]]
		) : R = {
			val addr = receiver.addr
			txContext.Cache.get(addr) match {
				case None =>
					throw new IllegalStateException(s"cannot invoke method on object that is not available in this tx. obj: $receiver")
				case Some(cached : StrongCassandraObject[T]) if cached.getClassTag == implicitly[ClassTag[T]] =>
					val result = cached.invoke[R](methodId, args)
					result
				case Some(cached) =>
					val level = receiver.level
					throw new IllegalStateException(s"lookup with wrong consistency level. level: $level, obj: $cached")
			}
		}
		def getField[T <: CassandraStore#ObjType : ClassTag, R](
			txContext : CassandraStore#TxContext,
			receiver : CassandraStore#RefType[T],
			fieldName : String
		) : R = {
			val addr = receiver.addr
			txContext.Cache.get(addr) match {
				case None =>
					throw new IllegalStateException(s"cannot invoke method on object that is not available in this tx. obj: $receiver")
				case Some(cached : StrongCassandraObject[T]) if cached.getClassTag == implicitly[ClassTag[T]] =>
					val result = cached.getField[R](fieldName)
					result
				case Some(cached) =>
					val level = receiver.level
					throw new IllegalStateException(s"lookup with wrong consistency level. level: $level, obj: $cached")
			}
		}
		def setField[T <: CassandraStore#ObjType : ClassTag, R](
			txContext : CassandraStore#TxContext,
			receiver : CassandraStore#RefType[T],
			fieldName : String, value : R
		) : Unit = {
			val addr = receiver.addr
			txContext.Cache.get(addr) match {
				case None =>
					throw new IllegalStateException(s"cannot invoke method on object that is not available in this tx. obj: $receiver")
				case Some(cached : StrongCassandraObject[T]) if cached.getClassTag == implicitly[ClassTag[T]] =>
					cached.setField[R](fieldName, value)
				case Some(cached) =>
					val level = receiver.level
					throw new IllegalStateException(s"lookup with wrong consistency level. level: $level, obj: $cached")
			}
		}

		override def commit(
			txContext : CassandraStore#TxContext,
			ref : CassandraStore#RefType[_ <: CassandraStore#ObjType]
		) : Unit = txContext.Cache.get(ref.addr) match {
			case None => throw new IllegalStateException(s"cannot commit $ref. Object not available.")
			case Some(cassObj) =>
				store.CassandraBinding.writeObject(cassObj.addr, cassObj.state, CassandraLevel.ALL, txContext.timestamp)
				txContext.releaseLock(cassObj.addr)
		}

		override def postCommit(txContext : CassandraStore#TxContext, ref : CassandraStore#RefType[_ <: CassandraStore#ObjType]) : Unit = {
			txContext.releaseLock(ref.addr)
		}

	}

	private class StrongCassandraObject[T <: CassandraStore#ObjType : ClassTag](
		override val addr : String,
		override val state : T
	) extends CassandraObject[T] {
		override def consistencyLevel : CassandraStore#Level = Strong
	}

}