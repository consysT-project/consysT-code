package de.tuda.stg.consys.core.store.cassandra.levels

import com.datastax.oss.driver.api.core.{ConsistencyLevel => CassandraLevel}
import de.tuda.stg.consys.core.store.cassandra.{CassandraObject, CassandraRef, CassandraStore}
import de.tuda.stg.consys.core.store.{ConsistencyLevel, ConsistencyProtocol}
import scala.reflect.ClassTag


/** Consistency level for weak, eventual consistency with last-writer-wins conflict resolution. */
case object Weak extends ConsistencyLevel[CassandraStore] {
	override def toProtocol(store : CassandraStore) : ConsistencyProtocol[CassandraStore, Weak.type] =
		new WeakProtocol(store)

	private class WeakProtocol(val store : CassandraStore) extends ConsistencyProtocol[CassandraStore, Weak.type] {
		override def toLevel : Weak.type = Weak

		override def replicate[T <: CassandraStore#ObjType : ClassTag](
			txContext : CassandraStore#TxContext,
			addr : CassandraStore#Addr,
			obj : T
		) : CassandraStore#RefType[T] = {
			val cassObj = new WeakCassandraObject[T](addr, obj)
			txContext.Cache.put(addr, cassObj)
			new CassandraRef[T](addr, Weak)
		}

		override def lookup[T <: CassandraStore#ObjType : ClassTag](
			txContext : CassandraStore#TxContext,
			addr : CassandraStore#Addr
		) : CassandraStore#RefType[T] = {
			new CassandraRef[T](addr, Weak)
//			txContext.Cache.get(addr) match {
//				case None =>
//					val cassObj = weakRead[T](addr)
//					txContext.Cache.put(addr, cassObj)
//					cassObj.toRef
//				case Some(cached : WeakCassandraObject[T]) if cached.getClassTag == implicitly[ClassTag[T]] =>
//					new CassandraRef[T](addr, Weak)
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
			val cached = txContext.Cache.getOrElseUpdate(addr, weakRead[T](addr))
			val result = cached.invoke[R](methodId, args)
			result
		}

		override def getField[T <: CassandraStore#ObjType : ClassTag, R](
			txContext : CassandraStore#TxContext,
			receiver : CassandraStore#RefType[T],
			fieldName : String
		) : R = {
			val addr = receiver.addr
			val cached = txContext.Cache.getOrElseUpdate(addr, weakRead[T](addr))
			val result = cached.getField[R](fieldName)
			result
		}

		override def setField[T <: CassandraStore#ObjType : ClassTag, R](
			txContext : CassandraStore#TxContext,
			receiver : CassandraStore#RefType[T],
			fieldName : String, value : R
		) : Unit = {
			val addr = receiver.addr
			val cached = txContext.Cache.getOrElseUpdate(addr, weakRead[T](addr))
			cached.setField[R](fieldName, value)
		}


		override def commit(
			txContext : CassandraStore#TxContext,
			ref : CassandraStore#RefType[_ <: CassandraStore#ObjType]
		) : Unit = txContext.Cache.get(ref.addr) match {
			case None => throw new IllegalStateException(s"cannot commit $ref. Object not available.")
			case Some(cassObj : WeakCassandraObject[_]) =>
				val builder = txContext.getCommitStatementBuilder
				builder.addStatement(store.CassandraBinding.writeObjectStatement(cassObj.addr, cassObj.state, CassandraLevel.ONE))
			case cached =>
				throw new IllegalStateException(s"cannot commit $ref. Object has wrong level, was $cached.")
		}

		override def postCommit(txContext : CassandraStore#TxContext, ref : CassandraStore#RefType[_ <: CassandraStore#ObjType]) : Unit = {
			//Do nothing
		}


		private def weakRead[T <: CassandraStore#ObjType : ClassTag](addr : CassandraStore#Addr) : WeakCassandraObject[T] = {
			val obj : T = store.CassandraBinding.readObject[T](addr, CassandraLevel.ONE)
			val cassObj = new WeakCassandraObject[T](addr, obj)
			cassObj
		}
	}


	private class WeakCassandraObject[T <: CassandraStore#ObjType : ClassTag](addr : CassandraStore#Addr, obj : T)
		extends CassandraObject[T, Weak.type](addr, obj, Weak)
}