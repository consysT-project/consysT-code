package de.tuda.stg.consys.core.store.cassandra.levels

import com.datastax.oss.driver.api.core.{ConsistencyLevel => CassandraLevel}
import de.tuda.stg.consys.annotations.MethodWriteList
import de.tuda.stg.consys.core.store.cassandra.objects.{CassandraObject, StrongCassandraObject}
import de.tuda.stg.consys.core.store.cassandra.{CassandraRef, CassandraStore}
import de.tuda.stg.consys.core.store.utils.Reflect
import de.tuda.stg.consys.core.store.{ConsistencyLevel, ConsistencyProtocol}
import java.lang.reflect.Field
import org.checkerframework.dataflow.qual.SideEffectFree
import org.graalvm.compiler.hotspot.nodes.`type`.MethodPointerStamp.method
import scala.reflect.ClassTag

/** Consistency level for strong, sequential consistency. */
case object Strong extends ConsistencyLevel[CassandraStore] {
	override def toProtocol(store : CassandraStore) : ConsistencyProtocol[CassandraStore, Strong.type] =
		new StrongProtocol(store)

	/**
	 * Protocol that implements sequential consistency on top of Cassandra. The protocol uses the following
	 * mechanisms to ensure sequential consistency.
	 *
	 * <ol>
	 * 	<li>Once an object is accessed for the first time in a transaction, i.e., <i>before</i> being read from Cassandra,
	 * a global distributed lock is acquired. </li>
	 * 	<li>When the transaction commits
	 * 		<ol>
	 * 		 <li>All objects that have been accessed are written back to Cassandra.
	 * 		 The protocol uses a batch commit with common timestamp for all objects of a transaction to
	 * 		 ensure atomicity of the transaction. </li>
	 * 		 <li>The lock is released (Two-Phase-Locking).</li>
	 * 		</ol>
	 * </ol>
	 */
	private class StrongProtocol(val store : CassandraStore) extends ConsistencyProtocol[CassandraStore, Strong.type] {
		override def toLevel : Strong.type = Strong

		override def replicate[T <: CassandraStore#ObjType : ClassTag](
			txContext : CassandraStore#TxContext,
			addr : CassandraStore#Addr,
			obj : T
		) : CassandraStore#RefType[T] = {
			txContext.acquireLock(addr)
			val cassObj = new StrongCassandraObject[T](addr, obj, -1)
			txContext.Cache.writeNewEntry(addr, cassObj)
			new CassandraRef[T](addr, Strong)
		}

		override def lookup[T <: CassandraStore#ObjType : ClassTag](
			txContext : CassandraStore#TxContext,
			addr : CassandraStore#Addr
		) : CassandraStore#RefType[T] = {
			CassandraRef(addr, Strong)
		}

		override def invoke[T <: CassandraStore#ObjType : ClassTag, R](
			txContext : CassandraStore#TxContext,
			receiver : CassandraStore#RefType[T],
			methodId : String,
			args : Seq[Seq[Any]]
		) : R = {
			val addr = receiver.addr
			txContext.acquireLock(addr)
			val cached = txContext.Cache.getOrFetch[T](addr, strongRead[T](addr))
				.asInstanceOf[StrongCassandraObject[T]]
			val result = cached.invoke[R](methodId, args)

			//If method call is not side effect free, then set the changed flag
			val (objectChanged, changedFields) = Utils.getMethodSideEffects[T](methodId, args)
			if (objectChanged) txContext.Cache.setObjectChanged(addr)
			if (changedFields.nonEmpty) txContext.Cache.setFieldsChanged(addr, changedFields)

			result
		}




		override def getField[T <: CassandraStore#ObjType : ClassTag, R](
			txContext : CassandraStore#TxContext,
			receiver : CassandraStore#RefType[T],
			fieldName : String
		) : R = {
			val addr = receiver.addr
			txContext.acquireLock(addr)
			val cached = txContext.Cache.getOrFetch[T](addr, strongRead[T](addr))
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
			val cached = txContext.Cache.getOrFetch[T](addr, strongRead[T](addr))
			cached.setField[R](fieldName, value)
			txContext.Cache.setFieldsChanged(addr, Iterable.single(Reflect.getField(implicitly[ClassTag[T]].runtimeClass, fieldName)))
		}

		override def commit(
			txContext : CassandraStore#TxContext,
			ref : CassandraStore#RefType[_ <: CassandraStore#ObjType]
		) : Unit = txContext.Cache.getData(ref.addr) match {
			case None =>
				throw new IllegalStateException(s"cannot commit $ref. Object not available.")

			case Some(cassObj : CassandraObject[_, Strong.type]) if cassObj.consistencyLevel == Strong =>
				// Add a new statement to the batch of write statements
				if (!txContext.Cache.hasChanges(ref.addr)) return

				val builder = txContext.getCommitStatementBuilder
				store.CassandraBinding.writeObjectEntry(builder, cassObj.addr, cassObj.state, CassandraLevel.ALL)
			case cached =>
				throw new IllegalStateException(s"cannot commit $ref. Object has wrong level, was $cached.")
		}

		override def postCommit(txContext : CassandraStore#TxContext, ref : CassandraStore#RefType[_ <: CassandraStore#ObjType]) : Unit = {
			txContext.releaseLock(ref.addr)
		}

		private def strongRead[T <: CassandraStore#ObjType : ClassTag](addr : CassandraStore#Addr) : StrongCassandraObject[T] = {
			val entry = store.CassandraBinding.readObjectEntry[T](addr, CassandraLevel.ALL)
			val cassObj = new StrongCassandraObject[T](addr, entry.state.asInstanceOf[T], entry.timestamp)
			cassObj
		}

	}
}