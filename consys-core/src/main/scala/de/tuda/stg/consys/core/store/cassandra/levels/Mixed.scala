package de.tuda.stg.consys.core.store.cassandra.levels

import com.datastax.oss.driver.api.core.{ConsistencyLevel => CassandraLevel}
import de.tuda.stg.consys.annotations.methods.{StrongOp, WeakOp}
import de.tuda.stg.consys.core.store.cassandra.objects.MixedCassandraObject
import de.tuda.stg.consys.core.store.cassandra.objects.MixedCassandraObject.{FetchedLevel, FetchedStrong, FetchedWeak}
import de.tuda.stg.consys.core.store.cassandra.{CassandraRef, CassandraStore}
import de.tuda.stg.consys.core.store.utils.Reflect
import de.tuda.stg.consys.core.store.{ConsistencyLevel, ConsistencyProtocol}
import scala.reflect.ClassTag

/**
 * Created on 11.12.19.
 *
 * @author Mirko Köhler
 */
case object Mixed extends ConsistencyLevel[CassandraStore] {
	override def toProtocol(store : CassandraStore) : ConsistencyProtocol[CassandraStore, Mixed.type] =
		new MixedProtocol(store)

	private class MixedProtocol(val store : CassandraStore) extends ConsistencyProtocol[CassandraStore, Mixed.type] {
		override def toLevel : Mixed.type = Mixed

		override def replicate[T <: CassandraStore#ObjType : ClassTag](
			txContext : CassandraStore#TxContext,
			addr : CassandraStore#Addr,
			obj : T
		) : CassandraStore#RefType[T] = {
			val cassObj = new MixedCassandraObject[T](addr, obj, Map.empty,
				Reflect.getFields(implicitly[ClassTag[T]].runtimeClass).map(f => (f, -1L)).toMap, FetchedStrong
			)
			txContext.Cache.writeNewEntry(addr, cassObj)
			new CassandraRef[T](addr, Mixed)
		}

		override def lookup[T <: CassandraStore#ObjType : ClassTag](
			txContext : CassandraStore#TxContext,
			addr : CassandraStore#Addr
		) : CassandraStore#RefType[T] = {
			new CassandraRef[T](addr, Mixed)
		}

		override def invoke[T <: CassandraStore#ObjType : ClassTag, R](
			txContext : CassandraStore#TxContext,
			receiver : CassandraStore#RefType[T],
			methodId : String,
			args : Seq[Seq[Any]]
		) : R = {
			val flattenedArgs = args.flatten
			val clazz = implicitly[ClassTag[T]]
			val method = Reflect.getMethod[T](clazz.runtimeClass.asInstanceOf[Class[T]], methodId, flattenedArgs : _*)

			/* Execute a strong method */
			if (method.getAnnotation(classOf[StrongOp]) != null) {

				val fields = Reflect.getFields(clazz.runtimeClass)/* TODO: Get fields from method */

				// Lock the object
				txContext.acquireLock(receiver.addr)
				//Lookup the object in the cache
				val addr = receiver.addr

				var cachedObj = txContext.Cache.getOrFetch(addr, readStrong[T](addr))

				if (cachedObj.asInstanceOf[MixedCassandraObject[T]].readLevel == FetchedWeak) {
					val obj = readStrong[T](addr)
					//TODO: Only update strong fields, and leave weak fields untouched
					txContext.Cache.updateEntry(addr, obj, false, Iterable.empty)
					cachedObj = obj
				}

				//If method call is not side effect free, then set the changed flag
				val (objectChanged, changedFields) = Utils.getMethodSideEffects[T](methodId, args)
				if (objectChanged) txContext.Cache.setObjectChanged(addr)
				if (changedFields.nonEmpty) txContext.Cache.setFieldsChanged(addr, changedFields)

				val result = cachedObj.invoke[R](methodId, args)

				result

			} else /* if (method.getAnnotation(classOf[WeakOp]) != null) */ {
				if (method.getAnnotation(classOf[WeakOp]) == null) {
					//println(s"Warning: Method [${method.toString}] executed with Weak consistency because it was not annotated.")
				}
				//If the annotation is weak, or if there was no annotation at all...
				//Lookup the object in the cache
				val addr = receiver.addr
				val fields = Reflect.getFields(clazz.runtimeClass)/* TODO: Get fields from method */

				val cachedObj = txContext.Cache.getOrFetch(addr, readWeak[T](addr))

				//If method call is not side effect free, then set the changed flag
				val (objectChanged, changedFields) = Utils.getMethodSideEffects[T](methodId, args)
				if (objectChanged) txContext.Cache.setObjectChanged(addr)
				if (changedFields.nonEmpty) txContext.Cache.setFieldsChanged(addr, changedFields)

				val result = cachedObj.invoke[R](methodId, args)

				result
			}
		}

		override def getField[T <: CassandraStore#ObjType : ClassTag, R](
			txContext : CassandraStore#TxContext,
			receiver : CassandraStore#RefType[T],
			fieldName : String
		) : R = {
			throw new UnsupportedOperationException("field reads are not supported by Mixed consistency")
		}

		override def setField[T <: CassandraStore#ObjType : ClassTag, R](
			txContext : CassandraStore#TxContext,
			receiver : CassandraStore#RefType[T],
			fieldName : String, value : R
		) : Unit = {
			throw new UnsupportedOperationException("field writes are not supported by Mixed consistency")
		}

		override def commit(
			txContext : CassandraStore#TxContext,
			ref : CassandraStore#RefType[_ <: CassandraStore#ObjType]
		) : Unit = {

			//TODO: Set consistency level per field

			txContext.Cache.getDataAndFields(ref.addr) match {
				case None =>
					throw new IllegalStateException(s"cannot commit $ref. Object not available.")
				case Some((cached : MixedCassandraObject[_], fields)) /* if cached.ml == MixedStrong */ =>
					val builder = txContext.getCommitStatementBuilder
					store.CassandraBinding.writeFieldEntry(builder, cached.addr, fields, cached.state, CassandraLevel.ALL)
				case Some((cached : MixedCassandraObject[_], fields)) /* if cached.ml == MixedWeak */ =>
					val builder = txContext.getCommitStatementBuilder
					store.CassandraBinding.writeFieldEntry(builder, cached.addr, fields, cached.state, CassandraLevel.ONE)
				case cached =>
					throw new IllegalStateException(s"cannot commit $ref. Object has wrong level, was $cached.")
			}
		}

		override def postCommit(txContext : CassandraStore#TxContext, ref : CassandraStore#RefType[_ <: CassandraStore#ObjType]) : Unit = {
			txContext.releaseLock(ref.addr)
		}

		//TODO: Make strong read all parts of the object, but weak only the weak parts
		private def readStrong[T <: CassandraStore#ObjType : ClassTag](addr : CassandraStore#Addr) : MixedCassandraObject[T] = {

			val fields = Reflect.getFields(implicitly[ClassTag[T]].runtimeClass)


			val storedObj = store.CassandraBinding.readFieldEntry[T](addr, CassandraLevel.ALL)
			storedObjToMixedObj[T](storedObj, FetchedStrong)
		}

		private def readWeak[T <: CassandraStore#ObjType : ClassTag](addr : CassandraStore#Addr) : MixedCassandraObject[T] = {

			val fields = Reflect.getFields(implicitly[ClassTag[T]].runtimeClass)

			val storedObj = store.CassandraBinding.readFieldEntry[T](addr, CassandraLevel.ONE)
			storedObjToMixedObj[T](storedObj, FetchedWeak)
		}



		private def storedObjToMixedObj[T <: CassandraStore#ObjType : ClassTag](storedObj : store.CassandraBinding.StoredFieldEntry, fetchedLevel : FetchedLevel) : MixedCassandraObject[T] = {
			val clazz = implicitly[ClassTag[T]].runtimeClass

			val constr = Reflect.getConstructor(clazz)
			val instance : T = constr.newInstance().asInstanceOf[T]

			storedObj.fields.foreach(entry => {
				clazz.getField(entry._1.getName).set(instance, entry._2)
			})

			val cassObj = new MixedCassandraObject[T](storedObj.addr, instance, Map.empty, storedObj.timestamps, fetchedLevel)
			cassObj
		}


	}
}