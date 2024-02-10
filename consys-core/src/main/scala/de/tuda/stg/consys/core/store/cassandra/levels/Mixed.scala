package de.tuda.stg.consys.core.store.cassandra.levels

import com.datastax.oss.driver.api.core.{ConsistencyLevel => CassandraLevel}
import de.tuda.stg.consys.annotations.methods.{StrongOp, WeakOp}
import de.tuda.stg.consys.core.store.cassandra.objects.MixedCassandraObject
import de.tuda.stg.consys.core.store.cassandra.objects.MixedCassandraObject.{FetchedLevel, FetchedStrong, FetchedWeak}
import de.tuda.stg.consys.core.store.cassandra.{CassandraConsistencyLevel, CassandraConsistencyProtocol, CassandraRef, CassandraStore}
import de.tuda.stg.consys.core.store.utils.Reflect
import de.tuda.stg.consys.core.store.{ConsistencyLevel, ConsistencyProtocol}

import java.lang.reflect.Field
import scala.reflect.ClassTag

/**
 * Created on 11.12.19.
 *
 * @author Mirko Köhler
 */
case object Mixed extends CassandraConsistencyLevel {
	override def toProtocol(store : CassandraStore) : CassandraConsistencyProtocol[Mixed.type] =
		new MixedProtocol(store)

	private class MixedProtocol(val store : CassandraStore) extends CassandraConsistencyProtocol[Mixed.type] {
		override def toLevel : Mixed.type = Mixed

		override def replicate[T <: CassandraStore#ObjType : ClassTag](
			txContext : CassandraStore#TxContext,
			addr : CassandraStore#Addr,
			obj : T
		) : CassandraStore#RefType[T] = {
			val fields = Reflect.getFields(implicitly[ClassTag[T]].runtimeClass)
			val cassObj = new MixedCassandraObject[T](addr, obj, Reflect.getMixedFieldLevels[T],
				fields.map(f => (f, -1L)).toMap, FetchedStrong
			)
			txContext.Cache.addEntry(addr, cassObj, fields)
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
				val fields = Reflect.getMixedFieldLevels[T]
				val allFields = fields.map(entry => entry._1.getName)

				// Lock the object
				txContext.acquireLock(receiver.addr)
				// Lookup the object in the cache
				val addr = receiver.addr

				// Read all fields, since a strong method may access strong and weak fields
				var cachedObj = txContext.Cache.readEntry(addr, readStrong[T](addr, allFields))

				if (cachedObj.asInstanceOf[MixedCassandraObject[T]].readLevel == FetchedWeak) {
					// We have already read all weak fields, so only update strong fields here
					val strongFields = fields.filter(entry => entry._2 == Strong).map(entry => entry._1.getName)
					val obj = readStrong[T](addr, strongFields, Some(cachedObj.asInstanceOf[MixedCassandraObject[T]]))
					txContext.Cache.updateEntry(addr, obj, changedObject = false, Iterable.empty)
					cachedObj = obj
				}

				// If method call is not side effect free, then set the changed flag
				val (objectChanged, changedFields) = Reflect.getMethodSideEffects[T](methodId, args)
				if (objectChanged) txContext.Cache.setObjectChanged(addr)
				if (changedFields.nonEmpty) txContext.Cache.setFieldsChanged(addr, changedFields)

				val result = cachedObj.invoke[R](methodId, args)

				result

			} else /* if (method.getAnnotation(classOf[WeakOp]) != null) */ { //TODO: Resolve default operation types
				if (method.getAnnotation(classOf[WeakOp]) == null) {
					//println(s"Warning: Method [${method.toString}] executed with Weak consistency because it was not annotated.")
				}
				// If the annotation is weak, or if there was no annotation at all...

				// Read all fields, since a weak method may still read strong fields
				val fields = Reflect.getMixedFieldLevels[T]
				val allFields = fields.map(entry => entry._1.getName)

				// Lookup the object in the cache
				val addr = receiver.addr

				val cachedObj = txContext.Cache.readEntry(addr, readWeak[T](addr, allFields))

				// If method call is not side effect free, then set the changed flag
				val (objectChanged, changedFields) = Reflect.getMethodSideEffects[T](methodId, args)
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

		def commit(
			txContext : CassandraStore#TxContext,
			ref : CassandraStore#RefType[_ <: CassandraStore#ObjType]
		) : Unit = {

			//TODO: Set consistency level per field
			txContext.Cache.readLocalEntry(ref.addr) zip txContext.Cache.getChangedFields(ref.addr) match {
				case None =>
					throw new IllegalStateException(s"cannot commit $ref. Object not available.")
				case Some((cached : MixedCassandraObject[_], changedFields)) /* if cached.ml == MixedStrong */
					// if any strong field was changed then write batch (all changed fields) with strong consistency
					if changedFields.map(f => cached.fieldLevels.getOrElse(f, throw new IllegalStateException())).exists(l => l == Strong) =>
					val builder = txContext.getCommitStatementBuilder
					store.cassandra.writeFieldEntry(builder, cached.addr, changedFields, cached.state, CassandraLevel.ALL)
				case Some((cached : MixedCassandraObject[_], changedFields)) /* if cached.ml == MixedWeak */ =>
					val builder = txContext.getCommitStatementBuilder
					store.cassandra.writeFieldEntry(builder, cached.addr, changedFields, cached.state, CassandraLevel.ONE)
				case cached =>
					throw new IllegalStateException(s"cannot commit $ref. Object has wrong level, was $cached.")
			}
		}

		private def readStrong[T <: CassandraStore#ObjType : ClassTag](addr : CassandraStore#Addr, fields: Iterable[String], cachedObject: Option[MixedCassandraObject[T]] = None) : MixedCassandraObject[T] = {
			val storedObj = store.cassandra.readFieldEntry[T](addr, fields, CassandraLevel.ALL)
			storedObjToMixedObj[T](storedObj, FetchedStrong, cachedObject)
		}

		private def readWeak[T <: CassandraStore#ObjType : ClassTag](addr : CassandraStore#Addr, fields: Iterable[String]) : MixedCassandraObject[T] = {
			val storedObj = store.cassandra.readFieldEntry[T](addr, fields, CassandraLevel.ONE)
			storedObjToMixedObj[T](storedObj, FetchedWeak)
		}

		private def storedObjToMixedObj[T <: CassandraStore#ObjType : ClassTag](storedObj : store.cassandra.StoredFieldEntry, fetchedLevel : FetchedLevel, cachedObject: Option[MixedCassandraObject[T]] = None) : MixedCassandraObject[T] = {
			val clazz = implicitly[ClassTag[T]].runtimeClass

			val instance = cachedObject match {
				case Some(value) => value.state
				case None => Reflect.getConstructor(clazz).newInstance().asInstanceOf[T]
			}

			storedObj.fields.foreach(entry => {
				val field = Reflect.getField(clazz, entry._1.getName)
				field.setAccessible(true)
				field.set(instance, entry._2)
			})

			val cachedTimestamps = cachedObject match {
				case Some(value) => value.timestamps
				case None => Map.empty[Field, Long]
			}

			val cassObj = new MixedCassandraObject[T](storedObj.addr, instance, Reflect.getMixedFieldLevels[T], cachedTimestamps ++ storedObj.timestamps, fetchedLevel)
			cassObj
		}


	}
}