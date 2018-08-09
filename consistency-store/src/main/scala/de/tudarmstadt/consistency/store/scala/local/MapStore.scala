package de.tudarmstadt.consistency.store.scala.local

import java.lang.annotation.Annotation

import de.tudarmstadt.consistency.checker.qual.{Strong, Weak}
import de.tudarmstadt.consistency.store.scala.impl.ReadWriteStore

import scala.collection.mutable

/**
	* Created on 09.08.18.
	*
	* @author Mirko Köhler
	*/
class MapStore[Key, Val] extends ReadWriteStore[Key, Val] {

	override type Context = MapSessionContext

	override def newSessionContext(): Context = new MapSessionContext


	private val data : mutable.HashMap[Key, Any] = mutable.HashMap.empty

	/**
		* Session contexts when working with maps.
		*/
	class MapSessionContext extends ReadWriteSessionContext {

		override def obtain[T <: Val](key: Key, consistencyLevel : Class[_ <: Annotation]): ReadWriteRef[T] = consistencyLevel match {
			case x if classOf[Weak] == x => new MapRef(key)
			case x if classOf[Strong] == x => new MapRef(key)
			case x => throw new IllegalArgumentException(s"unsupported consistency level. expected Weak or Strong, but got $x")
		}
	}

	/**
		* References to values in the map.
		* @param key the key that is referenced
		* @tparam T the value type that is refernced by this key
		*/
	class MapRef[T <: Val](val key : Key) extends ReadWriteRef[T] {

		override protected def handleRead(): Option[T] =
			data.get(key).asInstanceOf[Option[T]]

		override protected def handleWrite(t: T): Unit =
			data.put(key, t)
	}
}



