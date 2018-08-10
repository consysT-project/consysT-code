package de.tudarmstadt.consistency.store.scala.local

import de.tudarmstadt.consistency.store.scala.impl.ReadWriteRef

import scala.collection.mutable

/**
		* References to values in the map.
 *
		* @param key the key that is referenced
		* @tparam T the value type that is refernced by this key
		*/
	class MapRef[Key, T](val data : mutable.Map[Key, Any], val key : Key) extends ReadWriteRef[Key, T] {

		override protected def handleRead(): Option[T] =
			data.get(key).asInstanceOf[Option[T]]

		override protected def handleWrite(t: T): Unit =
			data.put(key, t)
	}