package de.tudarmstadt.consistency.store.shim

import de.tudarmstadt.consistency.store.shim.Event.EventRef

/**
	* Created on 04.09.18.
	*
	* @author Mirko Köhler
	*/
trait Event[Id, Key, Data] {
	/*
		Theoretically, dependencies only need to contain the id.
		However, we also include the key in order to have more
		efficient Cassandra reads (key is the partitioning key in the
		data table).
	 */
	def getDependencies : Set[EventRef[Id, Key]]
	def getData : Option[Data]
	def getId :Id

	val resolvedDependencies : Array[Boolean] = Array(false)
	def isResolved : Boolean = resolvedDependencies(0)
	def setResolved(): Unit =	resolvedDependencies(0) = true
}

object Event {

	case class EventRef[Id, Key](id : Id, key : Key)

	//Note: val dependencies does not contain the txid.
	case class Update[Id, Key, Data](id : Id, key : Key, data : Data, txid : Option[Id], dependencies : Set[EventRef[Id, Key]]) extends Event[Id, Key, Data] {
		override def getDependencies : Set[EventRef[Id, Key]] = dependencies //++ txid
		override def getData : Option[Data] =	Some(data)
		override def getId : Id = id
	}

	case class Tx[Id, Key, Data](id : Id, deps : Set[EventRef[Id, Key]]) extends Event[Id, Key, Data] {
		override def getDependencies : Set[EventRef[Id, Key]] = deps
		override def getData : Option[Data] = None
		override def getId : Id = id
	}
}

