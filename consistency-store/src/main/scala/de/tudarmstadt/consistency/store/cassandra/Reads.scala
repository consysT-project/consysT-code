package de.tudarmstadt.consistency.store.cassandra

import com.datastax.driver.core.{Row, TupleValue}
import de.tudarmstadt.consistency.store.shim.Event
import de.tudarmstadt.consistency.store.shim.Event.{Tx, Update}
import de.tudarmstadt.consistency.store.shim.EventRef.{TxRef, UpdateRef}

import scala.collection.JavaConverters

/**
	* Created on 19.09.18.
	*
	* @author Mirko Köhler
	*/
private[cassandra] object Reads {


	trait Read[Id, Key, Data] {
		def toEvent : Event[Id, Key, Data]
	}


	trait CassandraRead[Id, Key, Data, TxStatus, Isolation, Consistency] {
		def store : SysnameCassandraStore[Id, Key, Data, TxStatus, Isolation, Consistency]
	}


	trait ReadUpdate[Id, Key, Data, TxStatus, Isolation, Consistency] extends Read[Id, Key, Data] {
		def id : Id
		def key : Key
		def data : Data
		def txid : Option[TxRef[Id]]
		def deps : Set[UpdateRef[Id, Key]]
		def txStatus : TxStatus
		def isolation : Isolation
		def consistency : Consistency

		override def toEvent : Update[Id, Key, Data] =
			return Update(id, key, data, txid, deps)
	}

	trait ReadTx[Id, Key, Data, TxStatus, Isolation, Consistency] extends Read[Id, Key, Data] {
		def id : Id
		def deps : Set[UpdateRef[Id, Key]]
		def txStatus : TxStatus
		def isolation : Isolation
		def consistency : Consistency

		override def toEvent : Tx[Id, Key, Data] =
			return Tx(id, deps)
	}


	case class CassandraReadUpdate[Id, Key, Data, TxStatus, Isolation, Consistency](
		override val store : SysnameCassandraStore[Id, Key, Data, TxStatus, Isolation, Consistency]
	)(
		val row : Row
	) extends ReadUpdate[Id, Key, Data, TxStatus, Isolation, Consistency] with CassandraRead[Id, Key, Data, TxStatus, Isolation, Consistency]{
		import store._
		//TODO: For testing purposes only
		Seq("id", "key", "data", "txid", "deps", "txstatus", "isolation", "consistency").foreach(name =>
			assert(row.getColumnDefinitions.contains(name), s"expected update row to contain field $name")
		)

		override def id : Id = row.get("id", idType)
		override def key : Key = row.get("key", keyType)
		override def data : Data = row.get("data", dataType)
		override def txid : Option[TxRef[Id]] =
			Option(row.get("txid", idType)).map(id => TxRef(id))


		override def deps : Set[UpdateRef[Id, Key]] = {
			val rawSet : Set[TupleValue] = JavaConverters.asScalaSet(row.getSet("deps", runtimeClassOf[TupleValue])).toSet
			rawSet.map(tv => {
				val id = tv.get(0, idType)
				val key = tv.get(1, keyType)
				UpdateRef(id, key)
			})
		}
		override def txStatus : TxStatus = row.get("txstatus", txStatusType)
		override def isolation : Isolation = row.get("isolation", isolationType)
		override def consistency : Consistency = row.get("consistency", consistencyType)
	}

	case class CassandraReadTx[Id, Key, Data, TxStatus, Isolation, Consistency](
	  override val store : SysnameCassandraStore[Id, Key, Data, TxStatus, Isolation, Consistency]
	)(
	  val row : Row
	) extends ReadTx[Id, Key, Data, TxStatus, Isolation, Consistency] with CassandraRead[Id, Key, Data, TxStatus, Isolation, Consistency]{
		import store._
		//Check whether all fields are available
		//TODO: These are for testing purposes only
		Seq("id", "deps", "txstatus", "isolation", "consistency").foreach(name =>
			assert(row.getColumnDefinitions.contains(name), s"expected tx row to contain field $name")
		)




		override def id : Id = row.get("id", idType)

		override def deps : Set[UpdateRef[Id, Key]] = {
			val rawSet : Set[TupleValue] = JavaConverters.asScalaSet(row.getSet("deps", runtimeClassOf[TupleValue])).toSet
			rawSet.map(tv => {
				val id = tv.get(0, idType)
				val key = tv.get(1, keyType)
				UpdateRef(id, key)
			})
		}

		override def txStatus : TxStatus = row.get("txstatus", txStatusType)
		override def isolation : Isolation = row.get("isolation", isolationType)
		override def consistency : Consistency = row.get("consistency", consistencyType)
	}
}
