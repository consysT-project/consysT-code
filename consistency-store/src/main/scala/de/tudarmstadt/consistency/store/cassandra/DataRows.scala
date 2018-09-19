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
private [cassandra] object DataRows {

	trait DataRow[Id, Key, Data, TxStatus, Isolation, Consistency] {
		def id : Id
		def key : Key
		def data : Data
		def txid : Option[TxRef[Id]]
		def deps : Set[UpdateRef[Id, Key]]
		def txStatus : TxStatus
		def isolation : Isolation
		def consistency : Consistency

		def store : SysnameCassandraStore[Id, Key, Data, TxStatus, Isolation, Consistency]

		def cassandraTxid : Any =
			txid.map(ref => ref.id).getOrElse(null)

		def toEvent : Event[Id, Key, Data] = {
			if (key == store.keys.transactionKey) {
				return Tx(id, deps)
			} else {
				return Update(id, key, data, txid, deps)
			}
		}
	}

	case class CassandraRow[Id, Key, Data, TxStatus, Isolation, Consistency](
		store : SysnameCassandraStore[Id, Key, Data, TxStatus, Isolation, Consistency]
	)(
		val row : Row
	) extends DataRow[Id, Key, Data, TxStatus, Isolation, Consistency] {
		import store._

		override def id : Id = row.get("id", idType)
		override def key : Key = row.get("key", keyType)
		override def data : Data = row.get("data", dataType)
		override def txid : Option[TxRef[Id]] = Option(TxRef(row.get("txid", idType)))
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

	case class LocalRow[Id, Key, Data, TxStatus, Isolation, Consistency] (
		store : SysnameCassandraStore[Id, Key, Data, TxStatus, Isolation, Consistency]
	)(
		val id: Id, val key: Key, val data: Data, val txid: Option[TxRef[Id]], val deps: Set[UpdateRef[Id, Key]], val txStatus: TxStatus, val isolation: Isolation, val consistency: Consistency
	)	extends DataRow[Id, Key, Data, TxStatus, Isolation, Consistency]
}
