package de.tudarmstadt.consistency.store.shim

import com.datastax.driver.core.{ResultSet, Row, TupleValue}
import de.tudarmstadt.consistency.store._
import de.tudarmstadt.consistency.store.cassandra.DataRow
import de.tudarmstadt.consistency.store.shim.Event.{EventRef, Tx, Update}
import de.tudarmstadt.consistency.store.shim.EventOrdering._
import de.tudarmstadt.consistency.store.{RowConverter, StoreInterface}

import scala.collection.JavaConverters
import scala.reflect.runtime.universe._

/**
	* Created on 31.08.18.
	*
	* @author Mirko Köhler
	*/
class SysnameVersionedStoreImpl[Id : TypeTag, Key : TypeTag, Data : TypeTag, TxStatus, Isolation, Consistency, Read] (
	override val baseStore : StoreInterface[Key, Data, ResultSet, CassandraTxParams[Id, Isolation], CassandraWriteParams[Id, Key, Consistency], CassandraReadParams[Consistency], Seq[DataRow[Id, Key, Data, TxStatus, Isolation, Consistency]]]
)(
	override val idOps : IdOps[Id],
	override val keyOps : KeyOps[Key],
	override val txStatusOps : TxStatusOps[TxStatus],
	override val isolationLevelOps : IsolationLevelOps[Isolation],
	override val consistencyLevelOps : ConsistencyLevelOps[Consistency],
	val readNothing : Read,
	val readConvert : Update[Id, Key, Data] => Read

)(
  override implicit val idOrdering: Ordering[Id]
) extends SysnameVersionedStore[Id, Key, Data, TxStatus, Isolation, Consistency, Read] {

	override def convertNone : Read = readNothing
	override def convertResult(upd : Update[Id, Key, Data]) : Read = readConvert(upd)


	override val converter : RowConverter[Event[Id, Key, Data]] = (row : Row) => {
		val key = row.get("key", runtimeClassOf[Key])
		val id = row.get("id", runtimeClassOf[Id])
		val cassandraDeps : Set[TupleValue] = JavaConverters.asScalaSet(row.getSet("deps", classOf[TupleValue])).toSet

		val deps : Set[EventRef[Id, Key]] = cassandraDeps.map(tv => {
			val id = tv.get(0, runtimeClassOf[Id])
			val key = tv.get(1, runtimeClassOf[Key])
			EventRef(id, key)
		})

		if (key == keyOps.transactionKey) {
			//row is a transaction
			Tx[Id, Key, Data](id, deps)
		} else {
			val data = row.get("data", runtimeClassOf[Data])
			val txid = row.get("txid", runtimeClassOf[Id])

			Update(id, key, data, Option(txid), deps)
		}
	}
}
