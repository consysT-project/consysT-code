package de.tudarmstadt.consistency.store.scala.extra.shim

import com.datastax.driver.core.{ResultSet, Row}
import de.tudarmstadt.consistency.store.scala.extra.{RowConverter, StoreInterface, runtimeClassOf}
import de.tudarmstadt.consistency.store.scala.extra.Util._
import de.tudarmstadt.consistency.store.scala.extra.shim.EventOrdering._

import scala.reflect.runtime.universe._

import scala.collection.JavaConverters

/**
	* Created on 31.08.18.
	*
	* @author Mirko Köhler
	*/
class SysnameVersionedStoreImpl[Id : TypeTag, Key : TypeTag, Data : TypeTag, Isolation, Consistency] (
	override val baseStore : StoreInterface[Key, Data, ResultSet, CassandraTxParams[Id, Isolation], CassandraOpParams[Id, Consistency]]
)(
	override val idOps : IdOps[Id],
	val keyOps : KeyOps[Key],
	override val isolationLevelOps : IsolationLevelOps[Isolation],
	override val consistencyLevelOps : ConsistencyLevelOps[Consistency]
)(
  override implicit val idOrdering: Ordering[Id]
) extends SysnameVersionedStore[Id, Key, Data, Isolation, Consistency] {

	override val converter : RowConverter[Event[Id, Key, Data]] = new RowConverter[EventOrdering.Event[Id, Key, Data]] {


		override def convertRow(row : Row) : Event[Id, Key, Data] = {
			val key = row.get("key", runtimeClassOf[Key])
			val id = row.get("id", runtimeClassOf[Id])
			val deps = JavaConverters.asScalaSet(row.getSet("deps", runtimeClassOf[Id])).toSet

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
}
