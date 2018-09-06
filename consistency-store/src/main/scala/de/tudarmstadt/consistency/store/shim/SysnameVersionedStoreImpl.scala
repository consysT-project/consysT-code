package de.tudarmstadt.consistency.store.shim

import com.datastax.driver.core.{ResultSet, Row, TupleValue}
import de.tudarmstadt.consistency.store.cassandra.DataRow
import de.tudarmstadt.consistency.store.shim.Event.Update
import de.tudarmstadt.consistency.store.{RowConverter, Store, _}

import scala.collection.JavaConverters
import scala.reflect.runtime.universe._

/**
	* Created on 31.08.18.
	*
	* @author Mirko Köhler
	*/
class SysnameVersionedStoreImpl[Id : TypeTag, Key : TypeTag, Data : TypeTag, TxStatus, Isolation, Consistency, Read] (
	override val baseStore : Store[Key, Data, ResultSet, CassandraTxParams[Id, Isolation], CassandraWriteParams[Id, Key, Consistency], CassandraReadParams[Consistency], Seq[DataRow[Id, Key, Data, TxStatus, Isolation, Consistency]]]
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

}
