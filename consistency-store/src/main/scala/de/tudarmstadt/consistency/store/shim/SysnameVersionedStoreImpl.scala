package de.tudarmstadt.consistency.store.shim

import de.tudarmstadt.consistency.store.shim.Event.Update
import de.tudarmstadt.consistency.store.{Store, _}

import scala.reflect.runtime.universe._

/**
	* Created on 31.08.18.
	*
	* @author Mirko Köhler
	*/
class SysnameVersionedStoreImpl[Id : TypeTag, Key : TypeTag, Data : TypeTag, TxStatus, Isolation, Consistency, Read] (
	override val baseStore : Store[Key, Event[Id, Key, Data], CassandraTxParams[Id, Isolation], CassandraWriteParams[Consistency], CassandraReadParams[Id, Consistency], Seq[Event[Id, Key, Data]]]
)(
	override val ids : Ids[Id],
	override val keys : Keys[Key],
	override val txStatuses : TxStatuses[TxStatus],
	override val isolationLevels : IsolationLevels[Isolation],
	override val consistencyLevels : ConsistencyLevels[Consistency],
	val readNothing : Read,
	val readConvert : Update[Id, Key, Data] => Read

)(
  override implicit val idOrdering: Ordering[Id]
) extends SysnameVersionedStore[Id, Key, Data, TxStatus, Isolation, Consistency, Read] {

	override def convertNone : Read = readNothing
	override def convertResult(upd : Update[Id, Key, Data]) : Read = readConvert(upd)

}
