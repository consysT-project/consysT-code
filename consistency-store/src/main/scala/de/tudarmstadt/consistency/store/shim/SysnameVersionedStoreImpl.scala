package de.tudarmstadt.consistency.store.shim

import de.tudarmstadt.consistency.store._
import de.tudarmstadt.consistency.store.cassandra.SysnameCassandraStore
import de.tudarmstadt.consistency.store.shim.Event.Update

import scala.reflect.runtime.universe._

/**
	* Created on 31.08.18.
	*
	* @author Mirko Köhler
	*/
class SysnameVersionedStoreImpl[Id : TypeTag, Key : TypeTag, Data : TypeTag, TxStatus, Isolation, Consistency, Read] (
	override val baseStore :  SysnameCassandraStore[Id, Key, Data, TxStatus, Isolation, Consistency]
)(
	val readNothing : Read,
	val readConvert : Update[Id, Key, Data] => Read
)(
	override val Ids : Ids[Id],
	override val TxStatuses : TxStatuses[TxStatus],
	override val IsolationLevels : IsolationLevels[Isolation],
	override val ConsistencyLevels : ConsistencyLevels[Consistency]
)(
  override implicit val idOrdering: Ordering[Id]
) extends SysnameVersionedStore[Id, Key, Data, TxStatus, Isolation, Consistency, Read] {

	override def convertNone : Read = readNothing
	override def convertResult(upd : Update[Id, Key, Data]) : Read = readConvert(upd)

}
