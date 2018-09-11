package de.tudarmstadt.consistency.store.cassandra

import java.util.UUID

import com.datastax.driver.core.{DataType, TypeCodec}
import de.tudarmstadt.consistency.store._

import scala.reflect.runtime.universe._


/**
	* Created on 21.08.18.
	*
	* @author Mirko Köhler
	*/
class SysnameCassandraStoreImpl[Id : TypeTag, Key : TypeTag, Data : TypeTag, TxStatus : TypeTag, Isolation : TypeTag, Consistency : TypeTag]
(
	override protected val connectionParams : ConnectionParams,
	override val keyspaceName : String
)(
	override val keys : Keys[Key],
	override val txStatuses : TxStatuses[TxStatus],
	override val isolationLevels : IsolationLevels[Isolation],
	override val consistencyLevels : ConsistencyLevels[Consistency],
)(
	val idTpe : TypeCodec[Id] = null,
	val keyTpe : TypeCodec[Key] = null,
	val dataTpe : TypeCodec[Data] = null,
	val txStatusTpe : TypeCodec[TxStatus] = null,
	val isolationTpe : TypeCodec[Isolation] = null,
	val consistencyTpe : TypeCodec[Consistency] = null
) extends SysnameCassandraStore[Id, Key, Data, TxStatus, Isolation, Consistency] {

	private def setType[T : TypeTag](t : TypeCodec[T]) : TypeCodec[T] =
		if (t == null) typeCodecOf[T] else t

	override val idType : TypeCodec[Id] = setType[Id](idTpe)
	override val keyType : TypeCodec[Key] = setType[Key](keyTpe)
	override val dataType : TypeCodec[Data] = setType[Data](dataTpe)
	override val txStatusType : TypeCodec[TxStatus] = setType[TxStatus](txStatusTpe)
	override val isolationType : TypeCodec[Isolation] = setType[Isolation](isolationTpe)
	override val consistencyType : TypeCodec[Consistency] = setType[Consistency](consistencyTpe)
}


//	override val maxFunctionDef : String =
//		s"""Integer maxid = max.get(0, Integer.class);
//			 |
//			 |  if (maxid == null || id > maxid) {
//			 |			max.setInt(0, id);
//			 |			max.setString(1, key);
//			 |			max.setString(2, data);
//			 |			max.setSet(3, deps, Integer.class);
//			 |			max.set(4, txid, Integer.class);
//			 |			max.setString(5, consistency);
//			 |			return max;
//			 |		} else {
//			 |			return max;
//			 |		}
//		 """.stripMargin





