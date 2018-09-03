package de.tudarmstadt.consistency.store.cassandra

import de.tudarmstadt.consistency.store._

import scala.reflect.runtime.universe._


/**
	* Created on 21.08.18.
	*
	* @author Mirko Köhler
	*/
class SysnameCassandraStoreImpl[Id : TypeTag, Key : TypeTag, Data : TypeTag, TxStatus : TypeTag, Isolation : TypeTag, Consistency : TypeTag]
(
	protected val connectionParams : ConnectionParams
)(
	override val keyOps : KeyOps[Key],
	override val txStatusOps : TxStatusOps[TxStatus],
	override val isolationLevelOps : IsolationLevelOps[Isolation],
	override val consistencyLevelOps : ConsistencyLevelOps[Consistency],
)
extends SysnameCassandraStore[Id, Key, Data, TxStatus, Isolation, Consistency]


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






