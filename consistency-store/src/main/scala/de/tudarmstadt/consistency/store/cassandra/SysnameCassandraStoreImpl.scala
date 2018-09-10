package de.tudarmstadt.consistency.store.cassandra

import java.util.UUID

import com.datastax.driver.core.DataType
import de.tudarmstadt.consistency.store._

import scala.reflect.runtime.universe._

import SysnameCassandraStoreImpl.cassandraTypeOf

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
	override val idType : DataType = cassandraTypeOf[Id],
	override val keyType : DataType = cassandraTypeOf[Key],
	override val dataType : DataType = cassandraTypeOf[Data],
	override val txStatusType : DataType = cassandraTypeOf[TxStatus],
	override val isolationType : DataType = cassandraTypeOf[Isolation],
	override val consistencyType : DataType = cassandraTypeOf[Consistency]
) extends SysnameCassandraStore[Id, Key, Data, TxStatus, Isolation, Consistency]


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

object SysnameCassandraStoreImpl {
	private def cassandraTypeOf[T : TypeTag] : DataType = implicitly[TypeTag[T]] match {

		//TODO: Is it possible to use CodecRegistry and/or DataType for that task?
		case t if t == typeTag[Boolean] => DataType.cboolean()

		case t if t == typeTag[Int] || t == typeTag[Integer] => DataType.cint()

		case t if t == typeTag[Float] => DataType.cfloat()
		case t if t == typeTag[Double] => DataType.cdouble()
		case t if t == typeTag[BigDecimal] => DataType.decimal()

		case t if t == typeTag[String] => DataType.text()

		case t if t == typeTag[UUID] => DataType.uuid() //TODO Differentiate between UUID and TimeUUID

		case t => throw new IllegalArgumentException(s"can not infer a cassandra type from type tag $t")
	}
}





