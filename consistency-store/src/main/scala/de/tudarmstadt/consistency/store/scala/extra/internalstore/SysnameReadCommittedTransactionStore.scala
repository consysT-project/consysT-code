//package de.tudarmstadt.consistency.store.scala.extra.internalstore
//
//import com.datastax.driver.core.exceptions.WriteTimeoutException
//import com.datastax.driver.core.querybuilder.QueryBuilder
//import com.datastax.driver.core.{ConsistencyLevel, Row, WriteType}
//
//import scala.collection.JavaConverters
//import scala.reflect.runtime.universe._
//
//
///**
//	*
//	*
//	* @author Mirko Köhler
//	*/
//trait SysnameReadCommittedTransactionStore[Id, Key, Data, TxStatus, Consistency, Isolation] extends SysnameCassandraStore[Id, Key, Data, TxStatus, Consistency, Isolation] {
//
//
//	override def commit[Return](session : CassandraSession, transaction : Transaction[Return], isolation : Isolation)(implicit idTT : TypeTag[Id], keyTT : TypeTag[Key], dataTT : TypeTag[Data], txStatusTT : TypeTag[TxStatus], consistencyTT : TypeTag[Consistency], isolationTT : TypeTag[Isolation]) : CommitStatus[Id, Return] = isolation match {
//		case l if l == isolationLevelOps.readCommitted =>
//			val context = new ReadCommittedTransactionContext(session)
//
//			transaction(context) match {
//				case Some(result) =>
//					val commitStatus = commitWithReadCommitted(session, context, result)
//					return commitStatus
//				case None =>
//					return CommitStatus.Abort(context.txid, "user abort")
//			}
//
//		case _ => super.commit(session, transaction, isolation)
//	}
//
//
//	override def internalRead(session : CassandraSession, id : Id, key : Key, isolation : Isolation, row : Row)(implicit idTT : TypeTag[Id], keyTT : TypeTag[Key], dataTT : TypeTag[Data], txStatusTT : TypeTag[TxStatus], consistencyTT : TypeTag[Consistency], isolationTT : TypeTag[Isolation]) : ReadStatus[Id, Key, Data] = isolation match {
//		case  l if l == isolationLevelOps.readCommitted =>
//			readWithReadCommitted(session, id, key, isolation, row)
//
//		case _ => super.internalRead(session, id, key, isolation, row)
//	}
//
//
//
//	private class ReadCommittedTransactionContext(val session : CassandraSession) extends TransactionContext {
//
//		//2. Retrieve a fresh transaction id
//		val txid : Id = idOps.freshId()
//
//		case class Update(id : Id, key : Key, data : Data, dependencies : Set[Id])
//
//		var nextDependencies : Set[Id] = Set.empty
//		var updates : Set[Update] = Set.empty
//
//
//		override def read(key : Key)(implicit idTT : TypeTag[Id], keyTT : TypeTag[Key], dataTT : TypeTag[Data], txStatusTT : TypeTag[TxStatus], consistencyTT : TypeTag[Consistency], isolationTT : TypeTag[Isolation]) : Option[Data] = SysnameReadCommittedTransactionStore.this.read(session, key) match {
//			case ReadStatus.Success(_, id, data) =>
//				nextDependencies = nextDependencies + id
//				Some(data)
//			case _ => None
//		}
//
//
//		override def write(key : Key, data : Data)(implicit idTT : TypeTag[Id], keyTT : TypeTag[Key], dataTT : TypeTag[Data], txStatusTT : TypeTag[TxStatus], consistencyTT : TypeTag[Consistency], isolationTT : TypeTag[Isolation]) : Unit = {
//			val id = idOps.freshId() //TODO: Is it a problem that ids are generated here already?
//			updates = updates + Update(id, key, data, nextDependencies)
//			nextDependencies = Set(id)
//		}
//	}
//
//	private def commitWithReadCommitted[Return](session : CassandraSession, transactionContext : ReadCommittedTransactionContext, result : Return)
//	                                           (implicit idTT : TypeTag[Id], keyTT : TypeTag[Key], dataTT : TypeTag[Data], txStatusTT : TypeTag[TxStatus], consistencyTT : TypeTag[Consistency], isolationTT : TypeTag[Isolation]) : CommitStatus[Id, Return]	= {
//
//		import com.datastax.driver.core.querybuilder.QueryBuilder._
//		import CommitStatus._
//
//
//		val txid = transactionContext.txid
//
//		val updatedIds : Set[Id] = transactionContext.updates.map(upd => upd.id)
//		val depsJava : java.util.Set[Id] = JavaConverters.setAsJavaSet(updatedIds)
//
//		try {
//
//			transactionContext.updates.foreach(upd => {
//
//				val transactionContext.Update(id, key, data, deps) = upd
//
//				//Convert dependencies to Java
//				val writeDepsJava : java.util.Set[Id] = JavaConverters.setAsJavaSet(deps.union(Set(txid)))
//
//				session.execute(
//					update(keyspace.dataTable.name)
//						.`with`(set("data", upd.data))
//						.and(set("deps", writeDepsJava))
//						.and(set("txid", txid))
//						.and(set("txstatus", txStatusOps.committed))
//						.and(set("consistency", consistencyLevelOps.sequential))
//						.and(set("isolation", isolationLevelOps.readCommitted))
//						.where(QueryBuilder.eq("key", key))
//						.and(QueryBuilder.eq("id", id))
//						.setConsistencyLevel(ConsistencyLevel.ONE)
//				)
//			})
//
//			session.execute(
//				update(keyspace.dataTable.name)
//					.`with`(set("data", null))
//					.and(set("deps", depsJava))
//					.and(set("txid", txid))
//					.and(set("txstatus", txStatusOps.pending))
//					.and(set("consistency", consistencyLevelOps.sequential))
//					.and(set("isolation", isolationLevelOps.readCommitted))
//					.where(QueryBuilder.eq("key", "$trans"))
//					.and(QueryBuilder.eq("id", txid))
//					.setConsistencyLevel(ConsistencyLevel.ONE)
//			)
//
//		} catch {
//			//TODO: Do proper error handling here
//			case e : Exception => return Error(txid, e)
//		}
//
//		return Success(txid, updatedIds, result)
//
//	}
//
//
//	private def readWithReadCommitted(session : CassandraSession, id : Id, key : Key, isolation : Isolation, row : Row)(implicit idTT : TypeTag[Id], keyTT : TypeTag[Key], dataTT : TypeTag[Data], txStatusTT : TypeTag[TxStatus], consistencyTT : TypeTag[Consistency], isolationTT : TypeTag[Isolation]): ReadStatus[Id, Key, Data] = {
//		import ReadStatus._
//
//		val readData : Data = row.get("data", runtimeClassOf[Data])
//		return Success(key, id, readData)
//	}
//
//
//
//
//}
