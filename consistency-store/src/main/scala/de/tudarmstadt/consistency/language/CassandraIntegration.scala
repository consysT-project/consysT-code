package de.tudarmstadt.consistency.language

import java.nio.ByteBuffer

import de.tudarmstadt.consistency.language.CassandraIntegration._
import de.tudarmstadt.consistency.store.Stores
import de.tudarmstadt.consistency.store.cassandra.ConnectionParams

import scala.reflect.runtime.universe._

/**
	* Created on 18.12.18.
	*
	* @author Mirko Köhler
	*/
class CassandraIntegration(val connectionParams : ConnectionParams) {

	trait CassandraLanguageBinding extends Language {
		override type Addr = Stores.Default.Key
		override type Consistency = ConsistencyLevel
	}

	def session[A](f : CassandraLanguageBinding => A) : A = {
		val store = Stores.Default.newStore(connectionParams, /*TODO: Do not initialize store*/ initialize = true)
		import store._

		try {
			startSession { session =>
				import session._

				object CassandraLanguage extends CassandraLanguageBinding {
					private val ttStrong : TypeTag[Strong] = typeTag[Strong]
					private val ttWeak : TypeTag[Weak] = typeTag[Weak]

					private def matchConsistencyLevel[C <: ConsistencyLevel : TypeTag, T](caseStrong : => T, caseWeak : => T) : T = {
						val tt = implicitly[TypeTag[C]]

						if (tt == ttStrong) {
							caseStrong
						} else if (tt == ttWeak) {
							caseWeak
						} else {
							sys.error(s"unknown consistency type $tt")
						}
					}

					private var currentTransaction : TxCtx = _

					override def enref[T, C <: ConsistencyLevel : TypeTag](value : T) : Ref[T, C] = ???


					override def deref[T, C <: ConsistencyLevel](ref : Ref[T, C]) : Option[T] = {
						if (currentTransaction == null) {
							startTransaction(Stores.Default.IsolationLevels.NONE) { tx => tx.read(ref.addr, convertConsistency(ref.consistencyLevel)) }
								/*TODO: transform byte buffer to T*/ .asInstanceOf[Option[T]]
						} else {
							currentTransaction.read(ref.addr, convertConsistency(ref.consistencyLevel))
								/*TODO: transform byte buffer to T*/ .asInstanceOf[Option[T]]
						}
					}

					override def update[T, C <: ConsistencyLevel](ref : Ref[T, C], value : T) : Unit = {
						if (currentTransaction == null) {
							startTransaction(Stores.Default.IsolationLevels.NONE) { tx =>
								tx.write(ref.addr, value /*TODO: transform T to byte buffer*/ .asInstanceOf[ByteBuffer], convertConsistency(ref.consistencyLevel))
								Some()
							}
						} else {
							currentTransaction.write(ref.addr, value /*TODO: transform T to byte buffer*/ .asInstanceOf[ByteBuffer], convertConsistency(ref.consistencyLevel))
						}

					}

					override def isolate[T](c : => T) : Option[T] = {
						startTransaction(Stores.Default.IsolationLevels.SI) { tx =>
							currentTransaction = tx
							val r = c
							currentTransaction = null
							Some(r)
						}
					}

					override def cast[T, C <: ConsistencyLevel : TypeTag](value : T) : T = ???

					implicit def convertConsistency[C <: ConsistencyLevel : TypeTag] : Stores.Default.Consistency =
						matchConsistencyLevel(Stores.Default.ConsistencyLevels.CAUSAL, Stores.Default.ConsistencyLevels.WEAK)
				}

				f(CassandraLanguage)
			}
		} finally {
			store.close()
		}
	}
}

object CassandraIntegration {
	sealed trait ConsistencyLevel
	sealed trait Strong extends ConsistencyLevel
	sealed trait Weak extends ConsistencyLevel
}
