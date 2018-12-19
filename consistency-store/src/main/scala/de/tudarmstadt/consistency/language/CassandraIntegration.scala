package de.tudarmstadt.consistency.language

import de.tudarmstadt.consistency.store.Stores
import de.tudarmstadt.consistency.store.cassandra.ConnectionParams

import scala.reflect.runtime.universe._

/**
	* Created on 18.12.18.
	*
	* @author Mirko Köhler
	*/
class CassandraIntegration(val connectionParams : ConnectionParams) {

	sealed trait ConsistencyLevel
	sealed trait Strong extends ConsistencyLevel
	sealed trait Weak extends ConsistencyLevel

	def session[A](f : Language => A) : A = {
		val store = Stores.Default.newStore(connectionParams)
		import store._

		startSession { session =>
			import session._

			object CassandraLanguage extends Language {
				override type Addr = Stores.Default.Key
				override type Consistency = ConsistencyLevel

				private val ttStrong : TypeTag[Strong] = typeTag[Strong]
				private val ttWeak : TypeTag[Weak] = typeTag[Weak]

				private def matchConsistencyLevel[C <: ConsistencyLevel : TypeTag, T](caseStrong : =>T, caseWeak : =>T) : T = typeTag[C] match {
					case `ttStrong` => caseStrong
					case `ttWeak` => caseWeak
					case x => sys.error(s"unknown consistency type $x")
				}

				private var currentTransaction : TxCtx = _



				override def enref[T, C <: ConsistencyLevel : TypeTag](value : T) : Ref[T, C] = {

					if (currentTransaction == null) {
						matchConsistencyLevel[C, Ref[T, C]] (
							session.startTransaction(Stores.Default.IsolationLevels.NONE) { tx =>

							},
							???
						)
					}
					???
				}


				override def deref[T, C <: ConsistencyLevel](ref : Ref[T, C]) : Option[T] = {
					if (currentTransaction == null) {
						matchConsistencyLevel(
							startTransaction(Stores.Default.IsolationLevels.SI) {tx => tx.read(ref.addr, Stores.Default.ConsistencyLevels.CAUSAL)},
							startTransaction(Stores.Default.IsolationLevels.RC) {tx => tx.read(ref.addr, Stores.Default.ConsistencyLevels.WEAK)},
						)(ref.consistencyLevel)
					} else {
						matchConsistencyLevel(
							currentTransaction.read(ref.addr, Stores.Default.ConsistencyLevels.CAUSAL),
							currentTransaction.read(ref.addr, Stores.Default.ConsistencyLevels.WEAK)
						)
					}
				}
				override def update[T, C <: ConsistencyLevel](ref : Ref[T, C], value : T) : Unit = ???
				override def isolate[T](c : => T) : Option[T] = ???
				override def cast[T, C <: ConsistencyLevel : TypeTag](value : T) : T = ???
			}


			f(CassandraLanguage)
		}





	}





}
