package de.tudarmstadt.consistency.store.shim

import scala.collection.mutable
import Event._

/**
	* Created on 30.08.18.
	*
	* @author Mirko Köhler
	*/

object EventOrdering {


	sealed trait ReadResult[Id, Key, Data]
	/*Some data has been successfully found and resolved (= all dependencies have been satisfied). It also returns the latest known value, as well as all unresolved dependencies for the latest value.*/
	case class Resolved[Id, Key, Data](data : Update[Id, Key, Data], latest : Update[Id, Key, Data], unresolved: Set[EventRef[Id, Key]])  extends ReadResult[Id, Key, Data]
	/*Data has been found but there are still some unresolved dependencies */
	case class Unresolved[Id, Key, Data](data : Update[Id, Key, Data], unresolved : Set[EventRef[Id, Key]])  extends ReadResult[Id, Key, Data]
	/*The key has not been found.*/
	case class NotFound[Id, Key, Data]() extends ReadResult[Id, Key, Data]


//	case class ReadResult[Id, Key, Data](node : Option[Update[Id, Key, Data]], found : Boolean, unresolved : Set[EventRef[Id, Key]]) {
//		def getId : Option[Id] = node.map(n => n.getId)
//		def isFound : Boolean = found
//	}


	private [shim] class DependencyGraph[Id : Ordering, Key, Data] {
		type Node = Event[Id, Key, Data]

		/* Stores all entries of this dependency graph */
		private val entries : mutable.Map[Id, Node] = mutable.HashMap.empty

		/* Stores the pointers to the latest updates to keys. the first update in the list is the latest. updates may not be resolved yet */
		private val latestKeys : mutable.Map[Key, mutable.SortedSet[Id]] = mutable.HashMap.empty

		/* Ordering of ids. Specify which ids are newer/older. */
		private val ordering = implicitly[Ordering[Id]]



		def addTx(id : Id, deps : Set[EventRef[Id, Key]]): Tx[Id, Key, Data] = {
			val tx = Tx[Id, Key, Data](id, deps)
			addRaw(id, tx)
			tx
		}

		def addUpdate(id : Id, key : Key, data : Data, txid : Option[Id], dependencies : Set[EventRef[Id, Key]]): Update[Id, Key, Data] = {
			val upd = Update(id, key, data, txid, dependencies)
			addRaw(id, key, upd)
			upd
		}

		private [shim] def addRaw(id : Id, key : Key, update : Update[Id, Key, Data]) : Unit = {
			entries.put(id, update)
			putUpdateForKey(key, id)
		}

		private [shim] def addRaw(id : Id, tx : Tx[Id, Key, Data]) : Unit = {
			entries.put(id, tx)
		}


		def get(id : Id) : Option[Node] = {
			entries.get(id)
		}

		def getDependencies(id : Id) : Option[Set[EventRef[Id, Key]]] = {
			entries.get(id).map(dep => dep.getDependencies)
		}

		def isResolved(ref : EventRef[Id, Key]) : Boolean =
			unresolvedDependenciesOf(ref).isEmpty


		def readResolved(key : Key) : ReadResult[Id, Key, Data] = latestKeys.get(key) match {
			case None => NotFound()
			case Some(versions) =>
				val iter = versions.iterator
				var i = 0

				//Store all unresolved dependencies
				var unresolved : Set[EventRef[Id, Key]] = Set.empty

				if (!iter.hasNext) {
					return NotFound()
				}

				//Retrieve the latest known update
				val latest : Update[Id, Key, Data] = get(versions.head) match {
					case None => null
					//TODO: Check that the event is really an Update and act accordingly
					case Some(node) => node.asInstanceOf[Update[Id, Key, Data]]
				}
				assert(latest != null, "latest version was in versions but not found in entries")


				while(iter.hasNext) {
					val id = iter.next()
					val unresolvedForId = unresolvedDependenciesOf(EventRef(id, key))

					//there are no unresolved dependencies
					if (unresolvedForId.isEmpty) {
						//If there are versions that are older then the latest resolved version, then drop them
						//We cant remove older updates, because the latest update might get deleted.
						//TODO: Is it really the case? Deletion currently only happens when transaction are aborted.
						//An aborted transaction has no transaction record and thus the dependencies on the updates
						//are not fulfilled, i.e. deleted updates are never resolved.
						//versions.retain(_id =>  ordering.lteq(_id, id))



						val resolved = get(id) match {
							case None => null
							//TODO: Check that the event is really an Update and act accordingly
							case Some(node) => node.asInstanceOf[Update[Id, Key, Data]]
						}

						assert(resolved != null, "id was in versions but not found in entries")

						return Resolved(resolved, latest, unresolved)
					} else {
						unresolved = unresolved ++ unresolvedForId
					}
					i += 1
				}

				return Unresolved(latest, unresolved)
		}


		def remove(id : Id): Option[Node] = entries.remove(id) match {
			case None =>
				//TODO: Remove this assertion? Ids could be removed that have not propagated yet.
  			assert(false, "the entry cannot be removed as it is not part of the dependency graph")
				None
			case opt@Some(dep) =>
				assert(!dep.isResolved, "cannot remove resolved dependencies")

				latestKeys.foreach(entry => entry._2 -= id)
				opt
		}

		private def putUpdateForKey(key : Key, id : Id): Unit = latestKeys.get(key) match {
			case None => latestKeys.put(key, mutable.TreeSet(id)(ordering.reverse))
			case Some(buf) => buf.add(id)
		}


		//TODO: Check whether this method can be simplified... Also it is bugged
		def unresolvedDependenciesOf(ref : EventRef[Id, Key]) : Set[EventRef[Id, Key]] = {

			def unresolvedDependencies(innerRef : EventRef[Id, Key], visited : Set[Id]): Set[EventRef[Id, Key]] = {
				val id = innerRef.id

				if (visited.contains(id))
					return Set.empty //TODO: What to return here?

				entries.get(id) match {
					case None =>
						if (innerRef == ref)
							Set.empty[EventRef[Id, Key]]
						else
							Set(innerRef)
					case Some(dep) => if (dep.isResolved) {
						Set.empty
					} else {
						val extendedSet = visited + id
						val unresolved : Set[EventRef[Id, Key]] = dep.getDependencies.flatMap(other => unresolvedDependencies(other, extendedSet))

						if (unresolved.isEmpty) {
							dep.setResolved()
							Set.empty
						} else {
							if (innerRef == ref)
								unresolved
							else
								unresolved + innerRef
						}
					}
				}

			}

			unresolvedDependencies(ref, Set.empty)
		}

		override def toString : String = {
			var s = ""
			s += "entries:"
			s += entries.foldLeft("")((str, entry) => s"$str\n${entry._1} -> ${entry._2}")
			s += "\nhistories:"
			s += latestKeys.foldLeft("")((str, entry) => s"$str\nh(${entry._1}) = ${entry._2}")
			s
		}


	}

	class SessionOrder[Id : Ordering, Key, Data] {

		private type Node = Event[Id, Key, Data]

		//The latest node that has been created in this transaction
		private var sessionPointer : Option[EventRef[Id, Key]] = None
		//stores the session pointer before a transaction as a fallback in case the tx gets aborted.
		private var sessionPointerBeforeTx : Option[EventRef[Id, Key]] = None

		//The reads that occurred since the last node has been added
		private var readDependencies : Set[EventRef[Id, Key]] = Set.empty

		//The transaction id of the current transaction
		private var transactionPointer : Option[Id] = None
		//The ids of all updates that happened during this transaction
		private var transactionDependencies : Set[EventRef[Id, Key]] = Set.empty


		private [store] val graph : DependencyGraph[Id, Key, Data] = new DependencyGraph()


		def addUpdate(id : Id, key : Key, data : Data): Unit = {
			graph.addUpdate(id, key, data, transactionPointer, getNextDependencies)

			val eventRef = EventRef(id, key)

			sessionPointer = Some(eventRef)
			readDependencies = Set.empty

			if (transactionPointer.isDefined)
				transactionDependencies += eventRef
		}

		def addRead(ref : EventRef[Id, Key]): Unit = {
			readDependencies = readDependencies + ref
		}

		def getDependencies(id : Id) : Option[Set[EventRef[Id, Key]]] = {
			graph.getDependencies(id)
		}

		def getNextDependencies : Set[EventRef[Id, Key]] = {
			readDependencies ++ sessionPointer
		}

		//You need to manually add a read with addRead if this read should be visible as a dependency
		def read(key : Key) : ReadResult[Id, Key, Data] =
			graph.readResolved(key)


		def startTransaction(id : Id): Unit = {
			assert(transactionPointer.isEmpty)

			sessionPointerBeforeTx = sessionPointer
			transactionPointer = Some(id)
			transactionDependencies = Set.empty
		}

		def commitTransaction(): Unit = transactionPointer match {
			case None => assert(assertion = false, "cannot commit a transaction that has never started")
			case Some(id) =>
				graph.addTx(id, transactionDependencies)
				transactionDependencies = Set.empty
				transactionPointer = None
		}

		def abortTransaction() : Unit = transactionPointer match {
			case None => assert(assertion = false, "cannot abort a transaction that has never started")
			case Some(id) =>
				transactionDependencies.foreach(ref => graph.remove(ref.id))
				transactionDependencies = Set.empty
				transactionPointer = None
				//Reset session pointer to "before the transaction"
				sessionPointer = sessionPointerBeforeTx
		}

		private [shim] def addRaw(id : Id, key : Key, update : Update[Id, Key, Data]) : Unit = {
			graph.addRaw(id, key, update)
		}

		private [shim] def addRaw(id : Id, tx : Tx[Id, Key, Data]) : Unit = {
			graph.addRaw(id, tx)
		}


		override def toString : String = {
			graph.toString
		}

	}

	def newSessionOrder[Id : Ordering, Key, Data] : SessionOrder[Id, Key, Data] =
		new SessionOrder[Id, Key, Data]


}
