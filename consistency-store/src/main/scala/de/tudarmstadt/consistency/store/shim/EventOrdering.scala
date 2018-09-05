package de.tudarmstadt.consistency.store.shim

import scala.collection.mutable
import Event._

/**
	* Created on 30.08.18.
	*
	* @author Mirko Köhler
	*/

object EventOrdering {


	case class ReadResult[Id, Key, Data](node : Option[Update[Id, Key, Data]], found : Boolean, unresolved : Set[EventRef[Id, Key]]) {
		def getId : Option[Id] = node.map(n => n.getId)
		def isFound : Boolean = found
	}


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


		def readResolved(key : Key) : ReadResult[Id, Key, Data] = latestKeys.get(key) match {
			case None => ReadResult(None, found = false, Set.empty)
			case Some(versions) =>
				val iter = versions.iterator
				var i = 0

				var unresolved : Set[EventRef[Id, Key]] = Set.empty

				while(iter.hasNext) {
					val id = iter.next()
					val unresolvedForId = unresolvedDependencies(EventRef(id, key))

					//there are no unresolved dependencies
					if (unresolvedForId.isEmpty) {
						//If there are versions that are older then the latest resolved version, then drop them
						//We cant remove older updates, because the latest update might get deleted.
						//TODO: Is it really the case? Deletion currently only happens when transaction are aborted.
						//An aborted transaction has no transaction record and thus the dependencies on the updates
						//are not fulfilled, i.e. deleted updates are never resolved.
						//versions.retain(_id =>  ordering.lteq(_id, id))


						return ReadResult(
							//TODO: Check that the event is really an Update and act accordingly
							get(id).asInstanceOf[Option[Update[Id, Key, Data]]], found = true, unresolved)
					} else {
						unresolved = unresolved ++ unresolvedForId
					}
					i += 1
				}
				return ReadResult(None, found = true, unresolved)
		}

		def readLatest(key : Key) : Option[(Id, Node)] = latestKeys.get(key) match {
			case None => None
			case Some(buf) => buf.headOption match {
				case None => None
				case Some(id) => get(id).map(node => (id, node))
			}
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


		private [shim] def unresolvedDependencies(ref : EventRef[Id, Key]) : Set[EventRef[Id, Key]] = {

			def unresolvedDependencies(ref : EventRef[Id, Key], visited : Set[Id]): Set[EventRef[Id, Key]] = {
				val id = ref.id

				if (visited.contains(id))
					return Set.empty //TODO: What to return here?

				entries.get(id) match {
					case None => Set(ref)
					case Some(dep) => if (dep.isResolved) {
						Set.empty
					} else {
						val extendedSet = visited + id
						val unresolved : Set[EventRef[Id, Key]] = dep.getDependencies.flatMap(other => unresolvedDependencies(other, extendedSet))

						if (unresolved.isEmpty) {
							dep.setResolved()
							Set.empty
						} else {
							unresolved + ref
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
		var sessionPointer : Option[EventRef[Id, Key]] = None
		//stores the session pointer before a transaction as a fallback in case the tx gets aborted.
		var sessionPointerBeforeTx : Option[EventRef[Id, Key]] = None

		//The reads that occurred since the last node has been added
		var readDependencies : Set[EventRef[Id, Key]] = Set.empty

		//The transaction id of the current transaction
		var transactionPointer : Option[Id] = None
		//The ids of all updates that happened during this transaction
		var transactionDependencies : Set[EventRef[Id, Key]] = Set.empty


		private val graph : DependencyGraph[Id, Key, Data] = new DependencyGraph()


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

		def readResolved(key : Key) : ReadResult[Id, Key, Data] = {
			val read = graph.readResolved(key)

			read.node match {
				case None =>
				case Some(evt) => addRead(EventRef(evt.id, evt.key))
			}

			read
		}

		def readLatest(key : Key) : Option[(Id, Data)] = {
			???
//			graph.readLatest(key).flatMap(t => {
//				val (id, node) = t
//				addRead(id, key)
//				node.getData match {
//					case None => None
//					case Some(data) => Some (id, data)
//				}
//			})
		}

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
				sessionPointer = sessionPointerBeforeTx
		}

		def abortTransaction() : Unit = transactionPointer match {
			case None => assert(assertion = false, "cannot abort a transaction that has never started")
			case Some(id) =>
				transactionDependencies.foreach(ref => graph.remove(ref.id))
				transactionDependencies = Set.empty
				transactionPointer = None
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
