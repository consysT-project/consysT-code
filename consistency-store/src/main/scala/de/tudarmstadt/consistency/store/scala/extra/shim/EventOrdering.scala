package de.tudarmstadt.consistency.store.scala.extra.shim


import scala.collection.mutable

/**
	* Created on 30.08.18.
	*
	* @author Mirko Köhler
	*/

object EventOrdering {


//	private sealed trait AnyNode[+Id, +Key, +Data] {
//		def getData : Option[Data]
//	}
//	private sealed trait SessionNode[+Id, +Key, +Data] extends AnyNode[Id, Key, Data]
//	private sealed trait TxNode[+Id, +Key, +Data] extends AnyNode[Id, Key, Data]
//
//	//Updates can occur in session and in transactions
//	private case class Update[Id, Key, Data](id : Id, key : Key, data : Data) extends SessionNode[Id, Key, Data] with TxNode[Id, Key, Data] {
//		val getData : Option[Data] = Some(data)
//	}
//
//	//Transactions can occur in sessions, but no nested transactions are allowed
//	private case class Tx[Id, Key, Data](id : Id, order : TxEventOrder[Id, Key, Data]) extends SessionNode[Id, Key, Data] {
//		val getData : Option[Data] = None
//	}


	trait Event[Id, Key, Data] {
		def getDependencies : Set[Id]
		def getData : Option[Data]
		def getId :Id
		val resolvedDependencies : Array[Boolean] = Array(false)

		def isResolved : Boolean = resolvedDependencies(0)
		def setResolved(): Unit =	resolvedDependencies(0) = true
	}

	//Note: val dependencies does not contain the txid.
	case class Update[Id, Key, Data](id : Id, key : Key, data : Data, txid : Option[Id], dependencies : Set[Id]) extends Event[Id, Key, Data] {
		override def getDependencies : Set[Id] = dependencies ++ txid
		override def getData : Option[Data] =	Some(data)
		override def getId : Id = id
	}

	case class Tx[Id, Key, Data](id : Id, deps : Set[Id]) extends Event[Id, Key, Data] {
		override def getDependencies : Set[Id] = deps
		override def getData : Option[Data] = None
		override def getId : Id = id
	}





	private class DependencyGraph[Id : Ordering, Key, Data] {
		private val ordering = implicitly[Ordering[Id]]

		type Node = Event[Id, Key, Data]

		/* Stores all entries of this dependency graph */
		private val entries : mutable.Map[Id, Node] = mutable.HashMap.empty

		/* Stores the pointers to the latest updates to keys. the first update in the list is the latest. updates may not be resolved yet */
		private val latestKeys : mutable.Map[Key, mutable.SortedSet[Id]] = mutable.HashMap.empty




		def addTx(id : Id, deps : Set[Id]): Tx[Id, Key, Data] = {
			val tx = Tx[Id, Key, Data](id, deps)
			addRaw(id, tx)
			tx
		}

		def addUpdate(id : Id, key : Key, data : Data, txid : Option[Id], sessionDependency : Option[Id], readDependencies : Set[Id]): Update[Id, Key, Data] = {
			val upd = Update(id, key, data, txid, readDependencies ++ sessionDependency)
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

		def getDependencies(id : Id) : Option[Set[Id]] = {
			entries.get(id).map(dep => dep.getDependencies)
		}

		def readResolved(key : Key) : Option[(Id, Node)] = latestKeys.get(key) match {
			case None => None
			case Some(versions) =>
				val iter = versions.iterator
				var i = 0

				while(iter.hasNext) {
					val id = iter.next()
					if (checkResolved(id)) {

						//If there are versions that are older then the latest resolved version, then drop them
						//We cant remove older updates, because the latest update might get deleted.
						//TODO: Is it really the case? Deletion currently only happens when transaction are aborted.
						//An aborted transaction has no transaction record and thus the dependencies on the updates
						//are not fulfilled, i.e. deleted updates are never resolved.
						versions.retain(_id =>  ordering.lteq(_id, id))


						return get(id).map(node => (id, node))
					}
					i += 1
				}
				return None
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
			case None => latestKeys.put(key, mutable.TreeSet(id))
			case Some(buf) => buf.add(id)
		}


		private def checkResolved(id : Id) : Boolean = {
			def checkResolved(id : Id, visited : Set[Id]): Boolean = {
				if (visited.contains(id))
					return true //TODO: What to return here?

				entries.get(id) match {
					case None => false
					case Some(dep) => if (dep.isResolved) {
						true
					} else {
						val extendedSet = visited + id
						if (dep.getDependencies.forall(otherId => checkResolved(otherId, extendedSet))) {
							dep.setResolved()
							true
						} else {
							false
						}
					}
				}
			}

			checkResolved(id, Set.empty)
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
		var sessionPointer : Option[Id] = None
		//The reads that occurred since the last node has been added
		var readDependencies : Set[Id] = Set.empty

		//The transaction id of the current transaction
		var transactionPointer : Option[Id] = None
		//The ids of all updates that happened during this transaction
		var transactionDependencies : Set[Id] = Set.empty


		private val graph : DependencyGraph[Id, Key, Data] = new DependencyGraph()


		def addUpdate(id : Id, key : Key, data : Data): Unit = {
			graph.addUpdate(id, key, data, transactionPointer, sessionPointer, readDependencies)

			sessionPointer = Some(id)
			readDependencies = Set.empty

			if (transactionPointer.isDefined)
				transactionDependencies += id
		}

		def addRead(id : Id): Unit = {
			readDependencies = readDependencies + id
		}

		def getDependencies(id : Id) : Option[Set[Id]] = {
			graph.getDependencies(id)
		}

		def getNextDependencies : Set[Id] = {
			readDependencies ++ transactionPointer ++ sessionPointer
		}

		def readResolved(key : Key) : Option[(Id, Data)] = {
			graph.readResolved(key).flatMap(t => {
				val (id, node) = t
				node.getData match {
					case None => None
					case Some(data) => Some (id, data)
				}
			})
		}

		def readLatest(key : Key) : Option[(Id, Data)] = {
			graph.readLatest(key).flatMap(t => {
				val (id, node) = t
				node.getData match {
					case None => None
					case Some(data) => Some (id, data)
				}
			})
		}

		def startTransaction(id : Id): Unit = {
			assert(transactionPointer.isEmpty)

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
				transactionDependencies.foreach(graph.remove)
				transactionDependencies = Set.empty
				transactionPointer = None
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
