package de.tudarmstadt.consistency.store.shim

import de.tudarmstadt.consistency.store.shim.Event.{Tx, Update}
import de.tudarmstadt.consistency.store.shim.EventRef.{TxRef, UpdateRef}
import de.tudarmstadt.consistency.store.shim.Resolved.{Found, NotFound}

import scala.collection.mutable

/**
	* Note: The dependency graph does not store any transaction records anymore.
	* Transaction isolation is ensured before updates are pushed to the dependency graph layer.
	* Some tests that include transactions may not run properly.
	*
	* @author Mirko Köhler
	*/
class DependencyGraph[Id : Ordering, Key, Data] {

	final type Update = de.tudarmstadt.consistency.store.shim.Event.Update[Id, Key, Data]
	final type Tx = de.tudarmstadt.consistency.store.shim.Event.Tx[Id, Key, Data]



	/* Stores all entries of this dependency graph */
	private val entries : mutable.Map[Id, Update] = mutable.HashMap.empty
	/* Stores all transactions in this dependency graph */
//	private val transactions : mutable.Map[Id, Tx] = mutable.HashMap.empty

	/* indexes the pointers to the latest updates to keys. the first update in the list is the latest. updates may not be resolved yet */
	private val latestKeys : mutable.MultiMap[Key, Update] = new mutable.HashMap[Key, mutable.Set[Update]]() with mutable.MultiMap[Key, Update] {
		override protected def makeSet: mutable.Set[Update] = mutable.TreeSet[Update]()
	}


	//The ordering used for the sorted treeset in latestkeys
	private implicit val updateOrdering : Ordering[Update] = (x : Update, y : Update) =>
			//Swap x and y so that updates with higher ids are ordered before updates with lesser id
			Ordering.Tuple2(Ordering[Id], Ordering[Id]).compare(y.getSortingKey, x.getSortingKey)



	private def getEntry(id : Id) : Option[Update] = {
		val r = entries.get(id)
		//Check whether the returned event fits the given reference
		r.foreach(evt => assert(evt.id == id, s"reference does not fit stored event. expected: $id, but was: ${evt.id}"))
		r
	}


	def isResolved(id : Id) : Boolean = {
		//TODO: Use memoize already resolved nodes
		def isResolved(otherRef : Id, alreadyVisited : Set[Id]) : Boolean = getEntry(otherRef) match {
			case None => false
			case Some(evt) if alreadyVisited.contains(evt.id) => false
			case Some(evt) =>
				val newSet = alreadyVisited + evt.id
				evt.dependencies.forall(r => isResolved(r.id, newSet))
		}
		isResolved(id, Set.empty)
	}

	def unresolvedDependenciesOf(ref : EventRef[Id, Key]) : Set[EventRef[Id, Key]] = {
		//TODO: Use memoize already resolved nodes
		def unresolvedDependenciesOf(otherRef : EventRef[Id, Key], alreadyVisited : Set[Id]): Set[EventRef[Id, Key]] =
			getEntry(otherRef.id) match {
				case None =>
					Set(otherRef)
				case Some(evt) if alreadyVisited.contains(evt.id) =>
					Set.empty
				case Some(evt) =>
					val newSet = alreadyVisited + evt.id
					val unresolved : Set[EventRef[Id, Key]] =
						evt.dependencies.flatMap(dep => unresolvedDependenciesOf(dep, newSet))

					unresolved
			}

		unresolvedDependenciesOf(ref, Set.empty)
	}



	def addUpdate(update : Update) : Unit = {
		//add the update to the tree
		entries.put(update.id, update)
			// if the update already existed make sure that the overriding update is the same
			.foreach(evt => assert(evt == update, s"cannot override existing update with other update. other update was $evt"))

		//add the update to the latestKeys index
		latestKeys.addBinding(update.key, update)
	}

	/**
		* Reads a key from the dependency graph.
		* @param key The key to read from the graph.
		* @param txid The transaction id will not be considered unresolved. Use this when a read happens inside a
		*             transaction to satisfy "Read-your-writes".
		* @return A resolved value that contains the update that has been read.
		*/
	def resolve(key : Key, txid : Option[TxRef[Id]] = None) : Resolved[Update, EventRef[Id, Key]] = latestKeys.get(key) match {
		case None => NotFound()
		case Some(updates) =>
			//Store all unresolved dependencies
			var unresolved : Set[EventRef[Id, Key]] = Set.empty

			//Retrieve the latest known update
			val latest : Update = updates.head

			for(upd <- updates) {
				val unresolvedForId = unresolvedDependenciesOf(upd.toRef) -- txid
				//there are no unresolved dependencies
				if (unresolvedForId.isEmpty) {
					//If there are versions that are older then the latest resolved version, then drop them
					//We cant remove older updates, because the latest update might get deleted.
					//TODO: Is it really the case? Deletion currently only happens when transaction are aborted.
					//An aborted transaction has no transaction record and thus the dependencies on the updates
					//are not fulfilled, i.e. deleted updates are never resolved.
					//versions.retain(_id =>  ordering.lteq(_id, id))
					return Found(Some(upd), latest, unresolved)
				} else {
					unresolved = unresolved ++ unresolvedForId
				}
			}
			return Found(None, latest, unresolved)
	}


	def remove(id : Id): Option[Update] = entries.remove(id) match {
		case None => None
		case opt@Some(upd@Update(_,_,_,_,_)) =>
			latestKeys.keys.foreach(key => latestKeys.removeBinding(key, upd))
			opt
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


