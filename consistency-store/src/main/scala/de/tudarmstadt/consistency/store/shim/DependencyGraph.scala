package de.tudarmstadt.consistency.store.shim

import de.tudarmstadt.consistency.store.shim.Event.{Tx, Update}
import de.tudarmstadt.consistency.store.shim.EventRef.{TxRef, UpdateRef}
import de.tudarmstadt.consistency.store.shim.Resolved.{Found, NotFound}

import scala.collection.mutable

/**
	* Created on 06.09.18.
	*
	* @author Mirko Köhler
	*/
class DependencyGraph[Id : Ordering, Key, Data] {
	final type Event = de.tudarmstadt.consistency.store.shim.Event[Id, Key, Data]
	final type Update = de.tudarmstadt.consistency.store.shim.Event.Update[Id, Key, Data]
	final type Tx = de.tudarmstadt.consistency.store.shim.Event.Tx[Id, Key, Data]


	/* Stores all entries of this dependency graph */
	private val entries : mutable.Map[Id, Event] = mutable.HashMap.empty

	/* Stores the pointers to the latest updates to keys. the first update in the list is the latest. updates may not be resolved yet */
	private val latestKeys : mutable.MultiMap[Key, Update] = new mutable.HashMap[Key, mutable.Set[Update]]() with mutable.MultiMap[Key, Update] {
		override protected def makeSet: mutable.Set[Update] = mutable.TreeSet[Update]()
	}
	//The ordering used for the sorted treeset in latestkeys
	private implicit val updateOrdering : Ordering[Update] = new Ordering[Update] {
		override def compare(x : Update, y : Update) : Int =
			//Swap x and y so that updates with higher ids are ordered before updates with lesser id
			implicitly[Ordering[Id]].compare(y.id, x.id)
	}


	private def putEntry(node : Event) : Option[Event] =
		entries.put(node.id, node)

	private def getEntry(id : Id) : Option[Event] =
		entries.get(id)


	def isResolved(ref : EventRef[Id, Key]) : Boolean = {
		//TODO: Use memoize already resolved nodes
		def isResolved(otherRef : EventRef[Id, Key], alreadyVisited : Set[Id]) : Boolean = getEntry(otherRef.id) match {
			case None => false
			case Some(evt) if alreadyVisited.contains(evt.id) => false
			case Some(evt) =>
				val newSet = alreadyVisited + evt.id
				evt.dependencies.forall(r => isResolved(r, newSet))
		}
		isResolved(ref, Set.empty)
	}

	def unresolvedDependenciesOf(ref : EventRef[Id, Key]) : Set[EventRef[Id, Key]] = {
		//TODO: Use memoize already resolved nodes
		def unresolvedDependenciesOf(otherRef : EventRef[Id, Key], alreadyVisited : Set[Id]): Set[EventRef[Id, Key]] = getEntry(otherRef.id) match {
			case None => Set(otherRef)
			case Some(evt) if alreadyVisited.contains(evt.id) => Set.empty
			case Some(evt) =>
				val newSet = alreadyVisited + evt.id
				val unresolved : Set[EventRef[Id, Key]] =
					evt.dependencies.foldLeft(Set.empty[EventRef[Id, Key]])((xs, dep) => xs ++ unresolvedDependenciesOf(dep, newSet))
				unresolved
		}

		unresolvedDependenciesOf(ref, Set.empty)
	}

	def addTx(id : Id, deps : Set[UpdateRef[Id, Key]]): Tx = {
		val tx = Tx[Id, Key, Data](id, deps)
		addTx(tx)
		tx
	}


	def addUpdate(id : Id, key : Key, data : Data, txid : Option[TxRef[Id]], dependencies : Set[UpdateRef[Id, Key]]): Update = {
		val upd = Update(id, key, data, txid, dependencies)
		addUpdate(upd)
		upd
	}

	def addUpdate(update : Update) : Unit = {
		putEntry(update)
		putLatestKey(update)
	}

	def addTx(tx : Tx) : Unit = {
		putEntry(tx)
	}


	private def putLatestKey(upd : Update): Unit = {
		latestKeys.addBinding(upd.key, upd)
	}


	def read(key : Key) : Resolved[Update, EventRef[Id, Key]] = latestKeys.get(key) match {
		case None => NotFound()
		case Some(updates) =>
			//Store all unresolved dependencies
			var unresolved : Set[EventRef[Id, Key]] = Set.empty

			//Retrieve the latest known update
			val latest : Update = updates.head

			for(upd <- updates) {
				val unresolvedForId = unresolvedDependenciesOf(upd.toRef)

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


	def remove(id : Id): Option[Event] = entries.remove(id) match {
		case None => None
		case opt@Some(upd@Update(_,_,_,_,_)) =>
			latestKeys.foreach(entry => entry._2 -= upd)
			opt
		case opt@Some(Tx(_,_)) =>
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


