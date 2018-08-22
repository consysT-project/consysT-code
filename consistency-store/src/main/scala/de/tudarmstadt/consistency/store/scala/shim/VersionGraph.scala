package de.tudarmstadt.consistency.store.scala.shim

import de.tudarmstadt.consistency.checker.qual.Strong
import de.tudarmstadt.consistency.store.scala.shim

import scala.collection.mutable

/**
	* Created on 13.08.18.
	*
	* @author Mirko Köhler
	*/
trait VersionGraph[Id, Key, Val] {
/*


	/*
	Cassandra:

	CREATE TABLE table_prim (id int, key text, data text, PRIMARY KEY (key, id));
	key is partitioning key, id is clustering key (for sorting)

	SELECT MAX(id), key, data FROM table_prim WHERE key = 'z';
	find the maximum key among all available keys.
	 */

	private val nodes : GraphNodes = new GraphNodes




	private val keyHistory : KeyHistory = new KeyHistory

	private class KeyHistory {
		private val histories : mutable.Map[Key, List[Id]] = mutable.HashMap.empty

		def add(k : Key, node : Update): Unit = {
			histories.get(k) match {
				case None => histories.put(k, List(node))
				case Some(l) => histories.put(k, node :: l)
			}
		}

		def get(k : Key) : Option[Update] = {
			histories.get(k) match {
				case None => None
				case Some(Nil) => None
				case Some(l) =>
					l.find(node => contains(node))
			}
		}

		override def toString : String = {
			histories.foldLeft("")((res, entry) => {
				val key : Key = entry._1
				val value : List[GraphNode] = entry._2

				var s = s"${res}### key $key ###\n"

				var firstVersion = true
				for (n <- value) {
					if (!contains(n)) {
						s += s"-unresolved\n${n.toStringWithoutDeps}\n"
					} else if (firstVersion) {
						s += s"-pointsTo\n$n\n"
						firstVersion = false
					} else {
						s += s"-resolved\n$n\n"
					}
				}

				s
			})

			//histories.toString
		}
	}

	def startSession() : VersionedSession =
		new VersionedSession

	override def toString : String = {
		keyHistory.toString
	}


	class GraphNodes extends mutable.Map[Id, GraphEntry] {

		/**
			* Maps ids to their specific events as well as unresolved dependencies.
			*/
		private val data : mutable.Map[Id, GraphEntry] = mutable.HashMap.empty

		/**
			* Maps ids to other ids that have still unresolved dependencies of the first id.
			*/
		private val unresolvedDependencies : mutable.MultiMap[Id, Id] = new mutable.HashMap[Id, mutable.Set[Id]] with mutable.MultiMap[Id, Id]

		override def +=(kv : (Id, GraphEntry)) : GraphNodes.this.type = {
			data += kv
			this
		}

		override def -=(key : Id) : GraphNodes.this.type =
			???

		override def get(key : Id) : Option[GraphEntry] =
			data.get(key)

		override def iterator : Iterator[(Id, GraphEntry)] =
			data.iterator


		def isResolved(dependency : Id) : Boolean =
			nodes.get(dependency).fold(false)(entry => entry.isResolved)

		def isResolved(dependencies : Iterable[Id]) : Boolean =
			dependencies.forall(id => isResolved(id))


		def addEvent(id : Id, e : Event, sessionDependencies : Set[Id], visibleDependencies : Set[Id]) : Unit = {
			assert(!nodes.contains(id))

			val entry = new GraphEntry(e, sessionDependencies, visibleDependencies)
			nodes.put(id, entry)

			if (!entry.isResolved) {
				entry.foreachUnresolvedDependency(_id => unresolvedDependencies.addBinding(_id, id))
			}
		}






		private def addNode(node : GraphNode): Unit = {

			//Updates the dependencies when a new node (with resolved dependencies) has been added
			def updateDependencies(newNode : GraphNode): Unit = {

				//First remove dependencies and update other dependencies
				unresolvedDependencies.get(newNode) match {
					case None => //no unresolved dependencies with the newNode
					case Some(openDependencies) =>
						unresolvedDependencies.remove(newNode)

						openDependencies.foreach(_n =>
							nodes.get(_n) match {
								case None => assert(false)
								case Some(nodeSet) =>
									nodeSet.remove(newNode)
									if (nodeSet.isEmpty) {
										updateDependencies(_n)
									}
							}
						)
				}
			}

			def updateVersion(newNode : GraphNode): Unit = newNode match {
				case upd@Update(key, _, _) => keyHistory.add(key, upd)
				case _ =>
			}


			if (hasResolvedDependencies(node)) {
				//if the node has all dependencies resolved then update the unresolved dependencies
				nodes.put(node, mutable.Set.empty)
				updateDependencies(node)
				updateVersion(node)
			} else {
				//if there are unresolved dependencies, add the node to unresolvedDependencies
				val unresolvedDeps = mutable.Set.empty[GraphNode]
				unresolvedDeps ++= node.dependencies

				nodes.put(node, unresolvedDeps)
				unresolvedDeps.foreach(dep => unresolvedDependencies.addBinding(dep, node))

				updateVersion(node)
			}
		}
	}


	class GraphEntry(
		val event : Event,
		val sessionDependencies : Set[Id],
		val visibleDependencies : Set[Id]) {

		//Can be null!
		protected var unresolvedDependencies : mutable.Set[Id] = null
		initDependencies()

		def dependencies : Set[Id] =
			visibleDependencies ++ sessionDependencies

		def isResolved : Boolean =
			unresolvedDependencies != null && unresolvedDependencies.nonEmpty

		protected def initDependencies() : Unit = {
			dependencies.foreach(id => {
				if (!nodes.isResolved(id)) {
					if (unresolvedDependencies == null) {
						unresolvedDependencies = mutable.HashSet.empty
					}
					unresolvedDependencies.add(id)
				}
			})
		}

		protected def updateDependencies(): Unit = {
			if (unresolvedDependencies == null)
				return

			unresolvedDependencies.foreach(id => {
				if (nodes.isResolved(id)) unresolvedDependencies.remove(id)
			})

			if (unresolvedDependencies.isEmpty)
				unresolvedDependencies = null
		}

		def foreachUnresolvedDependency[U](f : Id => U) : Unit =
			unresolvedDependencies.foreach(f)
	}




	sealed trait Event
	case class Read(k : Key) extends Event
	case class Write(k : Key, v : Val) extends Event

	/*
	sealed trait GraphNode {
		def id : Id
		def sessionDependencies : Set[Id]
		def visibleDependencies : Set[Id]

		def dependencies : Set[Id] =
			visibleDependencies ++ sessionDependencies

		override def toString: String = {

			def padding(i : Int) : String =
				(0 until i).foldLeft("")((s, n) => s + "\t")

			def paddedStringFrom(node : GraphNode, pad : Int): String =
				padding(pad) + node.toStringWithoutDeps +
					node.dependencies.foldLeft("")((res, n) => s"$res\n${paddedStringFrom(n, pad + 1)}")


			paddedStringFrom(this, 0)
		}

		def toStringWithoutDeps : String = this match {
			case Update(id, k, v, _) =>	s"set<$id> $k := $v"
			case Read(id, k, _, _) =>  s"get<$id> $k"
		}
	}
	case class Update(id : Id, k : Key, v : Val, sessionDependencies : Set[Id]) extends GraphNode {
		val visibleDependencies : Set[Id] = Set.empty
	}
	case class Read(id : Id, k : Key, sessionDependencies : Set[Id], visibleDependencies : Set[Id]) extends GraphNode

	*/


	//Checks whether a node is contained in the graph. The graph does not contain nodes with unresolved dependencies.







	def handleChange(g : GraphNode) : Unit

	private def internalNotifyUpdate(k : Key, v : Val, sessionDependencies : Set[GraphNode]): Update = {
		val node = Update(k, v, sessionDependencies)
		addNode(node)
		node
	}

	private def internalNotifyRead(k : Key, sessionDependencies : Set[GraphNode], visibleDependencies : Set[GraphNode]): Read = {
		val node = Read(k, sessionDependencies, visibleDependencies)
		addNode(node)
		node
	}

	def notifyUpdate(k : Key, v : Val, sessionDependencies : Set[GraphNode]) : Update = this.synchronized {
		internalNotifyUpdate(k, v, sessionDependencies)
	}

	def notifyRead(k : Key, sessionDependencies : Set[GraphNode], visibleDependencies : Set[GraphNode]): Read = this.synchronized {
		internalNotifyRead(k, sessionDependencies, visibleDependencies)
	}

	private def addUpdate(k : Key, v : Val, sessionDependency : Option[GraphNode]): Update = this.synchronized {
		internalNotifyUpdate(k, v, sessionDependency.toSet)
	}

	private def addRead(k : Key, sessionDependency : Option[GraphNode]) : (Read, Option[Val]) = this.synchronized {
		val readNode = keyHistory.get(k)
		val node = internalNotifyRead(k, sessionDependency.toSet, readNode.toSet)
		(node, readNode.map(upd => upd.v))
	}

	class VersionedSession {

		private var sessionPointer : Option[GraphNode] = None

		def update(k : Key, v : Val): Unit = this.synchronized {
			val node = addUpdate(k, v, sessionPointer)
			sessionPointer = Some(node)
		}

		def read(k : Key) : Option[Val] = this.synchronized {
			val (node, optVal) = addRead(k, sessionPointer)
			sessionPointer = Some(node)
			optVal
		}

	}
}

object VersionGraph {

	def main(args : Array[String]): Unit = {
		val graph : VersionGraph[Char, Int] = new VersionGraph[Char, Int] {
			override def handleChange(g : GraphNode) : Unit =
				println("change:\n" + g)
		}

		val session0 = graph.startSession()
		val session1 = graph.startSession()
		val session2 = graph.startSession()

		session0.update('x', 11)
		session0.update('y', 22)
		session0.update('z', 33)

		session2.read('x') match {
			case None => session2.update('z', -1)
			case Some(value) => session2.update('z', value + 1)
		}

		session1.update('y', 64)
		session1.read('z')
		session1.update('y', 312)

		session2.update('x', 15)

		val r1 = graph.notifyRead('a', Set(graph.Update('a', 18, Set())), Set())
		val u2 = graph.notifyUpdate('a', 34, Set(r1))
		println(graph)

		graph.notifyUpdate('a', 18, Set())
		println(graph)

	}*/
}
