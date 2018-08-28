package de.tudarmstadt.consistency.store.scala.shim

import java.lang.annotation.Annotation

import de.tudarmstadt.consistency.checker.qual.{Strong, Weak}
import de.tudarmstadt.consistency.store.scala.impl.ReadWriteStore
import de.tudarmstadt.consistency.store.scala.shim

import scala.collection.mutable


/**
	* Created on 09.08.18.
	*
	* @author Mirko Köhler
	*/
abstract class VersionedStore[Key, Val] extends ReadWriteStore[Key, Val, Class[_ <: Annotation]] {

	type Id

	type Update = shim.Update[Id, Key, Val]

	val store : ReadWriteStore[Id, Update, Class[_ <: Annotation]]
	val idFactory : () => Id

	private val versionGraph : VersionGraph = new VersionGraph


	override type Context = VersionedSessionContext


	override def newSessionContext() : Context =
		new VersionedSessionContext

	override def close(): Unit = {
		store.close()
	}

	private def newId() : Id = idFactory.apply()

	private def addUpdateToStore(id : Id, update : Update, consistencyLevel : Class[_ <: Annotation]) : Unit = {
		store.commit(session => {
			val ref = session.obtain[Update](id, consistencyLevel)
			ref.write(update)
		})
	}

	private def getUpdateFromStore[T <: Val](id : Id, consistencyLevel : Class[_ <: Annotation]) : Option[Update] = {
		store.commit(session => {
			val ref = session.obtain[Update](id, consistencyLevel)
			ref.read()
		})
	}





	class VersionedSessionContext extends ReadWriteSessionContext {

		private var sessionPointer : Option[VersionGraphNode] = None
		private var nextDependencies : Set[VersionGraphNode] = Set.empty


		class CausalRef[T <: Val](val context : VersionedSessionContext, val key : Key) extends VersionedRef[Key, T] {

			override protected def handleRead(): Option[T] = {
				val (value, deps) = versionGraph.getValue(key)
				nextDependencies = nextDependencies ++ deps
				value
			}

			override protected def handleWrite(value: T): Unit = {
				synchronized {
					val newNode = versionGraph.addUpdate(key, value, nextDependencies)
					nextDependencies = Set(newNode)
					sessionPointer = Some(newNode)
				}
			}
		}

		def printSessionTree(): Unit = {
			println(sessionPointer.orNull)
		}


		override def obtain[T <: Val](key: Key, consistencyLevel: Class[_ <: Annotation]): VersionedRef[Key, T] = consistencyLevel match {
			//TODO: return the correct refs
			case x if x == classOf[Strong] => new CausalRef(this, key)
			case x if x == classOf[Weak] => new CausalRef(this, key)
			case x => throw new IllegalArgumentException(s"unsupported consistency level. expected Weak or Strong, but got $x")

		}
	}



	trait VersionGraphNode {
		val id : Id
		val dependsOn : Set[VersionGraphNode]
	}

	class VersionGraph {

		case class Entry(id : Id, key : Key, dependsOn : Set[VersionGraphNode]) extends VersionGraphNode {
			override def toString: String =
				toString(0)

			private def padding(i : Int) : String =
				(0 until i).foldLeft("")((s, n) => s + "\t")

			private def toString(pad : Int): String = {
				val storedValue : Any = getUpdateFromStore[Val](id, classOf[Strong]) match {
					case None => "<???>"
					case Some(Update(_, value, _)) => value
					case upd => s"<UNKNOWN UPDATE $upd>"
				}

				padding(pad) +  s"$id : $key = " + storedValue +
					dependsOn.foldLeft("")((res, node) => res + "\n" + node.asInstanceOf[Entry].toString(pad + 1))
			}

		}


		val keyPointer : mutable.Map[Key, VersionGraphNode] = mutable.HashMap.empty


		def addUpdate(key : Key, value : Val, dependencies : Set[VersionGraphNode]): VersionGraphNode = {
			val id = newId()
			val node = Entry(id, key, dependencies)
			val update = Update(key, value, dependencies.map((entry : VersionGraphNode) => entry.id))

			addUpdateToStore(id, update, classOf[Strong /*TODO: use appropriate consistency level*/])
			keyPointer.put(key, node)

			node
		}

		def getValue[T <: Val](key : Key) : (Option[T], Set[VersionGraphNode]) = {

			//TODO: Check whether dependencies are fulfilled.

			keyPointer.get(key) match {
				case None => (None, Set.empty)
				case Some(entry) => getUpdateFromStore(entry.id, classOf[Strong /*TODO: use appropriate consistency level*/]) match {
					case None => throw new IllegalStateException("") //TODO: Causal guarantee not fulfilled. Search for value that is already propagated
					case Some(update) => (Some(update.value.asInstanceOf[T]), Set(entry))
				}
			}
		}
	}
}

//Note: Update has to stay outside of VersionedStore to allow serializability.
case class Update[Id, Key, Val](key : Key, value : Val, dependencies : Set[Id])


object VersionedStore {
}

