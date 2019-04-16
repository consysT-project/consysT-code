package de.tudarmstadt.consistency.replobj.actors

import de.tudarmstadt.consistency.replobj.{ConsistencyLevel, ReplicatedObject}
import de.tudarmstadt.consistency.replobj.actors.Transaction.NestedTransaction

import scala.collection.mutable

/**
	* Created on 12.04.19.
	*
	* @author Mirko Köhler
	*/
trait Transaction extends Serializable {

	def consistencyLevel : ConsistencyLevel
	def txid : Long

	def contextPath : ContextPath

	def isToplevel : Boolean = getParent.isEmpty

	def getParent : Option[Transaction]

	def addLock(rob : String) : Unit

	def removeLock(rob : String) : Unit

	def locks : Iterable[String]

	def start(consistencyLevel : ConsistencyLevel) : Transaction = {
		new NestedTransaction(this, incAndGetSeqFor(consistencyLevel), consistencyLevel)
	}

	//TODO: Where to put this?
	@transient private var sequence : mutable.Map[ConsistencyLevel, Int] = null

	private def incAndGetSeqFor(level : ConsistencyLevel): Int = {
		if (sequence == null)
			sequence = mutable.HashMap.empty

		sequence.get(level) match {
			case None =>
				sequence.put(level, 0)
				0
			case Some(x) =>
				sequence.put(level, x + 1)
				x + 1
		}
	}
}

object Transaction {

	@SerialVersionUID(-9453185352L)
	case class ToplevelTransaction(override val txid : Long, override val consistencyLevel : ConsistencyLevel)
		extends Transaction {

		override def contextPath : ContextPath = ContextPath(txid)
		override def getParent : Option[Transaction] = None


		private val lockList : mutable.Buffer[String] = mutable.Buffer.empty

		override def addLock(rob : String) : Unit = {
			lockList += rob
		}

		override def removeLock(rob : String) : Unit = {
			lockList -= rob
		}

		override def locks : Iterable[String] = lockList


		override def toString : String = s"tx[locked=$lockList]::$consistencyLevel|$txid"
	}

	@SerialVersionUID(-1542145564L)
	case class NestedTransaction(parent : Transaction, seqId : Int, override val consistencyLevel : ConsistencyLevel)
		extends Transaction {

		override def txid : Long = parent.txid

		override def contextPath : ContextPath = parent.contextPath.withSeq(consistencyLevel, seqId)
		override def getParent : Option[Transaction] = Some(parent)

		override def addLock(rob : String) : Unit = {
			parent.addLock(rob)
		}

		override def removeLock(rob : String) : Unit = {
			parent.removeLock(rob)
		}

		override def locks : Iterable[String] = parent.locks


		override def toString : String = parent.toString + s"::/$consistencyLevel|$seqId"


	}


}
