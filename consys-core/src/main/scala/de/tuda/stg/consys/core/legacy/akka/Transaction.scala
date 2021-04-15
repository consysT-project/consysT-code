package de.tuda.stg.consys.core.legacy.akka

import de.tuda.stg.consys.core.legacy.ConsistencyLabel
import de.tuda.stg.consys.core.legacy.akka.Transaction.NestedTransaction
import scala.collection.mutable

/**
	* Created on 12.04.19.
	*
	* @author Mirko Köhler
	*/
private[akka] trait Transaction extends Serializable {

	val timestamp : Long = System.currentTimeMillis()

	def consistencyLevel : ConsistencyLabel
	def id : Long

	def isToplevel : Boolean = getParent.isEmpty

	def getParent : Option[Transaction]

	def addLock(rob : String) : Unit

	def removeLock(rob : String) : Unit

	def locks : Iterable[String]

	def hasOnlyLevel(level : ConsistencyLabel) : Boolean

	def start(consistencyLevel : ConsistencyLabel) : Transaction = {
		NestedTransaction(this, incAndGetSeqFor(consistencyLevel), consistencyLevel)
	}



	@transient private var sequence : mutable.Map[ConsistencyLabel, Int] = null

	private def incAndGetSeqFor(level : ConsistencyLabel): Int = {
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
	case class ToplevelTransaction(override val id : Long, override val consistencyLevel : ConsistencyLabel)
		extends Transaction {

		override def getParent : Option[Transaction] = None


		private val lockList : mutable.Buffer[String] = mutable.Buffer.empty

		override def addLock(rob : String) : Unit = {
			lockList += rob
		}

		override def removeLock(rob : String) : Unit = {
			lockList -= rob
		}

		override def locks : Iterable[String] = lockList


		override def toString : String = s"tx[locked=${lockList.mkString(",")}]::$consistencyLevel|$id"

		override def hasOnlyLevel(level : ConsistencyLabel) : Boolean =
			consistencyLevel == level
	}

	@SerialVersionUID(-1542145564L)
	case class NestedTransaction(parent : Transaction, seqId : Int, override val consistencyLevel : ConsistencyLabel)
		extends Transaction {

		override def id : Long = parent.id

		override def getParent : Option[Transaction] = Some(parent)

		override def addLock(rob : String) : Unit = {
			parent.addLock(rob)
		}

		override def removeLock(rob : String) : Unit = {
			parent.removeLock(rob)
		}

		override def locks : Iterable[String] = parent.locks


		override def toString : String = parent.toString + s"::/$consistencyLevel|$seqId"

		override def hasOnlyLevel(level : ConsistencyLabel) : Boolean =
			consistencyLevel == level && parent.hasOnlyLevel(level)


	}


}
