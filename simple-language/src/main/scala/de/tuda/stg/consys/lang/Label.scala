package de.tuda.stg.consys.lang

/**
	* Created on 04.07.19.
	*
	* @author Mirko Köhler
	*/
sealed trait Label

object Label {
	sealed trait AbstractLabel extends Label
	case object THIS extends AbstractLabel

	sealed trait ConcreteLabel extends Label

	sealed trait ConsistencyLabel extends ConcreteLabel {
		def joinWith(other : ConsistencyLabel) : ConsistencyLabel

		def isSmallerEq(other : ConsistencyLabel) : Boolean =
			this.joinWith(other) == other
	}
	case object Weak extends ConsistencyLabel {
		override def joinWith(other : ConsistencyLabel) : ConsistencyLabel = other match {
			case Weak => Weak
			case Strong => Weak
		}
	}
	case object Strong extends ConsistencyLabel {
		override def joinWith(other : ConsistencyLabel) : ConsistencyLabel = other match {
			case Weak => Weak
			case Strong => Strong
		}
	}

	case object LOCAL extends ConcreteLabel


}
