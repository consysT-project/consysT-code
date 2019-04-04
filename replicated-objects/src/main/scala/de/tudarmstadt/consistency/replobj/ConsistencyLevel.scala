package de.tudarmstadt.consistency.replobj

/**
	* Created on 14.02.19.
	*
	* @author Mirko Köhler
	*/

sealed trait ConsistencyLevel extends Serializable

object ConsistencyLevel {

	@SerialVersionUID(639383L)
	case object Inconsistent extends ConsistencyLevel
	@SerialVersionUID(639384L)
	case object Weak extends ConsistencyLevel
	@SerialVersionUID(639385L)
	case object Eventual extends ConsistencyLevel
	@SerialVersionUID(639386L)
	case object Causal extends ConsistencyLevel
	@SerialVersionUID(639387L)
	case object Strong extends ConsistencyLevel
	@SerialVersionUID(639388L)
	case object Local extends ConsistencyLevel

//	private val WeakType : Class[Weak] = classOf[Weak]
//	private val StrongType : Class[Strong] = classOf[Strong]
//
//	def isWeak[L : Class] : Boolean =
//		implicitly[Class[L]] == WeakType
//
//	def isStrong[L : Class] : Boolean =
//		implicitly[Class[L]] == StrongType
}
