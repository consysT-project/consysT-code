package de.tuda.stg.consys.lang

/**
	* Created on 04.07.19.
	*
	* @author Mirko Köhler
	*/
sealed trait Label

object Label {
	case object THIS extends Label
	case object Weak extends Label
	case object Strong extends Label
	case object LOCAL extends Label
}
