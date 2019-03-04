package de.tudarmstadt.consistency.replobj

import scala.reflect.api.{TypeCreator, Universe}

import scala.reflect.runtime.universe._

/**
	* Created on 01.03.19.
	*
	* @author Mirko Köhler
	*/
private[replobj] object Utils {

	def typeTagFromCls[T](cls : Class[T]) : TypeTag[T] = {
		/*TODO: Is there a better way to obtain TypeTags in Java code? These type tags here are not serializable.*/
		val mirror : Mirror = runtimeMirror(cls.getClassLoader)
		val tpe = mirror.classSymbol(cls).toType

		val objTypeCreator = SimpleTypeCreator(mirror, tpe)

		TypeTag[T](mirror, objTypeCreator)
	}

	private case class SimpleTypeCreator(mirror : Mirror, tpe : Type) extends TypeCreator {
		override def apply[U <: Universe with Singleton](m1: scala.reflect.api.Mirror[U]): U#Type =
			if (m1 != mirror)
				sys.error("wrong mirror")
			else
				tpe.asInstanceOf[U#Type]
	}

}
