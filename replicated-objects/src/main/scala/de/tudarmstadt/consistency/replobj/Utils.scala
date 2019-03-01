package de.tudarmstadt.consistency.replobj

import scala.reflect.api.{Mirror, TypeCreator, Universe}

import scala.reflect.runtime.universe._

/**
	* Created on 01.03.19.
	*
	* @author Mirko Köhler
	*/
private[replobj] object Utils {

	def typeTagFromCls[T](cls : Class[T]) : TypeTag[T] = {
		val mirror = runtimeMirror(cls.getClassLoader)
		val tpe = mirror.classSymbol(cls).toType

		val objTypeCreator = new TypeCreator {
			def apply[U <: Universe with Singleton](m1: Mirror[U]): U#Type =
				if (m1 != mirror)
					sys.error("wrong mirror")
				else
					tpe.asInstanceOf[U#Type]
		}

		TypeTag[T](mirror, objTypeCreator)
	}

}
