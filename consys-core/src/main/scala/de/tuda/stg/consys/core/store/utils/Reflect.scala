package de.tuda.stg.consys.core.store.utils

import java.lang.reflect.{Constructor, Method}

import akka.util.BoxedType

import scala.util.Try

/**
 * Created on 20.02.20.
 *
 * @author Mirko Köhler
 */
object Reflect {

	def findConstructor[T](clazz: Class[T], args: Any*): Constructor[T] = {
		def error(msg: String): Nothing = {
			val argClasses = args.map(safeGetClass).mkString(", ")
			throw new IllegalArgumentException(s"$msg found on $clazz for arguments [$argClasses]")
		}

		val constructor: Constructor[T] =
			if (args.isEmpty) Try { clazz.getDeclaredConstructor() }.getOrElse(null)
			else {
				val length = args.length
				val candidates =
					clazz.getDeclaredConstructors.asInstanceOf[Array[Constructor[T]]].iterator.filter { c =>
						val parameterTypes = c.getParameterTypes
						parameterTypes.length == length &&
							(parameterTypes.iterator.zip(args.iterator).forall {
								case (found, required) =>
									found.isInstance(required) || BoxedType(found).isInstance(required) ||
										(required == null && !found.isPrimitive)
							})
					}
				if (candidates.hasNext) {
					val cstrtr = candidates.next()
					if (candidates.hasNext) error("multiple matching constructors")
					else cstrtr
				} else null
			}

		if (constructor == null) error("no matching constructor")
		else constructor
	}

	def findMethod[T](clazz: Class[T], methodName : String, args: Any*): Method = {
		def error(msg: String): Nothing = {
			val argClasses = args.map(safeGetClass).mkString(", ")
			throw new IllegalArgumentException(s"$msg found on $clazz with name $methodName for arguments [$argClasses]")
		}

		val method : Method =
			if (args.isEmpty) Try { clazz.getMethod(methodName) }.getOrElse(null)
			else {
				val length = args.length
				val candidates =
					clazz.getMethods.iterator.filter { mthd =>
						val parameterTypes = mthd.getParameterTypes
						mthd.getName == methodName &&
						parameterTypes.length == length &&
							(parameterTypes.iterator.zip(args.iterator).forall {
								case (found, required) =>
									found.isInstance(required) || BoxedType(found).isInstance(required) ||
										(required == null && !found.isPrimitive)
							})
					}
				if (candidates.hasNext) {
					val mthdResult = candidates.next()
					if (candidates.hasNext) error("multiple matching methods")
					else mthdResult
				} else null
			}

		if (method == null) error("no matching method")
		else method
	}

	private def safeGetClass(a: Any): Class[_] =
		if (a == null) classOf[AnyRef] else a.getClass

}
