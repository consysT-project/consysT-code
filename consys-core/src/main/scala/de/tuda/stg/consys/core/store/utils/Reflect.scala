package de.tuda.stg.consys.core.store.utils

import akka.util.BoxedType
import java.lang.reflect.{Constructor, Method}
import scala.util.Try

/**
 * Utility methods for reflection.
 */
object Reflect {

	/**
	 * Returns the constructor for a given class that takes the specified arguments as
	 * parameters.
	 *
	 * @param clazz The class for which to return the constructor.
	 * @param args The arguments that are passed to the constructor.
	 * @tparam T The type of the class.
	 * @return A constructor of ´clazz´ that can be applied to the given arguments.
	 */
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

	/**
	 * Returns a method for a given class with the given name
	 * that takes the specified arguments as parameters.
	 * The method is also searched in superclasses of the specified class.
	 *
	 * @param clazz The class in which the method is defined.
	 * @param methodName The name of the method.
	 * @param args The arguments that are passed to the method.
	 * @tparam T The type of the class.
	 * @return The method of ´clazz´ with the given name that can be applied to the given arguments.
	 */
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
		if (a == null) classOf[Null] else a.getClass

}
