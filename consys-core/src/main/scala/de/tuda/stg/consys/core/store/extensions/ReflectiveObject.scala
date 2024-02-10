package de.tuda.stg.consys.core.store.extensions

import de.tuda.stg.consys.core.store.utils.Reflect

import java.lang.reflect.{Field, InvocationTargetException}
import scala.reflect.ClassTag

abstract class ReflectiveObject[Addr, T : ClassTag] {

	def addr : Addr
	def state : T

	@inline def getClassTag : ClassTag[T] = implicitly[ClassTag[T]]

	def invoke[R](methodId : String, args : Seq[Seq[Any]]) : R = {
		ReflectiveAccess.doInvoke[R](methodId, args)
	}

	def getField[R](fieldName : String) : R = {
		ReflectiveAccess.doGetField[R](fieldName)
	}

	def setField[R](fieldName : String, value : R) : Unit = {
		ReflectiveAccess.doSetField(fieldName, value)
	}


	/**
	 * This private object encapsulates the reflective access to the stored state.
	 */
	private case object ReflectiveAccess {
		def doInvoke[R](methodName : String, args : Seq[Seq[Any]]) : R = ReflectiveAccess.synchronized {
			//Arguments from multiple parameter lists are flattened in classes
			val flattenedArgs = args.flatten

			val clazz = state.getClass
			val method = Reflect.getMethod[T](clazz.asInstanceOf[Class[T]], methodName, flattenedArgs : _*) // clazz.runtimeClass.getMethod(methodName, flattenedArgs.map(e => e.getClass): _*)

			try {
				method.invoke(state, flattenedArgs.map(e => e.asInstanceOf[AnyRef]) : _*).asInstanceOf[R]
			} catch {
				case e: InvocationTargetException => if (e.getCause.isInstanceOf[Exception]) throw e.getCause else throw e
			}
		}

		def doGetField[R](fieldName : String) : R = ReflectiveAccess.synchronized {
			val clazz = state.getClass

			// TODO: find cleaner solution
			val field = clazz.getDeclaredField(fieldName)
			field.setAccessible(true)
			field.get(state).asInstanceOf[R]

			//clazz.getField(fieldName).get(state).asInstanceOf[R]
		}

		def doSetField(fieldName : String, value : Any) : Unit = ReflectiveAccess.synchronized {
			val clazz = state.getClass

			// TODO: find cleaner solution
			val field = clazz.getDeclaredField(fieldName)
			field.setAccessible(true)
			field.set(state, value.asInstanceOf[AnyRef])

			//clazz.getField(fieldName).set(state, value.asInstanceOf[AnyRef])
		}
	}



}
