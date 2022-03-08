package de.tuda.stg.consys.core.store.extensions

import de.tuda.stg.consys.core.store.utils.Reflect
import java.lang.reflect.Field
import scala.reflect.ClassTag

abstract class ReflectiveObject[Addr, T : ClassTag] {

	def addr : Addr
	def state : T

	lazy val getClassTag : ClassTag[T] = implicitly[ClassTag[T]]

	lazy val getFields : Iterable[Field] = Reflect.getFields(getClassTag.runtimeClass)

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
	private final object ReflectiveAccess {

		def doInvoke[R](methodName : String, args : Seq[Seq[Any]]) : R = ReflectiveAccess.synchronized {
			//Arguments from multiple parameter lists are flattened in classes
			val flattenedArgs = args.flatten

			val clazz = implicitly[ClassTag[T]]
			val method = Reflect.getMethod[T](clazz.runtimeClass.asInstanceOf[Class[T]], methodName, flattenedArgs : _*) // clazz.runtimeClass.getMethod(methodName, flattenedArgs.map(e => e.getClass): _*)

			method.invoke(state, flattenedArgs.map(e => e.asInstanceOf[AnyRef]) : _*).asInstanceOf[R]


		}

		def doGetField[R](fieldName : String) : R = ReflectiveAccess.synchronized {
			val clazz = implicitly[ClassTag[T]]
			clazz.runtimeClass.getField(fieldName).get(state).asInstanceOf[R]
		}

		def doSetField(fieldName : String, value : Any) : Unit = ReflectiveAccess.synchronized {
			val clazz = implicitly[ClassTag[T]]
			clazz.runtimeClass.getField(fieldName).set(state, value.asInstanceOf[AnyRef])
		}
	}



}
