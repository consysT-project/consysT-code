package de.tuda.stg.consys.core.store.cassandra.levels

import de.tuda.stg.consys.annotations.MethodWriteList
import de.tuda.stg.consys.core.store.utils.Reflect
import java.lang.reflect.Field
import org.checkerframework.dataflow.qual.SideEffectFree
import scala.reflect.ClassTag

object Utils {

	def hasSideEffects[T : ClassTag](methodId : String, args : Seq[Seq[Any]]) : Boolean = {
		val t = getMethodSideEffects(methodId, args)
		t._1 || t._2.nonEmpty
	}

	def getMethodSideEffects[T : ClassTag](methodId : String, args : Seq[Seq[Any]]) : (
		Boolean /* true, if the whole object is changed */, Iterable[Field] /* a list of fields that are changed by the method */
		) = {

		val flattenedArgs = args.flatten
		val clazz = implicitly[ClassTag[T]]
		val method = Reflect.getMethod[T](clazz.runtimeClass.asInstanceOf[Class[T]], methodId, flattenedArgs : _*)

		// If @SideEffect is present => true
		val writes : Iterable[Field] = {
			val methodWritesAnnotation = method.getAnnotation(classOf[MethodWriteList])
			// If method write is not present => assume that all fields could be written => false
			if (methodWritesAnnotation == null) Reflect.getFields(clazz.runtimeClass)
			// If no fields are written => true
			else methodWritesAnnotation.value().map(name => Reflect.getField(clazz.runtimeClass, name))
		}

		(method.getAnnotation(classOf[SideEffectFree]) != null, writes)
	}

}
