package de.tuda.stg.consys.core.store.cassandra

import de.tuda.stg.consys.core.store.utils.Reflect
import de.tuda.stg.consys.core.store.{StoreConsistencyLevel, StoredObject}
import jdk.dynalink.linker.support.TypeUtilities

import scala.reflect.ClassTag
import scala.reflect.runtime.universe._


/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
private[cassandra] abstract class CassandraObject[T <: java.io.Serializable : ClassTag] extends StoredObject[CassandraStore, T] {

	def addr : CassandraStore#Addr
	def state : T
	def consistencyLevel : CassandraStore#Level

	override def invoke[R](methodId : String, args : Seq[Seq[Any]]) : R = {
		ReflectiveAccess.doInvoke[R](methodId, args)
	}

	override def getField[R](fieldName : String) : R = {
		ReflectiveAccess.doGetField[R](fieldName)
	}

	override def setField[R](fieldName : String, value : R) : Unit = {
		ReflectiveAccess.doSetField(fieldName, value)
	}


	protected[cassandra] def writeToStore(store : CassandraStore) : Unit

	//This method is called for every object that was part of a transaction.
	//It has to be used to write changes back to Cassandra and to release all locks.
//	def commit() : Unit

	/**
	 * This private object encapsulates the reflective access to the stored state.
	 */
	private final object ReflectiveAccess {
//		private val rtMirror = runtimeMirror(state.getClass.getClassLoader)
//		private val objMirror : InstanceMirror = rtMirror.reflect(state)

		def doInvoke[R](methodName : String, args : Seq[Seq[Any]]) : R = ReflectiveAccess.synchronized {

			//Arguments from multiple parameter lists are flattened in classes
			val flattenedArgs = args.flatten

			val clazz = implicitly[ClassTag[T]]
			val method = Reflect.findMethod[T](clazz.runtimeClass.asInstanceOf[Class[T]], methodName, flattenedArgs : _*) // clazz.runtimeClass.getMethod(methodName, flattenedArgs.map(e => e.getClass): _*)

			method.invoke(state, flattenedArgs.map(e => e.asInstanceOf[AnyRef]) : _*).asInstanceOf[R]



//			val mthdTerm = TermName(methodName)
//			val argClasses : Seq[Seq[Class[_]]] = args.map(argList => argList.map(arg => arg.getClass))
//			val mbMethodSym : Option[Symbol] = typeOf[T].member(mthdTerm).asTerm.alternatives.find { s =>
//				val flattenedParams : Seq[Seq[Class[_]]] =
//					s.asMethod.paramLists.map(paramList => paramList.map(param => {
//						val classSymbol = param.typeSignature.typeSymbol.asClass
//						rtMirror.runtimeClass(classSymbol)
//					} ))
//
//				//Check whether parameters can be assigned the given arguments
//				flattenedParams.length == argClasses.length && flattenedParams.zip(argClasses).forall(t1 => {
//					val (paramList, argList) = t1
//					paramList.length == argList.length && paramList.zip(argList).forall(t2 => {
//						val (param, arg) = t2
//						val result = if (param.isPrimitive) {
//							//Treat boxed types correctly: primitive types are converted to boxed types and then checked.
//							TypeUtilities.getWrapperType(param).isAssignableFrom(arg)
//						} else {
//							param.isAssignableFrom(arg)
//						}
//						result
//					})
//				})
//				//				flattenedParams == argClasses
//			}
//
//			mbMethodSym match {
//				case Some(methodSymbol: MethodSymbol) =>
//					val methodMirror = objMirror.reflectMethod(methodSymbol)
//					val result = methodMirror.apply(args.flatten : _*)
//					result.asInstanceOf[R]
//				case _ =>
//					throw new NoSuchMethodException(s"method <$methodName> with arguments $args was not found in $objMirror.")
//			}
		}

		def doGetField[R](fieldName : String) : R = ReflectiveAccess.synchronized {
			val clazz = implicitly[ClassTag[T]]
			clazz.runtimeClass.getField(fieldName).get(state).asInstanceOf[R]

//			val tpe = typeOf[T]
//			val fldTerm = TermName(fieldName)
//
//			val fieldSymbol = tpe.member(fldTerm).asTerm
//			val fieldMirror = objMirror.reflectField(fieldSymbol)
//			val result = fieldMirror.get
//			result.asInstanceOf[R]
		}

		def doSetField(fieldName : String, value : Any) : Unit = ReflectiveAccess.synchronized {
			val clazz = implicitly[ClassTag[T]]
			clazz.runtimeClass.getField(fieldName).set(state, value.asInstanceOf[AnyRef])

//			val fieldSymbol = typeOf[T].member(TermName(fieldName)).asTerm
//			val fieldMirror = objMirror.reflectField(fieldSymbol)
//			fieldMirror.set(value)
		}
	}



}
