package de.tuda.stg.consys.core.legacy

import jdk.dynalink.linker.support.TypeUtilities
import scala.reflect.ClassTag
import scala.reflect.runtime.universe._

/**
 * Created on 06.12.19.
 *
 * @author Mirko Köhler
 */
trait ReflectiveReplicatedObject[Addr, T] extends ReplicatedObject[Addr, T] {
	protected implicit def ttt : TypeTag[T]

	protected def setObject(obj : T) : Unit = {
		ReflectiveAccess.setObject(obj)
	}

	protected[core] def getObject : T = {
		ReflectiveAccess.getObject
	}


	override def invoke[R](methodName : String, args : Seq[Seq[Any]]) : R =
		ReflectiveAccess.doInvoke[R](methodName, args)


	override def getField[R](fieldName : String) : R =
		ReflectiveAccess.doGetField(fieldName)


	override def setField[R](fieldName : String, value : R) : Unit =
		ReflectiveAccess.doSetField(fieldName, value)



	private final object ReflectiveAccess {

		private var state : T = _

		private implicit val ct : ClassTag[T]  = ConsysUtils.typeToClassTag[T] //used as implicit argument
		//TODO: Define this as field and keep in sync with obj
		private var objMirror : InstanceMirror = _

		private final val rtMirror = runtimeMirror(ReflectiveReplicatedObject.this.getClass.getClassLoader)

		private[ReflectiveReplicatedObject] def setObject(obj : T) : Unit = {
			state = obj
			objMirror = rtMirror.reflect(state)
		}

		private[ReflectiveReplicatedObject] def getObject : T =
			state

		def doInvoke[R](methodName : String, args : Seq[Seq[Any]]) : R = ReflectiveAccess.synchronized {
			val mthdTerm = TermName(methodName)
			val argClasses : Seq[Seq[Class[_]]] = args.map(argList => argList.map(arg => arg.getClass))
			val mbMethodSym : Option[Symbol] = typeOf[T].member(mthdTerm).asTerm.alternatives.find { s =>
				val flattenedParams : Seq[Seq[Class[_]]] =
					s.asMethod.paramLists.map(paramList => paramList.map(param => {
						val typeSymbol = param.typeSignature.typeSymbol
						val classSymbol = typeSymbol.asClass
						rtMirror.runtimeClass(classSymbol)
					} ))

				//Check whether parameters can be assigned the given arguments
				flattenedParams.length == argClasses.length && flattenedParams.zip(argClasses).forall(t1 => {
					val (paramList, argList) = t1
					paramList.length == argList.length && paramList.zip(argList).forall(t2 => {
						val (param, arg) = t2
						val result = if (param.isPrimitive) {
							//Treat boxed types correctly: primitive types are converted to boxed types and then checked.
							TypeUtilities.getWrapperType(param).isAssignableFrom(arg)
						} else {
							param.isAssignableFrom(arg)
						}
						result
					})
				})
				//				flattenedParams == argClasses
			}

			mbMethodSym match {
				case Some(methodSymbol: MethodSymbol) =>
					val methodMirror = objMirror.reflectMethod(methodSymbol)
					val result = methodMirror.apply(args.flatten : _*)
					result.asInstanceOf[R]
				case _ =>
					throw new NoSuchMethodException(s"method <$methodName> with arguments $args was not found in $objMirror.")
			}
		}

		def doGetField[R](fieldName : String) : R = ReflectiveAccess.synchronized {
			val tpe = typeOf[T]
			val fldTerm = TermName(fieldName)

			val fieldSymbol = tpe.member(fldTerm).asTerm
			val fieldMirror = objMirror.reflectField(fieldSymbol)
			val result = fieldMirror.get
			result.asInstanceOf[R]
		}

		def doSetField(fieldName : String, value : Any) : Unit = ReflectiveAccess.synchronized {
			val fieldSymbol = typeOf[T].member(TermName(fieldName)).asTerm
			val fieldMirror = objMirror.reflectField(fieldSymbol)
			fieldMirror.set(value)
		}
	}

}
