package de.tuda.stg.consys.core.store.akka

import java.lang.reflect.Modifier

import de.tuda.stg.consys.core.store.akka.Requests.Request
import de.tuda.stg.consys.core.store.utils.Reflect
import de.tuda.stg.consys.core.store.{ConsistencyLevel, Handler}

import scala.reflect.ClassTag

/**
 * Created on 25.02.20.
 *
 * @author Mirko Köhler
 */
private[akka] abstract class AkkaObject[T <: java.io.Serializable : ClassTag] extends Handler[AkkaStore, T] {

	def addr : AkkaStore#Addr
	def state : T
	def consistencyLevel : AkkaStore#Level


	def sync() : Unit


	/**
	 * Handles a request possibly from another replica system.
	 * This method can be called concurrently.
	 *
	 * @param request The request to be handled
	 *
	 * @return The return value of the request.
	 */
	private[akka] def handleRequest[R](request : Request[R]) : R = {
		throw new IllegalArgumentException(s"can not handle request $request")
	}

	override def invoke[R](methodId : String, args : Seq[Seq[Any]]) : R = {
		ReflectiveAccess.doInvoke[R](methodId, args)
	}

	override def getField[R](fieldName : String) : R = {
		ReflectiveAccess.doGetField[R](fieldName)
	}

	override def setField[R](fieldName : String, value : R) : Unit = {
		ReflectiveAccess.doSetField(fieldName, value)
	}



	final def syncAll() : Unit = {
		def syncObject(obj : Any, alreadySynced : Set[Any]) : Unit = {
			//TODO:Change contains so that it uses eq?
			if (obj == null || alreadySynced.contains(obj)) {
				return
			}

			obj match {
				case rob : AkkaObject[_] =>
					rob.sync()
					syncObject(state, alreadySynced + rob)

				case ref : AkkaRef[_] =>
					val rob = ref.resolve()
					syncObject(rob, alreadySynced + ref)

				case _ =>

					val anyClass = obj.getClass
					//If the value is primitive (e.g. int) then stop
					if (anyClass.isPrimitive) {
						return
					}

					//If the value is an array, then initialize ever element of the array.
					if (anyClass.isArray) {
						val anyArray : Array[_] = obj.asInstanceOf[Array[_]]
						val initSet = alreadySynced + obj
						anyArray.foreach(e => syncObject(e, initSet))
					}


					val anyPackage = anyClass.getPackage
					if (anyPackage == null) {
						return
					}

					//If the object should be initialized, then initialize all fields
					anyClass.getDeclaredFields.foreach { field =>
						if ((field.getModifiers & Modifier.STATIC) == 0) { //If field is not static
							//Recursively initialize refs in the fields
							field.setAccessible(true)
							val fieldObj = field.get(obj)
							syncObject(fieldObj, alreadySynced + obj)
						}
					}
			}
		}

		syncObject(this, Set.empty)
	}

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

			try {
				method.invoke(state, flattenedArgs.map(e => e.asInstanceOf[AnyRef]) : _*).asInstanceOf[R]
			} catch {
				case e : Exception =>
					println("ex")
					throw e
			}

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

