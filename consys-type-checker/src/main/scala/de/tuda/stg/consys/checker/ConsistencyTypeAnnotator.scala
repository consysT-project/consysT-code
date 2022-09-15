package de.tuda.stg.consys.checker

import de.tuda.stg.consys.checker.qual.ThisConsistent
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.{AnnotatedDeclaredType, AnnotatedExecutableType}
import org.checkerframework.framework.`type`.typeannotator.TypeAnnotator
import org.checkerframework.javacutil.{AnnotationUtils, ElementUtils, TypesUtils}

import scala.jdk.CollectionConverters._

/**
	* Created on 23.07.19.
	*
	* @author Mirko Köhler
	*/
class ConsistencyTypeAnnotator(implicit tf : ConsistencyAnnotatedTypeFactory) extends TypeAnnotator(tf) {
	import TypeFactoryUtils._

	override def visitDeclared(declaredType: AnnotatedDeclaredType, aVoid: Void): Void = {
		val r = super.visitDeclared(declaredType, aVoid)

		if (typeIsRef(declaredType.getUnderlyingType)) {
			// visit class under given consistency to check compatibility, skip for bottom type
			val typeElt = declaredType.getTypeArguments.get(0)
			val qualifier = typeElt.getAnnotationInHierarchy(inconsistentAnnotation)
			if (qualifier != null && !AnnotationUtils.areSame(qualifier, localAnnotation)) {
				val classElement = TypesUtils.getTypeElement(typeElt.getUnderlyingType)
				tf.getVisitor.queueClassVisit(classElement, qualifier)
			}
		}

		r
	}

	override def visitExecutable(method: AnnotatedExecutableType, aVoid: Void): Void = {
		val r = super.visitExecutable(method, aVoid)

		// return & parameter type adaptation for @ThisConsistent inside method body context
		tf.getMethodReceiverContext match {
			// check for @ThisAnnotation in underlying type, i.e. without checker-framework processing,
			// to allow repeated modification (for classes with multiple potential consistencies)
			case Some(recvQualifier) =>
				// return type
				if (tf.containsSameByClass(method.getUnderlyingType.getReturnType.getAnnotationMirrors, classOf[ThisConsistent]))
					method.getReturnType.replaceAnnotation(inferTypeFromReceiver(recvQualifier, method.getElement))

				// parameter types
				(method.getUnderlyingType.getParameterTypes.asScala zip method.getParameterTypes.asScala).foreach(e => {
					val (underlying, typ) = e
					if (tf.containsSameByClass(underlying.getAnnotationMirrors, classOf[ThisConsistent]))
						typ.replaceAnnotation(inferTypeFromReceiver(recvQualifier, method.getElement))
				})

			case _ =>
		}

		r
	}
}
