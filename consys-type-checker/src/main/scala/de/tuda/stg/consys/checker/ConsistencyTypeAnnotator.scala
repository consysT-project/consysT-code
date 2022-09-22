package de.tuda.stg.consys.checker

import org.checkerframework.framework.`type`.AnnotatedTypeMirror.{AnnotatedDeclaredType, AnnotatedExecutableType}
import org.checkerframework.framework.`type`.typeannotator.TypeAnnotator
import org.checkerframework.javacutil.{AnnotationUtils, TypesUtils}

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
		tf.replaceThisConsistent(method)
		r
	}
}
