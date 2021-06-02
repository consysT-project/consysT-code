package de.tuda.stg.consys.checker

import de.tuda.stg.consys.checker.TypeFactoryUtils.{getExplicitAnnotation, inconsistentAnnotation}
import de.tuda.stg.consys.checker.qual.Mixed
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.AnnotatedExecutableType
import org.checkerframework.framework.`type`.{AnnotatedTypeFactory, AnnotatedTypeMirror}
import org.checkerframework.framework.`type`.typeannotator.TypeAnnotator
import org.checkerframework.javacutil.{ElementUtils, TreeUtils}

import javax.lang.model.`type`.NoType

/**
	* Created on 23.07.19.
	*
	* @author Mirko Köhler
	*/
class ConsistencyTypeAnnotator(tf : AnnotatedTypeFactory) extends TypeAnnotator(tf) {
	var currentMethod: AnnotatedExecutableType = null

	override def visitExecutable(method: AnnotatedExecutableType, aVoid: Void): Void = {
		if (currentMethod == method) {
			return null
		}
		val prevMethod = currentMethod
		currentMethod = method

		super.visitExecutable(method, aVoid)

		if (tf.getAnnotatedType(method.getElement.getEnclosingElement).hasAnnotation(classOf[Mixed])
			&& !method.getReturnType.hasExplicitAnnotation(method.getReturnType.getAnnotationInHierarchy(inconsistentAnnotation(tf)))
			&& !method.getElement.getReturnType.isInstanceOf[NoType]) {

			val visitor = new ReturnTypeVisitor(tf)
			val lup = visitor.visitMethod(tf.getTreeUtils.getTree(method.getElement))
			method.getReturnType.replaceAnnotation(lup)
		}

		currentMethod = prevMethod
		aVoid
	}
}
