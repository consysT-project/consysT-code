package de.tuda.stg.consys.checker

import de.tuda.stg.consys.checker.TypeFactoryUtils.getExplicitAnnotation
import de.tuda.stg.consys.checker.qual.Mixed
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.AnnotatedExecutableType
import org.checkerframework.framework.`type`.typeannotator.TypeAnnotator
import org.checkerframework.javacutil.AnnotationUtils

import javax.lang.model.`type`.NoType
import javax.lang.model.element.TypeElement
import scala.collection.convert.ImplicitConversions.`collection AsScalaIterable`

/**
	* Created on 23.07.19.
	*
	* @author Mirko Köhler
	*/
class ConsistencyTypeAnnotator(tf : ConsistencyAnnotatedTypeFactory) extends TypeAnnotator(tf) {
	var currentMethod: AnnotatedExecutableType = null

	override def visitExecutable(method: AnnotatedExecutableType, aVoid: Void): Void = {
		if (currentMethod == method) {
			return null
		}
		val prevMethod = currentMethod
		currentMethod = method

		super.visitExecutable(method, aVoid)

		val recvType = method.getReceiverType
		val returnType = method.getReturnType
		val mixed = if (recvType != null) recvType.getAnnotation(classOf[Mixed]) else null

		if (mixed != null && getExplicitAnnotation(tf, returnType).isEmpty && !returnType.getUnderlyingType.isInstanceOf[NoType]) {
			val defaultOpLevel = if (mixed != null)
				AnnotationUtils.getElementValuesWithDefaults(mixed).values().head.getValue.toString else ""
			tf.setMixedClassContext(recvType.getUnderlyingType.asElement().asInstanceOf[TypeElement], defaultOpLevel)

			val visitor = new ReturnTypeVisitor(tf)
			val lup = visitor.visitMethod(tf.getTreeUtils.getTree(method.getElement))
			method.getReturnType.replaceAnnotation(lup)

			tf.resetMixedClassContext()
		}

		currentMethod = prevMethod
		aVoid
	}
}
