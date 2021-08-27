package de.tuda.stg.consys.checker

import de.tuda.stg.consys.checker.TypeFactoryUtils.{getExplicitAnnotation, getMixedDefaultOp, immutableAnnotation, inconsistentAnnotation, localAnnotation, mutableAnnotation}
import de.tuda.stg.consys.checker.qual.Mixed
import org.checkerframework.framework.`type`.AnnotatedTypeMirror
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.{AnnotatedDeclaredType, AnnotatedExecutableType}
import org.checkerframework.framework.`type`.typeannotator.TypeAnnotator
import org.checkerframework.javacutil.{AnnotationUtils, TypesUtils}

import javax.lang.model.`type`.{NoType, TypeKind}
import javax.lang.model.element.{AnnotationMirror, ElementKind, Modifier, TypeElement}
import scala.collection.convert.ImplicitConversions.`collection AsScalaIterable`

/**
	* Created on 23.07.19.
	*
	* @author Mirko Köhler
	*/
class ConsistencyTypeAnnotator(implicit tf : ConsistencyAnnotatedTypeFactory) extends TypeAnnotator(tf) {
	var currentMethod: AnnotatedExecutableType = null

	/*override def visitExecutable(method: AnnotatedExecutableType, aVoid: Void): Void = {
		if (method.getElement.getKind != ElementKind.METHOD)
			return null

		if (currentMethod == method) {
			return null
		}
		val prevMethod = currentMethod
		currentMethod = method

		super.visitExecutable(method, aVoid)

		// TODO: problem: receiverType is declaring class, not instance -> we cant get instance annotation here
		//       keep this here for method declarations and use visitclasscontext -> for compatibility check
		//       put similar code in treeannotator for methodinvocation trees and use instance annotation
		val recvType = method.getReceiverType
		val returnType = method.getReturnType

		if (recvType == null || method.getElement.getModifiers.contains(Modifier.ABSTRACT))
			return null
		if (returnType.getUnderlyingType.getKind != TypeKind.VOID) {
			val annotation = recvType.getAnnotationInHierarchy(inconsistentAnnotation)
			if (annotation != null) {
				tf.returnTypeVisitor.inferenceTable.get(recvType.getUnderlyingType.asElement().asInstanceOf[TypeElement], annotation) match {
					case Some(value) => value.get(method.getElement) match {
						case Some(value) => returnType.replaceAnnotation(value)
						case None => //tf.getChecker.reportWarning(method.getElement, "invocation") // TODO
					}
					case None => // method is from bytecode, so we cannot infer anything
				}

			}
		}


		/*
		// currently only run on mixed classe
		val mixed = if (recvType != null) recvType.getAnnotation(classOf[Mixed]) else null
		val methodTree = tf.getTreeUtils.getTree(method.getElement)s
		if (mixed != null && getExplicitAnnotation(returnType).isEmpty && !returnType.getUnderlyingType.isInstanceOf[NoType]
			&& methodTree != null && !methodTree.getModifiers.getFlags.contains(Modifier.ABSTRACT)) {

			val defaultOpLevel = if (mixed != null)
				AnnotationUtils.getElementValuesWithDefaults(mixed).values().head.getValue.toString else ""
			tf.pushMixedClassContext(recvType.getUnderlyingType.asElement().asInstanceOf[TypeElement], defaultOpLevel)

			val visitor = new ReturnTypeVisitor(tf)
			val lup = visitor.visitMethod(methodTree)
			method.getReturnType.replaceAnnotation(lup)

			tf.popMixedClassContext()
		}*/

		currentMethod = prevMethod
		aVoid
	}*/

	override def visitDeclared(declaredType: AnnotatedDeclaredType, p: Void): Void = {
		val r = super.visitDeclared(declaredType, p)

		val annotation = declaredType.getAnnotationInHierarchy(inconsistentAnnotation)
		if (annotation == null)
			return r

		val classElement = TypesUtils.getTypeElement(declaredType.getUnderlyingType)
		val classTree = tf.getTreeUtils.getTree(classElement)

		if (classTree != null && !AnnotationUtils.areSame(annotation, localAnnotation)) {
			// visit class under given consistency to check compatibility, skip for bottom type
			tf.getVisitor.visitOrQueueClassTree(classTree, annotation)
		}

		if (tf.areSameByClass(annotation, classOf[Mixed])) {
			// run inference on mixed types in case we need the field types
			val defaultOpLevel = getMixedDefaultOp(annotation)
			tf.pushVisitClassContext(classElement, annotation)
			if (classTree != null) {
				tf.inferenceVisitor.processClass(classTree, annotation)
			} else {
				tf.inferenceVisitor.processClass(classElement, annotation)
			}
			tf.popVisitClassContext()
		}

		r
	}
}
