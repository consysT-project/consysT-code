package de.tuda.stg.consys.checker

import de.tuda.stg.consys.checker.TypeFactoryUtils.{getExplicitConsistencyAnnotation, getMixedDefaultOp, getQualifiedName, immutableAnnotation, inconsistentAnnotation, localAnnotation, mutableAnnotation}
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

	override def visitDeclared(declaredType: AnnotatedDeclaredType, p: Void): Void = {
		val r = super.visitDeclared(declaredType, p)

		val annotation = declaredType.getAnnotationInHierarchy(inconsistentAnnotation)
		if (annotation == null)
			return r

		if (!AnnotationUtils.areSame(annotation, localAnnotation)) {
			// visit class under given consistency to check compatibility, skip for bottom type
			val classElement = TypesUtils.getTypeElement(declaredType.getUnderlyingType)
			tf.getVisitor.visitOrQueueClassTree(classElement, annotation)
		}

		/*
		if (tf.areSameByClass(annotation, classOf[Mixed])) {
			// run inference on mixed types in case we need the field types
			tf.pushVisitClassContext(classElement, annotation)
			if (classTree != null) {
				// TODO: javac dumps processed classes -> no classTree
				tf.inferenceVisitor.processClass(classTree, annotation)
			} else {
				tf.inferenceVisitor.processClass(classElement, annotation)
			}
			tf.popVisitClassContext()
		}
		 */

		r
	}
}
