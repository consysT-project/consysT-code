package de.tuda.stg.consys.checker

import com.sun.source.tree.ClassTree

import javax.lang.model.element.{AnnotationMirror, Element}
import org.checkerframework.framework.`type`.{AnnotatedTypeFactory, AnnotatedTypeMirror}
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.AnnotatedDeclaredType
import org.checkerframework.javacutil.{AnnotationUtils, TreeUtils, TypesUtils}

import javax.lang.model.`type`.DeclaredType

/**
	* Created on 06.03.19.
	*
	* @author Mirko Köhler
	*/
object TypeFactoryUtils {
	/*
		Annotation definitions
	 */
	def localAnnotation(implicit atypeFactory : AnnotatedTypeFactory) : AnnotationMirror =
		AnnotationUtils.getAnnotationByName(atypeFactory.getQualifierHierarchy.getBottomAnnotations,"de.tuda.stg.consys.checker.qual.Local")

	def inconsistentAnnotation(implicit atypeFactory : AnnotatedTypeFactory) : AnnotationMirror =
		AnnotationUtils.getAnnotationByName(atypeFactory.getQualifierHierarchy.getTopAnnotations, "de.tuda.stg.consys.checker.qual.Inconsistent")

	val checkerPackageName = s"de.tuda.stg.consys.checker"
	val japiPackageName = s"de.tuda.stg.consys.japi"
	val annoPackageName = s"de.tuda.stg.consys.annotations"

	def getQualifiedName(adt: AnnotatedDeclaredType): String = TypesUtils.getQualifiedName(adt.getUnderlyingType).toString
	def getQualifiedName(dt: DeclaredType): String = TypesUtils.getQualifiedName(dt).toString
	def getQualifiedName(ct: ClassTree): String = TreeUtils.elementFromDeclaration(ct).getQualifiedName.toString

	def getDefaultOp(annotation: AnnotationMirror): String =
		AnnotationUtils.getElementValue(annotation, "withDefault", classOf[Object], true).toString

	def getExplicitAnnotation(implicit atypeFactory : AnnotatedTypeFactory, atype: AnnotatedTypeMirror): Option[AnnotationMirror] =
		Some(atype.getAnnotationInHierarchy(inconsistentAnnotation)).filter(atype.hasExplicitAnnotation)

	def getExplicitAnnotation(implicit atypeFactory : AnnotatedTypeFactory, elt: Element): Option[AnnotationMirror] =
		getExplicitAnnotation(atypeFactory, atypeFactory.getAnnotatedType(elt))
}
