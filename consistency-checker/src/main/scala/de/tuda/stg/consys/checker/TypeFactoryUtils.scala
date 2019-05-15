package de.tuda.stg.consys.checker

import javax.lang.model.element.AnnotationMirror
import org.checkerframework.framework.`type`.AnnotatedTypeFactory
import org.checkerframework.javacutil.AnnotationUtils

/**
	* Created on 06.03.19.
	*
	* @author Mirko Köhler
	*/
object TypeFactoryUtils {
	/*
		Annotation definitions
	 */
	@inline def localAnnotation(implicit atypeFactory : AnnotatedTypeFactory) : AnnotationMirror =
		AnnotationUtils.getAnnotationByName(atypeFactory.getQualifierHierarchy.getBottomAnnotations, "de.tudarmstadt.consistency.checker.qual.Local")

	@inline def inconsistentAnnotation(implicit atypeFactory : AnnotatedTypeFactory) : AnnotationMirror =
		AnnotationUtils.getAnnotationByName(atypeFactory.getQualifierHierarchy.getTopAnnotations, "de.tudarmstadt.consistency.checker.qual.Inconsistent")

}
