package de.tuda.stg.consys.checker

import com.sun.source.tree.{AnnotationTree, ClassTree, ModifiersTree}
import de.tuda.stg.consys.checker.qual.{Immutable, Mutable, MutableBottom, QualifierForOperation, Strong}

import javax.lang.model.element.{AnnotationMirror, Element, ExecutableElement}
import org.checkerframework.framework.`type`.{AnnotatedTypeFactory, AnnotatedTypeMirror}
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.AnnotatedDeclaredType
import org.checkerframework.javacutil.{AnnotationBuilder, AnnotationUtils, ElementUtils, TreeUtils, TypesUtils}

import java.lang.annotation.Annotation
import javax.lang.model.`type`.DeclaredType
import scala.collection.convert.ImplicitConversions.`collection AsScalaIterable`

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

	def strongAnnotation(implicit atypeFactory : AnnotatedTypeFactory): AnnotationMirror =
		AnnotationBuilder.fromClass(atypeFactory.getElementUtils, classOf[Strong])

	def immutableAnnotation(implicit atypeFactory : AnnotatedTypeFactory) : AnnotationMirror =
		AnnotationBuilder.fromClass(atypeFactory.getElementUtils, classOf[Immutable])

	def mutableAnnotation(implicit atypeFactory : AnnotatedTypeFactory) : AnnotationMirror =
		AnnotationBuilder.fromClass(atypeFactory.getElementUtils, classOf[Mutable])

	def mutableBottomAnnotation(implicit atypeFactory : AnnotatedTypeFactory) : AnnotationMirror =
		AnnotationBuilder.fromClass(atypeFactory.getElementUtils, classOf[MutableBottom])

	val checkerPackageName = s"de.tuda.stg.consys.checker"
	val japiPackageName = s"de.tuda.stg.consys.japi"
	val annoPackageName = s"de.tuda.stg.consys.annotations"
	val qualPackageName = s"de.tuda.stg.consys.checker.qual"

	def getQualifiedName(adt: AnnotatedDeclaredType): String = TypesUtils.getQualifiedName(adt.getUnderlyingType).toString
	def getQualifiedName(dt: DeclaredType): String = TypesUtils.getQualifiedName(dt).toString
	def getQualifiedName(ct: ClassTree): String = TreeUtils.elementFromDeclaration(ct).getQualifiedName.toString
	def getQualifiedName(elt: Element): String = ElementUtils.getQualifiedName(elt)
	def getQualifiedName(annotation: AnnotationMirror): String = AnnotationUtils.annotationName(annotation)

	def getExplicitAnnotation(aType: AnnotatedTypeMirror)(implicit tf : AnnotatedTypeFactory): Option[AnnotationMirror] =
		Some(aType.getAnnotationInHierarchy(inconsistentAnnotation)).filter(a => a != null && aType.hasExplicitAnnotation(a))

	def getExplicitAnnotation(elt: Element)(implicit tf : AnnotatedTypeFactory): Option[AnnotationMirror] =
		getExplicitAnnotation(tf.getAnnotatedType(elt))

	def hasAnnotation(modifiers: ModifiersTree, annotation: String)(implicit tf : AnnotatedTypeFactory): Boolean = {
		modifiers.getAnnotations.exists((at: AnnotationTree) => tf.getAnnotatedType(at.getAnnotationType) match {
			case adt: AnnotatedDeclaredType => getQualifiedName(adt) == annotation
			case _ => false
		})
	}

	def hasAnnotation(modifiers: ModifiersTree, annotation: Class[_ <: Annotation])(implicit tf : AnnotatedTypeFactory): Boolean =
		hasAnnotation(modifiers, annotation.getCanonicalName)

	def hasAnnotation(elt: Element, annotation: Class[_ <: Annotation]): Boolean =
		ElementUtils.hasAnnotation(elt, annotation.getCanonicalName)

	def getMixedDefaultOp(mixedAnnotation: AnnotationMirror): String =
		AnnotationUtils.getElementValue(mixedAnnotation, "value", classOf[Object], true).toString

	def getMixedOpForMethod(method: ExecutableElement, default: String)(implicit atypeFactory: AnnotatedTypeFactory): String = {
		var methodLevel: Option[String] = None
		getQualifierForOpMap.foreach(mapping => {
			val (operation, _) = mapping
			if (ElementUtils.hasAnnotation(method, operation)) {
				methodLevel match {
					case None =>
						methodLevel = Option(operation)
					case _ => // TODO: handle case if more than one annotation given
				}
			}
		})

		if (methodLevel.isEmpty) default else methodLevel.get
	}



	def getQualifierNameForOp(qualifiedName: String)(implicit tf: AnnotatedTypeFactory): Option[String] = {
		if (qualifierForOpMap.isEmpty)
			qualifierForOpMap = Some(buildQualifierMap)
		qualifierForOpMap.get.get(qualifiedName)
	}

	def getQualifierForOp(qualifiedName: String)(implicit tf: AnnotatedTypeFactory): Option[AnnotationMirror] = {
		if (qualifierForOpMap.isEmpty)
			qualifierForOpMap = Some(buildQualifierMap)
		qualifierForOpMap.get.get(qualifiedName) match {
			case Some(value) => Some(AnnotationBuilder.fromName(tf.getElementUtils, value))
			case None => None
		}
	}

	def getQualifierForOpMap(implicit tf: AnnotatedTypeFactory): Map[String, String] = {
		if (qualifierForOpMap.isEmpty)
			qualifierForOpMap = Some(buildQualifierMap)
		qualifierForOpMap.get
	}

	private var qualifierForOpMap: Option[Map[String, String]] = None
	private def buildQualifierMap(implicit atypeFactory: AnnotatedTypeFactory): Map[String, String] =
		atypeFactory.getSupportedTypeQualifiers.
			map(q => atypeFactory.getAnnotatedType(q) match {
				case adt: AnnotatedDeclaredType => adt.getUnderlyingType.asElement
				case _ => null
			}).
			filter(x => x != null).
			foldLeft(Map.empty[String, String])((map, elt) => {
				atypeFactory.getAnnotationByClass(elt.getAnnotationMirrors, classOf[QualifierForOperation]) match {
					case null => map
					case annotation =>
						val value = annotation.getElementValues.values().head
						map + (value.getValue.toString -> elt.toString)
				}
			})
}
