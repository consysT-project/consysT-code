package de.tuda.stg.consys.checker

import com.sun.source.tree.{AnnotationTree, ClassTree, ModifiersTree}
import de.tuda.stg.consys.checker.qual.{Mutable, MutableBottom, QualifierForOperation}

import javax.lang.model.element.{AnnotationMirror, Element, ExecutableElement}
import org.checkerframework.framework.`type`.{AnnotatedTypeFactory, AnnotatedTypeMirror}
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.AnnotatedDeclaredType
import org.checkerframework.javacutil.{AnnotationBuilder, AnnotationUtils, ElementUtils, TreeUtils, TypesUtils}

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

	def immutableAnnotation(implicit atypeFactory : AnnotatedTypeFactory) : AnnotationMirror =
		AnnotationUtils.getAnnotationByName(atypeFactory.getQualifierHierarchy.getTopAnnotations, "de.tuda.stg.consys.checker.qual.Immutable")

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

	def getExplicitAnnotation(implicit atypeFactory : AnnotatedTypeFactory, atype: AnnotatedTypeMirror): Option[AnnotationMirror] =
		Some(atype.getAnnotationInHierarchy(inconsistentAnnotation)).filter(atype.hasExplicitAnnotation)

	def getExplicitAnnotation(elt: Element)(implicit atypeFactory : AnnotatedTypeFactory): Option[AnnotationMirror] =
		getExplicitAnnotation(atypeFactory, atypeFactory.getAnnotatedType(elt))

	def hasAnnotation(implicit atypeFactory : AnnotatedTypeFactory, modifiers: ModifiersTree, annotation: String): Boolean = {
		modifiers.getAnnotations.exists((at: AnnotationTree) => atypeFactory.getAnnotatedType(at.getAnnotationType) match {
			case adt: AnnotatedDeclaredType =>
				getQualifiedName(adt) == annotation
			case _ =>
				false
		})
	}

	def getMixedDefaultOp(mixedAnnotation: AnnotationMirror): String =
		AnnotationUtils.getElementValue(mixedAnnotation, "withDefault", classOf[Object], true).toString

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
