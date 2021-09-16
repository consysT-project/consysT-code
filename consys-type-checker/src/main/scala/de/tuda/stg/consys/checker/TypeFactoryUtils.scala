package de.tuda.stg.consys.checker

import com.sun.source.tree.{AnnotationTree, ClassTree, MemberSelectTree, MethodInvocationTree, ModifiersTree}
import de.tuda.stg.consys.annotations.methods.{StrongOp, WeakOp}
import de.tuda.stg.consys.checker.qual.{Immutable, Mixed, Mutable, MutableBottom, QualifierForOperation, Strong, Weak}

import javax.lang.model.element.{AnnotationMirror, AnnotationValue, Element, ExecutableElement, Modifier, TypeElement}
import org.checkerframework.framework.`type`.{AnnotatedTypeFactory, AnnotatedTypeMirror}
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.AnnotatedDeclaredType
import org.checkerframework.javacutil.{AnnotationBuilder, AnnotationUtils, ElementUtils, TreeUtils, TypesUtils}

import java.lang.annotation.Annotation
import javax.lang.model.`type`.{DeclaredType, NoType, TypeMirror}
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

	// TODO: cache AnnotationMirrors
	def strongAnnotation(implicit atypeFactory : AnnotatedTypeFactory): AnnotationMirror =
		AnnotationBuilder.fromClass(atypeFactory.getElementUtils, classOf[Strong])

	def weakAnnotation(implicit atypeFactory : AnnotatedTypeFactory): AnnotationMirror =
		AnnotationBuilder.fromClass(atypeFactory.getElementUtils, classOf[Weak])

	def mixedAnnotation(defaultOp: Class[_ <: Annotation])(implicit atypeFactory : AnnotatedTypeFactory): AnnotationMirror =
		AnnotationBuilder.fromClass(atypeFactory.getElementUtils, classOf[Mixed],
			AnnotationBuilder.elementNamesValues("value", defaultOp))

	def immutableAnnotation(implicit atypeFactory : AnnotatedTypeFactory) : AnnotationMirror =
		AnnotationBuilder.fromClass(atypeFactory.getElementUtils, classOf[Immutable])

	def mutableAnnotation(implicit atypeFactory : AnnotatedTypeFactory) : AnnotationMirror =
		AnnotationBuilder.fromClass(atypeFactory.getElementUtils, classOf[Mutable])

	def mutableBottomAnnotation(implicit atypeFactory : AnnotatedTypeFactory) : AnnotationMirror =
		AnnotationBuilder.fromClass(atypeFactory.getElementUtils, classOf[MutableBottom])

	private var consistencyQualifiers: Set[AnnotationMirror] = Set.empty
	def getConsistencyQualifiers(implicit tf: AnnotatedTypeFactory): Set[AnnotationMirror] = {
		if (consistencyQualifiers.isEmpty)
			consistencyQualifiers = Set(strongAnnotation, weakAnnotation, mixedAnnotation(classOf[StrongOp]), mixedAnnotation(classOf[WeakOp]))
		consistencyQualifiers
	}


	val checkerPackageName = s"de.tuda.stg.consys.checker"
	val japiPackageName = s"de.tuda.stg.consys.japi"
	val annoPackageName = s"de.tuda.stg.consys.annotations"
	val qualPackageName = s"de.tuda.stg.consys.checker.qual"

	def getQualifiedName(adt: AnnotatedDeclaredType): String = TypesUtils.getQualifiedName(adt.getUnderlyingType).toString
	def getQualifiedName(dt: DeclaredType): String = TypesUtils.getQualifiedName(dt).toString
	def getQualifiedName(ct: ClassTree): String = TreeUtils.elementFromDeclaration(ct).getQualifiedName.toString
	def getQualifiedName(elt: Element): String = ElementUtils.getQualifiedName(elt)
	def getQualifiedName(annotation: AnnotationMirror): String = AnnotationUtils.annotationName(annotation)

	def getExplicitConsistencyAnnotation(aType: AnnotatedTypeMirror)(implicit tf : AnnotatedTypeFactory): Option[AnnotationMirror] = {
		val a = tf.getQualifierHierarchy.findAnnotationInHierarchy(aType.getExplicitAnnotations, inconsistentAnnotation)
		Option(a)
	}

	def getExplicitConsistencyAnnotation(elt: Element)(implicit tf : AnnotatedTypeFactory): Option[AnnotationMirror] =
		getExplicitConsistencyAnnotation(tf.getAnnotatedType(elt))

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

	def isMixedQualifier(qualifier: AnnotationMirror)(implicit tf : AnnotatedTypeFactory): Boolean =
		tf.areSameByClass(qualifier, classOf[Mixed])

	def getNameForMixedDefaultOp(mixedAnnotation: AnnotationMirror)(implicit tf : AnnotatedTypeFactory): String = {
		if (mixedAnnotation.getElementValues.values().isEmpty)
			classOf[WeakOp].getCanonicalName
		else
			mixedAnnotation.getElementValues.values().head.getValue match {
				case v: DeclaredType => getQualifiedName(v)
				case v: Class[_] => v.getCanonicalName
				case _ => sys.error("consyst checker bug")
			}
	}

	def getQualifierForMixedDefaultOp(mixedAnnotation: AnnotationMirror)(implicit tf : AnnotatedTypeFactory): AnnotationMirror = {
		val operationLevel = getNameForMixedDefaultOp(mixedAnnotation)
		getQualifierNameForOp(operationLevel) match {
			case Some(qualifier) =>
				AnnotationBuilder.fromName(tf.getElementUtils, qualifier)
			case None =>
				sys.error("invalid default operation on mixed") // TODO: handle case where given default operation level is not valid
		}
	}

	def getMixedOpForMethod(method: ExecutableElement, default: String)(implicit atypeFactory: AnnotatedTypeFactory): String = {
		var methodLevel: Option[String] = None
		getQualifierForOpMap.foreach(mapping => {
			val (operation, _) = mapping
			if (ElementUtils.hasAnnotation(method, operation)) {
				methodLevel match {
					case None => methodLevel = Option(operation)
					case _ => // TODO: handle case if more than one annotation given
				}
			}
		})

		if (methodLevel.isEmpty) default else methodLevel.get
	}

	def getQualifierForMethodOp(method: ExecutableElement, recvQual: AnnotationMirror)(implicit atypeFactory: AnnotatedTypeFactory): Option[AnnotationMirror] =
		getQualifierForOp(getMixedOpForMethod(method, getNameForMixedDefaultOp(recvQual)))

	def repairMixed(annotation: AnnotationMirror)(implicit tf : AnnotatedTypeFactory): AnnotationMirror = {
		if (tf.areSameByClass(annotation, classOf[Mixed]) && annotation.getElementValues.isEmpty)
			mixedAnnotation(classOf[WeakOp])
		else annotation
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

	def isPrivateOrProtected(elt: Element): Boolean =
		elt.getModifiers.contains(Modifier.PRIVATE) || elt.getModifiers.contains(Modifier.PROTECTED)

	def methodInvocationIsAny(node: MethodInvocationTree, receiverName: String, methodNames: List[String]) : Boolean = {
		def checkMethodName(memberSelectTree: MemberSelectTree): Boolean = {
			val methodId = memberSelectTree.getIdentifier.toString
			methodNames.map(x => x == methodId).fold(false)(_ || _)
		}
		def checkReceiverNameInInterfaces(dt: DeclaredType, mst: MemberSelectTree): Boolean = dt.asElement() match {
			case te: TypeElement => te.getInterfaces.exists {
				case interfaceType: DeclaredType if getQualifiedName(interfaceType) == receiverName =>
					checkMethodName(mst)
				case interfaceType: DeclaredType =>
					checkReceiverNameInInterfaces(interfaceType, mst)
				case _ => false
			}
			case _ => false
		}
		def checkReceiverNameInSuperClass(dt: DeclaredType, mst: MemberSelectTree): Boolean = dt.asElement() match {
			case te: TypeElement => te.getSuperclass match {
				case _: NoType => false
				case dt: DeclaredType if getQualifiedName(dt) == receiverName =>
					checkMethodName(mst)
				case dt: DeclaredType =>
					checkReceiverNameInInterfaces(dt, mst) || checkReceiverNameInSuperClass(dt, mst)
				case _ => false
			}
			case _ => false
		}

		node.getMethodSelect match {
			case memberSelectTree : MemberSelectTree =>
				val receiverElement = TreeUtils.elementFromUse(memberSelectTree.getExpression)
				receiverElement.asType() match {
					// check for a direct name match
					case dt: DeclaredType if getQualifiedName(dt) == receiverName =>
						checkMethodName(memberSelectTree)
					// check for name match in interfaces or superclass
					case dt: DeclaredType =>
						checkReceiverNameInInterfaces(dt, memberSelectTree) ||
							checkReceiverNameInSuperClass(dt, memberSelectTree)
					case _ => false
				}
			case _ => false
		}
	}

	def isRefDereference(node: MethodInvocationTree): Boolean =
		methodInvocationIsAny(node, s"$japiPackageName.Ref", List("ref"))

	def isAnyRefAccess(node: MethodInvocationTree): Boolean =
		methodInvocationIsAny(node, s"$japiPackageName.Ref", List("ref", "getField", "setField", "invoke"))

	def isReplicateOrLookup(node: MethodInvocationTree): Boolean =
		methodInvocationIsAny(node, s"$japiPackageName.TransactionContext", List("replicate", "lookup"))

	def isTransaction(node: MethodInvocationTree): Boolean =
		methodInvocationIsAny(node, s"$japiPackageName.Store", List("transaction"))
}
