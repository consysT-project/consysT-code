package de.tuda.stg.consys.checker

import com.sun.source.tree._
import de.tuda.stg.consys.annotations.Transactional
import de.tuda.stg.consys.annotations.methods.{StrongOp, WeakOp}
import de.tuda.stg.consys.checker.qual._
import org.checkerframework.dataflow.qual.SideEffectFree
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.AnnotatedDeclaredType
import org.checkerframework.framework.`type`.{AnnotatedTypeFactory, AnnotatedTypeMirror}
import org.checkerframework.javacutil._
import org.jmlspecs.annotation.Pure

import java.lang.annotation.Annotation
import javax.lang.model.`type`.{DeclaredType, NoType}
import javax.lang.model.element._
import scala.annotation.tailrec
import scala.jdk.CollectionConverters._

/**
	* Created on 06.03.19.
	*
	* @author Mirko Köhler
	*/
object TypeFactoryUtils {

	// #################################################################################################################
	// ### Qualifier getters
	// #################################################################################################################

	def localAnnotation(implicit tf : AnnotatedTypeFactory) : AnnotationMirror =
		AnnotationBuilder.fromClass(tf.getElementUtils, classOf[Local])

	def inconsistentAnnotation(implicit tf : AnnotatedTypeFactory) : AnnotationMirror =
		AnnotationBuilder.fromClass(tf.getElementUtils, classOf[Inconsistent])

	def strongAnnotation(implicit tf : AnnotatedTypeFactory): AnnotationMirror =
		AnnotationBuilder.fromClass(tf.getElementUtils, classOf[Strong])

	def weakAnnotation(implicit tf : AnnotatedTypeFactory): AnnotationMirror =
		AnnotationBuilder.fromClass(tf.getElementUtils, classOf[Weak])

	def mixedAnnotation(defaultOp: Class[_ <: Annotation])(implicit tf : AnnotatedTypeFactory): AnnotationMirror =
		AnnotationBuilder.fromClass(tf.getElementUtils, classOf[Mixed],
			AnnotationBuilder.elementNamesValues("value", defaultOp))

	def immutableAnnotation(implicit tf : AnnotatedTypeFactory) : AnnotationMirror =
		AnnotationBuilder.fromClass(tf.getElementUtils, classOf[Immutable])

	def mutableAnnotation(implicit tf : AnnotatedTypeFactory) : AnnotationMirror =
		AnnotationBuilder.fromClass(tf.getElementUtils, classOf[Mutable])

	def mutableBottomAnnotation(implicit tf : AnnotatedTypeFactory) : AnnotationMirror =
		AnnotationBuilder.fromClass(tf.getElementUtils, classOf[MutableBottom])

	private var consistencyQualifiers: Set[AnnotationMirror] = Set.empty
	def getConsistencyQualifiers(implicit tf: AnnotatedTypeFactory): Set[AnnotationMirror] = {
		if (consistencyQualifiers.isEmpty)
			consistencyQualifiers = Set(
				strongAnnotation,
				weakAnnotation,
				mixedAnnotation(classOf[StrongOp]),
				mixedAnnotation(classOf[WeakOp]))
		consistencyQualifiers
	}


	// #################################################################################################################
	// ### Type name helpers
	// #################################################################################################################

	def getQualifiedName(adt: AnnotatedDeclaredType): String = TypesUtils.getQualifiedName(adt.getUnderlyingType)

	def getQualifiedName(dt: DeclaredType): String = TypesUtils.getQualifiedName(dt)

	def getQualifiedName(ct: ClassTree): String = TreeUtils.elementFromDeclaration(ct).getQualifiedName.toString

	def getQualifiedName(elt: Element): String = ElementUtils.getQualifiedName(elt)

	def getQualifiedName(annotation: AnnotationMirror): String = AnnotationUtils.annotationName(annotation)


	// #################################################################################################################
	// ### Annotation helpers
	// #################################################################################################################

	def getExplicitConsistencyAnnotation(aType: AnnotatedTypeMirror)(implicit tf : AnnotatedTypeFactory): Option[AnnotationMirror] = {
		val a = tf.getQualifierHierarchy.findAnnotationInHierarchy(aType.getExplicitAnnotations, inconsistentAnnotation)
		Option(a)
	}

	def getExplicitConsistencyAnnotation(elt: Element)(implicit tf : AnnotatedTypeFactory): Option[AnnotationMirror] =
		getExplicitConsistencyAnnotation(tf.getAnnotatedType(elt))

	def hasAnnotation(modifiers: ModifiersTree, annotation: String)(implicit tf : AnnotatedTypeFactory): Boolean = {
		modifiers.getAnnotations.asScala.exists((at: AnnotationTree) => tf.getAnnotatedType(at.getAnnotationType) match {
			case adt: AnnotatedDeclaredType => getQualifiedName(adt) == annotation
			case _ => false
		})
	}

	def hasAnnotation(modifiers: ModifiersTree, annotation: Class[_ <: Annotation])(implicit tf : AnnotatedTypeFactory): Boolean =
		hasAnnotation(modifiers, annotation.getCanonicalName)

	def hasAnnotation(elt: Element, annotation: Class[_ <: Annotation]): Boolean =
		ElementUtils.hasAnnotation(elt, annotation.getCanonicalName)


	// #################################################################################################################
	// ### @ThisConsistent helpers
	// #################################################################################################################

	/**
	 * Infers a type for substituting @ThisConsistent based on a given method. If the method belongs to a @Mixed
	 * receiver, the inferred type is the type belonging to the method's operation level. Else, the receiver's
	 * type is used.
	 * @param recvQualifier qualifier of the method's receiver
	 * @param method the method from which to infer the type
	 * @return The qualifier for the substitution type
	 */
	def inferThisTypeFromReceiver(recvQualifier: AnnotationMirror, method: ExecutableElement)(implicit tf : AnnotatedTypeFactory): AnnotationMirror = {
		if (isMixedQualifier(recvQualifier))
			getQualifierForOp(getMixedOpForMethod(method, getNameForMixedDefaultOp(recvQualifier))).get
		else
			recvQualifier
	}

	/**
	 * Infers a type for substituting @ThisConsistent based on the method that encloses an element, e.g. parameters or
	 * local variables. If the method belongs to a @Mixed receiver, the inferred type is the type belonging to the
	 * method's operation level. Else, the receiver's type is used.
	 * @param element the element for which to infer the type
	 * @return The qualifier for the substitution type
	 */
	def inferThisTypeFromEnclosingMethod(element: Element)(implicit tf : ConsistencyAnnotatedTypeFactory): AnnotationMirror = {
		val method = element.getEnclosingElement.asInstanceOf[ExecutableElement]
		// for parameters and local variables the receiver w.r.t @ThisConsistent substitution
		// is the currently visited class
		val (_, recvQualifier) = tf.peekVisitClassContext
		inferThisTypeFromReceiver(recvQualifier, method)
	}


	// #################################################################################################################
	// ### @Mixed helpers
	// #################################################################################################################

	def isMixedQualifier(qualifier: AnnotationMirror)(implicit tf : AnnotatedTypeFactory): Boolean =
		tf.areSameByClass(qualifier, classOf[Mixed])

	/**
	 * Returns the qualified name of the default op for a given mixed qualifier
	 */
	def getNameForMixedDefaultOp(mixedAnnotation: AnnotationMirror)(implicit tf : AnnotatedTypeFactory): String = {
		if (mixedAnnotation.getElementValues.values().isEmpty)
			classOf[WeakOp].getCanonicalName
		else
			mixedAnnotation.getElementValues.values().asScala.head.getValue match {
				case v: DeclaredType => getQualifiedName(v)
				case v: Class[_] => v.getCanonicalName
				case _ => sys.error("ConSysT type checker bug: mixed annotation value not found")
			}
	}

	/**
	 * Returns the consistency qualifier for the default op for a given mixed qualifier
	 */
	def getQualifierForMixedDefaultOp(mixedAnnotation: AnnotationMirror)(implicit tf : AnnotatedTypeFactory): AnnotationMirror = {
		val operationLevel = getNameForMixedDefaultOp(mixedAnnotation)
		getQualifierNameForOp(operationLevel) match {
			case Some(qualifier) =>
				AnnotationBuilder.fromName(tf.getElementUtils, qualifier)
			case None =>
				sys.error("ConSysT type checker bug: invalid default operation on mixed")
		}
	}

	/**
	 * Returns the qualified name of the operation level on a given method
	 */
	def getMixedOpForMethod(method: ExecutableElement, default: String)(implicit tf: AnnotatedTypeFactory): String = {
		var methodLevel: Option[String] = None
		getQualifierForOpMap.foreach(mapping => {
			val (operation, _) = mapping
			if (ElementUtils.hasAnnotation(method, operation)) {
				methodLevel match {
					case None => methodLevel = Option(operation)
					case _ => tf.getChecker.reportError(method, "mixed.operation.ambiguous")
				}
			}
		})

		if (methodLevel.isEmpty) default else methodLevel.get
	}

	/**
	 * Returns the consistency qualifier of the operation level on a given method for a given mixed receiver
	 */
	def getQualifierForMethodOp(method: ExecutableElement, recvQual: AnnotationMirror)(implicit tf: AnnotatedTypeFactory): Option[AnnotationMirror] =
		getQualifierForOp(getMixedOpForMethod(method, getNameForMixedDefaultOp(recvQual)))

	/**
	 * Adds missing default op levels to a mixed qualifier (using WeakOp as the default)
	 */
	def repairMixed(annotation: AnnotationMirror)(implicit tf : AnnotatedTypeFactory): AnnotationMirror = {
		if (tf.areSameByClass(annotation, classOf[Mixed]) && annotation.getElementValues.isEmpty)
			mixedAnnotation(classOf[WeakOp])
		else annotation
	}

	/**
	 * Returns the qualified name of the consistency qualifier for a given operation level (passed by qualified name).
	 */
	def getQualifierNameForOp(qualifiedName: String)(implicit tf: AnnotatedTypeFactory): Option[String] = {
		if (qualifierForOpMap.isEmpty)
			qualifierForOpMap = Some(buildQualifierMap)
		qualifierForOpMap.get.get(qualifiedName)
	}

	/**
	 * Returns the consistency qualifier for a given operation level (passed by qualified name).
	 */
	def getQualifierForOp(qualifiedName: String)(implicit tf: AnnotatedTypeFactory): Option[AnnotationMirror] = {
		if (qualifierForOpMap.isEmpty)
			qualifierForOpMap = Some(buildQualifierMap)
		qualifierForOpMap.get.get(qualifiedName) match {
			case Some(value) => Some(AnnotationBuilder.fromName(tf.getElementUtils, value))
			case None => None
		}
	}

	/**
	 * Constructs and returns the mapping between consistency qualifiers and operation levels
	 */
	def getQualifierForOpMap(implicit tf: AnnotatedTypeFactory): Map[String, String] = {
		if (qualifierForOpMap.isEmpty)
			qualifierForOpMap = Some(buildQualifierMap)
		qualifierForOpMap.get
	}

	private var qualifierForOpMap: Option[Map[String, String]] = None
	private def buildQualifierMap(implicit tf: AnnotatedTypeFactory): Map[String, String] = {
		// search for QualifierForOperation meta-annotation on all qualifiers in the qual/ directory
		// and map the qualifiers to the given operation level
		tf.getSupportedTypeQualifiers.asScala.
			map(q => tf.getAnnotatedType(q) match {
				case adt: AnnotatedDeclaredType => adt.getUnderlyingType.asElement
				case _ => null
			}).
			filter(x => x != null).
			foldLeft(Map.empty[String, String])((map, elt) => {
				tf.getAnnotationByClass(elt.getAnnotationMirrors, classOf[QualifierForOperation]) match {
					case null => map
					case annotation =>
						val value = annotation.getElementValues.values().asScala.head
						map + (value.getValue.toString -> elt.toString)
				}
			})
	}


	// #################################################################################################################
	// ### J-API types helpers
	// #################################################################################################################

	private val japiPackageName = s"de.tuda.stg.consys.japi"

	/**
	 * Checks if the given method invocation is a specific method on a specific receiver, including in interfaces and
	 * superclasses.
	 */
	private def methodInvocationIsAny(node: MethodInvocationTree,
									  receiverName: String,
									  methodNames: List[String])(implicit tf: AnnotatedTypeFactory) : Boolean = {
		def checkMethodName(memberSelectTree: MemberSelectTree): Boolean = {
			val methodId = memberSelectTree.getIdentifier.toString
			methodNames.map(x => x == methodId).fold(false)(_ || _)
		}
		def checkReceiverNameInInterfaces(dt: DeclaredType, mst: MemberSelectTree): Boolean = dt.asElement() match {
			case te: TypeElement => te.getInterfaces.asScala.exists {
				case interfaceType: DeclaredType if getQualifiedName(interfaceType) == receiverName =>
					checkMethodName(mst)
				case interfaceType: DeclaredType =>
					checkReceiverNameInInterfaces(interfaceType, mst)
				case _ => false
			}
			case _ => false
		}
		@tailrec
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
				val receiverType = tf.getAnnotatedType(memberSelectTree.getExpression)
				receiverType match {
					// check for a direct name match
					case adt : AnnotatedDeclaredType if getQualifiedName(adt) == receiverName =>
						checkMethodName(memberSelectTree)
					// check for name match in interfaces or superclass
					case adt: AnnotatedDeclaredType =>
						checkReceiverNameInInterfaces(adt.getUnderlyingType, memberSelectTree) ||
							checkReceiverNameInSuperClass(adt.getUnderlyingType, memberSelectTree)
					case _ => false
				}
			case _ => false
		}
	}

	def isRefDereference(node: MethodInvocationTree)(implicit tf: AnnotatedTypeFactory): Boolean =
		methodInvocationIsAny(node, s"$japiPackageName.Ref", List("ref"))

	def isAnyRefAccess(node: MethodInvocationTree)(implicit tf: AnnotatedTypeFactory): Boolean =
		methodInvocationIsAny(node, s"$japiPackageName.Ref", List("ref", "getField", "setField", "invoke"))

	def isCompiledRefAccess(node: MethodInvocationTree)(implicit tf: AnnotatedTypeFactory): Boolean =
		methodInvocationIsAny(node, s"$japiPackageName.Ref", List("getField", "setField", "invoke"))

	def isReplicateOrLookup(node: MethodInvocationTree)(implicit tf: AnnotatedTypeFactory): Boolean =
		methodInvocationIsAny(node, s"$japiPackageName.TransactionContext", List("replicate", "lookup"))

	def isTransaction(node: MethodInvocationTree)(implicit tf: AnnotatedTypeFactory): Boolean =
		methodInvocationIsAny(node, s"$japiPackageName.Store", List("transaction"))

	/**
	 * Checks if a type has a specific name, including in interfaces and superclasses.
	 */
	private def typeIsInstanceOf(typ: DeclaredType, name: String): Boolean = {
		def checkReceiverNameInInterfaces(dt: DeclaredType, name: String): Boolean = dt.asElement() match {
			case te: TypeElement => te.getInterfaces.asScala.exists {
				case interfaceType: DeclaredType if getQualifiedName(interfaceType) == name => true
				case interfaceType: DeclaredType => checkReceiverNameInInterfaces(interfaceType, name)
				case _ => false
			}
			case _ => false
		}
		@tailrec
		def checkReceiverNameInSuperClass(dt: DeclaredType, name: String): Boolean = dt.asElement() match {
			case te: TypeElement => te.getSuperclass match {
				case _: NoType => false
				case dt: DeclaredType if getQualifiedName(dt) == name => true
				case dt: DeclaredType => checkReceiverNameInInterfaces(dt, name) || checkReceiverNameInSuperClass(dt, name)
				case _ => false
			}
			case _ => false
		}

		val typName = getQualifiedName(typ)
		if (typName == name)
			true
		else
			checkReceiverNameInInterfaces(typ, name) || checkReceiverNameInSuperClass(typ, name)
	}

	def typeIsRef(typ: DeclaredType): Boolean = {
		typeIsInstanceOf(typ, s"$japiPackageName.Ref")
	}


	// #################################################################################################################
	// ### Method helpers
	// #################################################################################################################

	def isDeclaredSideEffectFree(method: ExecutableElement)(implicit tf: AnnotatedTypeFactory): Boolean =
		tf.getDeclAnnotation(method, classOf[SideEffectFree]) != null ||
			tf.getDeclAnnotation(method, classOf[Pure]) != null

	def isDeclaredTransactional(method: ExecutableElement)(implicit tf: AnnotatedTypeFactory): Boolean =
		tf.getDeclAnnotation(method, classOf[Transactional]) != null

	def isDeclaredStrongOp(method: ExecutableElement)(implicit tf: AnnotatedTypeFactory): Boolean =
		tf.getDeclAnnotation(method, classOf[StrongOp]) != null

	def isDeclaredWeakOp(method: ExecutableElement)(implicit tf: AnnotatedTypeFactory): Boolean =
		tf.getDeclAnnotation(method, classOf[WeakOp]) != null

	def isDeclaredDefaultOp(method: ExecutableElement)(implicit tf: AnnotatedTypeFactory): Boolean =
		!isDeclaredWeakOp(method) && !isDeclaredStrongOp(method)

	def isPrivateOrProtected(elt: Element): Boolean =
		elt.getModifiers.contains(Modifier.PRIVATE) || elt.getModifiers.contains(Modifier.PROTECTED)

	def isStatic(method: ExecutableElement): Boolean = method.getModifiers.contains(Modifier.STATIC)
}
