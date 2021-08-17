package de.tuda.stg.consys.checker

import de.tuda.stg.consys.checker.TypeFactoryUtils.{immutableAnnotation, inconsistentAnnotation, japiPackageName}
import de.tuda.stg.consys.checker.qual.MutableBottom
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.AnnotatedDeclaredType
import org.checkerframework.framework.`type`.{AnnotatedTypeFactory, AnnotatedTypeMirror, TypeHierarchy}
import org.checkerframework.javacutil.TypesUtils

import javax.lang.model.element.AnnotationMirror

/**
	* Created on 23.07.19.
	*
	* @author Mirko Köhler
	*/
class ConsistencyTypeHierarchy(val hierarchy : TypeHierarchy, val atypeFactory : AnnotatedTypeFactory) extends TypeHierarchy {
	implicit private val tf: AnnotatedTypeFactory = atypeFactory
	var doImmutabilityCheck: Boolean = false

	override def isSubtype(subtype : AnnotatedTypeMirror, supertype : AnnotatedTypeMirror) : Boolean = (refType(subtype), refType(supertype)) match {
		case (Some(declaredSubtype), Some(declaredSupertype)) =>
			val subtypeMirror = getArgOfRefType(declaredSubtype)
			val superTypeMirror = getArgOfRefType(declaredSupertype)

			// always check immutability for Ref<> types
			isCombinedSubtype(subtypeMirror, superTypeMirror)

		case _ if TypesUtils.isPrimitiveOrBoxed(subtype.getUnderlyingType) && TypesUtils.isPrimitiveOrBoxed(supertype.getUnderlyingType) =>
				// || TypesUtils.isClassType(subtype.getUnderlyingType) && TypesUtils.isClassType(supertype.getUnderlyingType) =>
			isConsistencySubtypeOnly(subtype, supertype)

		case _ if tf.asInstanceOf[ConsistencyAnnotatedTypeFactory].isInMixedClassContext =>
			isCombinedSubtype(subtype, supertype)

		case _ =>
			// TODO: find a way to use this subtyping check for non-ref objects without breaking non-distributed code
			//hierarchy.isSubtype(subtype, supertype)
			//isConsistencySubtypeOnly(subtype, supertype)
			isCombinedSubtype(subtype, supertype)
	}


	private def refType(typ : AnnotatedTypeMirror) : Option[AnnotatedDeclaredType] = typ match {
		case declared : AnnotatedDeclaredType
			if TypesUtils.getQualifiedName(declared.getUnderlyingType) contentEquals s"$japiPackageName.Ref" =>
				Some(declared)

		case _ => None
	}


	private def getArgOfRefType(refType : AnnotatedDeclaredType) : AnnotatedTypeMirror = {
			val typeArgs = refType.getTypeArguments

			if (typeArgs.size() == 1) {
				//If JRef has a type argument then return it
				typeArgs.get(0)
			} else {
				//else create a mirror for Object and annotate it
				val objectMirror = TypesUtils.typeFromClass(classOf[Object], atypeFactory.types, atypeFactory.getElementUtils)
				val annotated = AnnotatedTypeMirror.createType(objectMirror, atypeFactory, true)
				annotated.addAnnotation(TypeFactoryUtils.inconsistentAnnotation(atypeFactory))
				annotated.addAnnotation(TypeFactoryUtils.mutableAnnotation)
				annotated
			}
	}

	private def isConsistencySubtypeOnly(subtype : AnnotatedTypeMirror, supertype : AnnotatedTypeMirror): Boolean = {
		val consistencySubtype = subtype.getEffectiveAnnotationInHierarchy(inconsistentAnnotation)
		val consistencySupertype = supertype.getEffectiveAnnotationInHierarchy(inconsistentAnnotation)
		tf.getQualifierHierarchy.isSubtype(consistencySubtype, consistencySupertype)
	}

	// TODO: disable mutability check for primitive types
	private def isCombinedSubtype(subtype : AnnotatedTypeMirror, supertype : AnnotatedTypeMirror): Boolean = {
		val mutabilitySubtype = subtype.getEffectiveAnnotationInHierarchy(immutableAnnotation)
		val mutabilitySupertype = supertype.getEffectiveAnnotationInHierarchy(immutableAnnotation)
		val consistencySubtype = subtype.getEffectiveAnnotationInHierarchy(inconsistentAnnotation)
		val consistencySupertype = supertype.getEffectiveAnnotationInHierarchy(inconsistentAnnotation)

		if (subtype.hasAnnotation(classOf[MutableBottom]))
			true
		else if (isSameType(consistencySubtype, consistencySupertype))
			tf.getQualifierHierarchy.isSubtype(mutabilitySubtype, mutabilitySupertype)
		else if (isSameType(mutabilitySubtype, immutableAnnotation) && isSameType(mutabilitySupertype, immutableAnnotation))
			tf.getQualifierHierarchy.isSubtype(consistencySubtype, consistencySupertype)
		else
			false
	}

	private def isSameType(t1: AnnotationMirror, t2: AnnotationMirror): Boolean =
		tf.getQualifierHierarchy.isSubtype(t1, t2) && tf.getQualifierHierarchy.isSubtype(t2, t1)
}
