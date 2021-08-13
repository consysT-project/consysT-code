package de.tuda.stg.consys.checker

import de.tuda.stg.consys.checker.TypeFactoryUtils.{immutableAnnotation, inconsistentAnnotation, japiPackageName}
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.AnnotatedDeclaredType
import org.checkerframework.framework.`type`.{AnnotatedTypeFactory, AnnotatedTypeMirror, TypeHierarchy}
import org.checkerframework.javacutil.TypesUtils

import javax.lang.model.`type`.TypeKind
import javax.lang.model.element.AnnotationMirror

/**
	* Created on 23.07.19.
	*
	* @author Mirko Köhler
	*/
class ConsistencyTypeHierarchy(val hierarchy : TypeHierarchy, val atypeFactory : AnnotatedTypeFactory) extends TypeHierarchy {
	implicit private val tf: AnnotatedTypeFactory = atypeFactory

	override def isSubtype(subtype : AnnotatedTypeMirror, supertype : AnnotatedTypeMirror) : Boolean = (refType(subtype), refType(supertype)) match {
		case (Some(declaredSubtype), Some(declaredSupertype)) =>
			val subtypeMirror = getArgOfRefType(declaredSubtype)
			val superTypeMirror = getArgOfRefType(declaredSupertype)

			//hierarchy.isSubtype(subtypeMirror, superTypeMirror)
			isCombinedSubtype(subtypeMirror, superTypeMirror)

		case _ if tf.asInstanceOf[ConsistencyAnnotatedTypeFactory].isInMixedClassContext =>
			if (TypesUtils.isPrimitiveOrBoxed(subtype.getUnderlyingType) && TypesUtils.isPrimitiveOrBoxed(supertype.getUnderlyingType)) {
				val consistencySubtype = subtype.getAnnotationInHierarchy(inconsistentAnnotation)
				val consistencySupertype = supertype.getAnnotationInHierarchy(inconsistentAnnotation)
				tf.getQualifierHierarchy.isSubtype(consistencySubtype, consistencySupertype)
			} else {
				isCombinedSubtype(subtype, supertype)
			}

		case _ =>
			// TODO: find a way to use this subtyping check for non-ref objects without breaking non-distributed code
			//hierarchy.isSubtype(subtype, supertype)
			//isCombinedSubtype(subtype, supertype)
			val consistencySubtype = subtype.getAnnotationInHierarchy(inconsistentAnnotation)
			val consistencySupertype = supertype.getAnnotationInHierarchy(inconsistentAnnotation)
			tf.getQualifierHierarchy.isSubtype(consistencySubtype, consistencySupertype)
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


	// TODO: disable mutability check for primitive types
	private def isCombinedSubtype(subtype : AnnotatedTypeMirror, supertype : AnnotatedTypeMirror): Boolean = {
		val mutabilitySubtype = subtype.getAnnotationInHierarchy(immutableAnnotation)
		val mutabilitySupertype = supertype.getAnnotationInHierarchy(immutableAnnotation)
		val consistencySubtype = subtype.getAnnotationInHierarchy(inconsistentAnnotation)
		val consistencySupertype = supertype.getAnnotationInHierarchy(inconsistentAnnotation)

		if (isSameType(consistencySubtype, consistencySupertype))
			tf.getQualifierHierarchy.isSubtype(mutabilitySubtype, mutabilitySupertype)
		else if (isSameType(mutabilitySubtype, immutableAnnotation) && isSameType(mutabilitySupertype, immutableAnnotation))
			tf.getQualifierHierarchy.isSubtype(consistencySubtype, consistencySupertype)
		else
			false
	}

	private def isSameType(t1: AnnotationMirror, t2: AnnotationMirror): Boolean = tf.getQualifierHierarchy.isSubtype(t1, t2) &&
		tf.getQualifierHierarchy.isSubtype(t2, t1)
}
