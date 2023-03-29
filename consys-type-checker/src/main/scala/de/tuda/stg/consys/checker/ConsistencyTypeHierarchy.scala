package de.tuda.stg.consys.checker

import de.tuda.stg.consys.checker.TypeFactoryUtils.{immutableAnnotation, inconsistentAnnotation, typeIsRef}
import de.tuda.stg.consys.checker.qual.{Local, MutableBottom, ThisConsistent}
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
	implicit private val tf: ConsistencyAnnotatedTypeFactory = atypeFactory.asInstanceOf[ConsistencyAnnotatedTypeFactory]

    override def isSubtype(subtype: AnnotatedTypeMirror, supertype: AnnotatedTypeMirror): Boolean = {
		checkThisConsistent(subtype)
		checkThisConsistent(supertype)

		(refType(subtype), refType(supertype)) match {
            case (Some(declaredSubtype), Some(declaredSupertype)) =>
                val subtypeMirror = getArgOfRefType(declaredSubtype)
                val superTypeMirror = getArgOfRefType(declaredSupertype)
				checkThisConsistent(subtypeMirror)
				checkThisConsistent(superTypeMirror)

                // always check immutability for Ref<> types
                isCombinedSubtype(subtypeMirror, superTypeMirror) && hierarchy.isSubtype(subtypeMirror.getErased, superTypeMirror.getErased)

            case _ if TypesUtils.isPrimitiveOrBoxed(subtype.getUnderlyingType) && TypesUtils.isPrimitiveOrBoxed(supertype.getUnderlyingType) =>
                isConsistencySubtypeOnly(subtype, supertype)

            case _ if tf.visitClassContext.nonEmpty || tf.getVisitor.getTransactionContext =>
				// in transactions or replicated classes check for full subtyping
                isCombinedSubtype(subtype, supertype) && hierarchy.isSubtype(subtype, supertype)

            case _ => // skip immutability checks for non-replicated type-checking
                isConsistencySubtypeOnly(subtype, supertype) && hierarchy.isSubtype(subtype, supertype)
        }
    }

	private def refType(typ : AnnotatedTypeMirror) : Option[AnnotatedDeclaredType] = typ match {
		case declared : AnnotatedDeclaredType if typeIsRef(declared.getUnderlyingType) => Some(declared)
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

	private def isCombinedSubtype(subtype : AnnotatedTypeMirror, supertype : AnnotatedTypeMirror): Boolean = {
		val mutabilitySubtype = subtype.getEffectiveAnnotationInHierarchy(immutableAnnotation)
		val mutabilitySupertype = supertype.getEffectiveAnnotationInHierarchy(immutableAnnotation)
		val consistencySubtype = subtype.getEffectiveAnnotationInHierarchy(inconsistentAnnotation)
		val consistencySupertype = supertype.getEffectiveAnnotationInHierarchy(inconsistentAnnotation)

		if (mutabilitySubtype == null || mutabilitySupertype == null)
			sys.error("ConSysT type checker bug: immutability qualifier is missing from type")
		if (consistencySubtype == null || consistencySupertype == null)
			sys.error("ConSysT type checker bug: consistency qualifier is missing from type")

		if (subtype.hasAnnotation(classOf[MutableBottom]) && !subtype.hasAnnotation(classOf[Local]))
			sys.error(s"ConSysT type checker bug: @MutableBottom found on non-@Local qualifier, " +
				s"was ${subtype.getAnnotationInHierarchy(TypeFactoryUtils.inconsistentAnnotation)}")
		else if (subtype.hasAnnotation(classOf[MutableBottom]) && subtype.hasAnnotation(classOf[Local]))
			true
		else if (isSameType(mutabilitySupertype, immutableAnnotation))
			tf.getQualifierHierarchy.isSubtype(mutabilitySubtype, mutabilitySupertype) &&
				tf.getQualifierHierarchy.isSubtype(consistencySubtype, consistencySupertype)
		else
			tf.getQualifierHierarchy.isSubtype(mutabilitySubtype, mutabilitySupertype) &&
				isSameType(consistencySubtype, consistencySupertype)
	}

    private def isSameType(t1: AnnotationMirror, t2: AnnotationMirror): Boolean =
        tf.getQualifierHierarchy.isSubtype(t1, t2) && tf.getQualifierHierarchy.isSubtype(t2, t1)

    private def checkThisConsistent(atm: AnnotatedTypeMirror): Unit = {
        // @ThisConsistent must be replaced before any type hierarchy operation, as it is not a real concrete type
        if (atm.hasAnnotation(classOf[ThisConsistent]))
            sys.error("ConSysT type checker bug: Trying to use @ThisConsistent in subtyping check")
	}
}
