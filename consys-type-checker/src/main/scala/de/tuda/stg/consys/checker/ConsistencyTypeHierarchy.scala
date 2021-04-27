package de.tuda.stg.consys.checker

import de.tuda.stg.consys.checker.TypeFactoryUtils.japiPackageName
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.AnnotatedDeclaredType
import org.checkerframework.framework.`type`.{AnnotatedTypeFactory, AnnotatedTypeMirror, TypeHierarchy}
import org.checkerframework.javacutil.TypesUtils

/**
	* Created on 23.07.19.
	*
	* @author Mirko Köhler
	*/
class ConsistencyTypeHierarchy(val hierarchy : TypeHierarchy, val atypeFactory : AnnotatedTypeFactory) extends TypeHierarchy {

	override def isSubtype(subtype : AnnotatedTypeMirror, supertype : AnnotatedTypeMirror) : Boolean = (refType(subtype), refType(supertype)) match {
		case (Some(declaredSubtype), Some(declaredSupertype)) =>
			val subtypeMirror = getArgOfRefType(declaredSubtype)
			val superTypeMirror = getArgOfRefType(declaredSupertype)

			hierarchy.isSubtype(subtypeMirror, superTypeMirror)

		case _ =>
			hierarchy.isSubtype(subtype, supertype)
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
				annotated
			}
	}




}
