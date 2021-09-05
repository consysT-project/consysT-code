package de.tuda.stg.consys.checker

import de.tuda.stg.consys.checker.qual.Mixed
import org.checkerframework.framework.`type`.{AnnotatedTypeFactory, MostlyNoElementQualifierHierarchy, TypeHierarchy}
import org.checkerframework.framework.util.QualifierKind

import java.lang.annotation.Annotation
import java.util
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.util.Elements

class ConsistencyQualifierHierarchy(qualifierClasses: util.Collection[Class[_ <: Annotation]], elements: Elements, val atypeFactory: ConsistencyAnnotatedTypeFactory) extends MostlyNoElementQualifierHierarchy(qualifierClasses, elements) {
    import TypeFactoryUtils._
    implicit val tf: AnnotatedTypeFactory = atypeFactory

    override def isSubtypeWithElements(subAnno: AnnotationMirror, subKind: QualifierKind, superAnno: AnnotationMirror, superKind: QualifierKind): Boolean = {
        subKind.compareTo(superKind) match {
            case 0 if subKind.getAnnotationClass.equals(classOf[Mixed]) =>
                super.isSubtype(getQualifierForMixedDefaultOp(subAnno), getQualifierForMixedDefaultOp(superAnno))
            case _ => subKind.isSubtypeOf(superKind)
        }
    }

    override def leastUpperBoundWithElements(a1: AnnotationMirror, qualifierKind1: QualifierKind, a2: AnnotationMirror, qualifierKind2: QualifierKind, lubKind: QualifierKind): AnnotationMirror = {
        qualifierKind1.compareTo(qualifierKind2) match {
            case 0 if qualifierKind1.getAnnotationClass.equals(classOf[Mixed]) =>
                super.leastUpperBound(getQualifierForMixedDefaultOp(a1), getQualifierForMixedDefaultOp(a2))
            case _ =>
                if (qualifierKind1.compareTo(lubKind) == 0) a1 else a2
        }
    }

    override def greatestLowerBoundWithElements(a1: AnnotationMirror, qualifierKind1: QualifierKind, a2: AnnotationMirror, qualifierKind2: QualifierKind, glbKind: QualifierKind): AnnotationMirror = {
        qualifierKind1.compareTo(qualifierKind2) match {
            case 0 if qualifierKind1.getAnnotationClass.equals(classOf[Mixed]) =>
                super.greatestLowerBound(getQualifierForMixedDefaultOp(a1), getQualifierForMixedDefaultOp(a2))
            case _ =>
                if (qualifierKind1.compareTo(glbKind) == 0) a1 else a2
        }
    }
}
