package de.tuda.stg.consys.checker

import org.checkerframework.framework.`type`.{AnnotatedTypeFactory, MostlyNoElementQualifierHierarchy, TypeHierarchy}
import org.checkerframework.framework.util.QualifierKind
import org.checkerframework.javacutil.{AnnotationBuilder, AnnotationUtils}

import java.lang.annotation.Annotation
import java.util
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.util.Elements
import scala.collection.convert.ImplicitConversions.`collection AsScalaIterable`

class ConsistencyQualifierHierarchy(qualifierClasses: util.Collection[Class[_ <: Annotation]], elements: Elements, val atypeFactory: ConsistencyAnnotatedTypeFactory) extends MostlyNoElementQualifierHierarchy(qualifierClasses, elements) {
    override def isSubtypeWithElements(subAnno: AnnotationMirror, subKind: QualifierKind, superAnno: AnnotationMirror, superKind: QualifierKind): Boolean = {
        if (subKind.compareTo(superKind) != 0) { // TODO: correct comparison?
            return false
        }

        (annotationClassFromElement(subAnno), annotationClassFromElement(superAnno)) match {
            case (sub, sup) => super.isSubtype(sub, sup)
            case _ => false
        }
    }

    override def leastUpperBoundWithElements(a1: AnnotationMirror, qualifierKind1: QualifierKind, a2: AnnotationMirror, qualifierKind2: QualifierKind, lubKind: QualifierKind): AnnotationMirror = ???

    override def greatestLowerBoundWithElements(a1: AnnotationMirror, qualifierKind1: QualifierKind, a2: AnnotationMirror, qualifierKind2: QualifierKind, glbKind: QualifierKind): AnnotationMirror = ???

    private def annotationClassFromElement(anno: AnnotationMirror) = {
        val op = AnnotationUtils.getElementValuesWithDefaults(anno).values.head.getValue
        val qual = atypeFactory.qualifierForOperation(op.toString)
        AnnotationBuilder.fromName(atypeFactory.getElementUtils, qual)
    }
}
