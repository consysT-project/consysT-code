package de.tuda.stg.consys.checker

import de.tuda.stg.consys.checker.TypeFactoryUtils.getDefaultOp
import de.tuda.stg.consys.checker.qual.Mixed
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
        subKind.compareTo(superKind) match {
            case 0 if subKind.getAnnotationClass.equals(classOf[Mixed]) =>
                super.isSubtype(getDefaultOpElement(subAnno), getDefaultOpElement(superAnno))
            case _ => subKind.isSubtypeOf(superKind)
        }
    }

    override def leastUpperBoundWithElements(a1: AnnotationMirror, qualifierKind1: QualifierKind, a2: AnnotationMirror, qualifierKind2: QualifierKind, lubKind: QualifierKind): AnnotationMirror = {
        qualifierKind1.compareTo(qualifierKind2) match {
            case 0 if qualifierKind1.getAnnotationClass.equals(classOf[Mixed]) =>
                super.leastUpperBound(getDefaultOpElement(a1), getDefaultOpElement(a2))
            case _ =>
                if (qualifierKind1.compareTo(lubKind) == 0) a1 else a2
        }
    }

    override def greatestLowerBoundWithElements(a1: AnnotationMirror, qualifierKind1: QualifierKind, a2: AnnotationMirror, qualifierKind2: QualifierKind, glbKind: QualifierKind): AnnotationMirror = {
        qualifierKind1.compareTo(qualifierKind2) match {
            case 0 if qualifierKind1.getAnnotationClass.equals(classOf[Mixed]) =>
                super.greatestLowerBound(getDefaultOpElement(a1), getDefaultOpElement(a2))
            case _ =>
                if (qualifierKind1.compareTo(glbKind) == 0) a1 else a2
        }
    }

    private def getDefaultOpElement(anno: AnnotationMirror): AnnotationMirror = {
        val operationLevel = getDefaultOp(anno)
        val qualifier = atypeFactory.qualifierForOperation(operationLevel)
        AnnotationBuilder.fromName(atypeFactory.getElementUtils, qualifier)
    }
}
