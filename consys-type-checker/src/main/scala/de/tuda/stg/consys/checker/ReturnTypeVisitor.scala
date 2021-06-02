package de.tuda.stg.consys.checker

import com.sun.source.tree.{MethodTree, ReturnTree}
import com.sun.source.util.TreeScanner
import de.tuda.stg.consys.checker.TypeFactoryUtils.{inconsistentAnnotation, localAnnotation}
import org.checkerframework.framework.`type`.AnnotatedTypeFactory

import javax.lang.model.element.AnnotationMirror

class ReturnTypeVisitor(atypeFactory: AnnotatedTypeFactory) extends TreeScanner[AnnotationMirror, AnnotationMirror] {

    override def reduce(r1: AnnotationMirror, r2: AnnotationMirror): AnnotationMirror = {
        (r1, r2) match {
            case (null, null) => null
            case (null, r) => r
            case (r, null) => r
            case (_, _) => atypeFactory.getQualifierHierarchy.leastUpperBound(r1, r2)
        }
    }

    def visitMethod(node: MethodTree): AnnotationMirror = {
        super.visitMethod(node, localAnnotation(atypeFactory))
    }

    override def visitReturn(node: ReturnTree, p: AnnotationMirror): AnnotationMirror = {
        node.getExpression match {
            case null => null
            case tree =>
                atypeFactory.getQualifierHierarchy.leastUpperBound(
                    p,
                    atypeFactory.getAnnotatedType(tree).getAnnotationInHierarchy(localAnnotation(atypeFactory)))
        }
    }
}
