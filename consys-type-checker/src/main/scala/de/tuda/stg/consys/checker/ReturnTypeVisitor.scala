package de.tuda.stg.consys.checker

import com.sun.source.tree.{AnnotatedTypeTree, ClassTree, MethodTree, ReturnTree}
import com.sun.source.util.TreeScanner
import de.tuda.stg.consys.checker.TypeFactoryUtils.{getMixedDefaultOp, getQualifiedName, inconsistentAnnotation, localAnnotation}
import de.tuda.stg.consys.checker.qual.Mixed
import org.checkerframework.framework.`type`.AnnotatedTypeFactory
import org.checkerframework.javacutil.{AnnotationUtils, ElementUtils, TreeUtils}

import javax.lang.model.`type`.TypeKind
import javax.lang.model.element.{AnnotationMirror, ExecutableElement, TypeElement}
import scala.collection.convert.ImplicitConversions.`collection AsScalaIterable`
import scala.collection.convert.ImplicitConversions.`collection asJava`
import scala.collection.mutable

class ReturnTypeVisitor(implicit tf: AnnotatedTypeFactory) extends TreeScanner[AnnotationMirror, AnnotationMirror] {

    // TODO: string representations?
    type InferenceTable = mutable.Map[(String, String, String), mutable.Map[ExecutableElement, AnnotationMirror]]
    var inferenceTable: InferenceTable = mutable.Map.empty


    def processClass(node: ClassTree, qualifier: AnnotationMirror): Unit = {
        val classElement = TreeUtils.elementFromDeclaration(node)
        val className = getQualifiedName(node)
        val qualifierName = getQualifiedName(qualifier)
        val defaultOp = if (tf.areSameByClass(qualifier, classOf[Mixed])) getMixedDefaultOp(qualifier) else ""

        if (inferenceTable.contains((className, qualifierName, defaultOp)))
            return

        inferenceTable.put((className, qualifierName, defaultOp), mutable.Map.empty)

        node.getMembers.foreach {
            case m: MethodTree =>
                val methodElement = TreeUtils.elementFromDeclaration(m)
                if (methodElement.getReturnType.getKind != TypeKind.VOID) {
                    val overrides = ElementUtils.getOverriddenMethods(methodElement, tf.types)
                    val init =
                        if (!overrides.isEmpty)
                            tf.getAnnotatedType(overrides.head).getReturnType.getAnnotationInHierarchy(inconsistentAnnotation)
                        else localAnnotation

                    val r = this.visitMethodWithInit(m, init)
                    inferenceTable.get(className, qualifierName, defaultOp).get.put(methodElement, r)
                }
            case _ =>
        }
    }

    override def reduce(r1: AnnotationMirror, r2: AnnotationMirror): AnnotationMirror = {
        (r1, r2) match {
            case (null, null) => null
            case (null, r) => r
            case (r, null) => r
            case (_, _) => tf.getQualifierHierarchy.leastUpperBound(r1, r2)
        }
    }

    private def visitMethodWithInit(node: MethodTree, init: AnnotationMirror = localAnnotation): AnnotationMirror = {
        val annos = node.getModifiers.getAnnotations.map(t => TreeUtils.annotationFromAnnotationTree(t)).filter(p => tf.isSupportedQualifier(p))
        val explicit = tf.getQualifierHierarchy.findAnnotationInHierarchy(annos, inconsistentAnnotation)
        if (explicit != null) explicit else super.visitMethod(node, init)
    }

    override def visitReturn(node: ReturnTree, p: AnnotationMirror): AnnotationMirror = {
        node.getExpression match {
            case null => null
            case tree =>
                tf.getQualifierHierarchy.leastUpperBound(
                    p,
                    tf.getAnnotatedType(tree).getAnnotationInHierarchy(localAnnotation))
            // TODO: framework not ready here if called from visitDeclared, doesn't seem to be a problem for inferenceVisitor
        }
    }
}
