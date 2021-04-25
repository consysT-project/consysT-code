package de.tuda.stg.consys.checker

import com.sun.source.tree.{AnnotationTree, ClassTree, IdentifierTree, MethodTree, ModifiersTree, Tree, VariableTree}
import com.sun.source.util.TreeScanner
import de.tuda.stg.consys.checker.TypeFactoryUtils.{checkerPackageName, getQualifiedName}
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.AnnotatedDeclaredType
import org.checkerframework.framework.`type`.GenericAnnotatedTypeFactory
import org.checkerframework.javacutil.{AnnotationBuilder, AnnotationUtils, ElementUtils, TreeUtils}

import javax.lang.model.element.{AnnotationMirror, ElementKind, TypeElement, VariableElement}
import scala.collection.convert.ImplicitConversions.`collection AsScalaIterable`
import scala.collection.mutable

class InferenceVisitor(atypeFactory: GenericAnnotatedTypeFactory[_, _, _, _]) extends TreeScanner[Void, Void] {

    var fieldTable: mutable.Map[String, String] = mutable.Map[String, String]()
    //private var fieldTable = mutable.Map[VariableElement, AnnotationMirror]()

    private var classContext = ""
    private var methodContext = ""

    private val annnoMapping = Map(s"$checkerPackageName.qual.WeakOp" -> s"$checkerPackageName.qual.Weak",
        s"$checkerPackageName.qual.StrongOp" -> s"$checkerPackageName.qual.Strong")


    override def visitClass(node: ClassTree, p: Void): Void = {
        val replicated = hasAnnotation(node.getModifiers, s"$checkerPackageName.qual.Mixed")
        //AnnotationUtils.containsSameByName(p.getUnderlyingType.getAnnotationMirrors, s"$checkerPackageName.qual.Replicated")

        if (replicated) {
            val prev = classContext
            classContext = getQualifiedName(node)
            val r = super.visitClass(node, p)
            classContext = prev
            r
        } else {
            null
        }
    }

    override def visitMethod(node: MethodTree, p: Void): Void = {
        if (classContext.nonEmpty) {
            annnoMapping.foreach(mapping => {
                if (hasAnnotation(node.getModifiers, mapping._1))
                    methodContext = mapping._2
            })

            val r = super.visitMethod(node, p)
            methodContext = ""
            r
        } else {
            null
        }
    }

    override def visitIdentifier(node: IdentifierTree, p: Void): Void = {
        // TODO: check if ID belongs to this class
        if (methodContext.nonEmpty) {
            val elt = TreeUtils.elementFromUse(node)
            if (elt.getKind == ElementKind.FIELD) {
                val fieldName = ElementUtils.getQualifiedName(elt)
                fieldTable.get(fieldName) match {
                    case Some(level) =>
                        val lup = atypeFactory.getQualifierHierarchy.leastUpperBound(
                            AnnotationBuilder.fromName(atypeFactory.getElementUtils, level),
                            AnnotationBuilder.fromName(atypeFactory.getElementUtils, methodContext))
                        fieldTable.update(fieldName, AnnotationUtils.annotationName(lup))
                    case None =>
                        fieldTable.update(fieldName, methodContext)
                }
            }
        }
        super.visitIdentifier(node, p)
    }

    private def hasAnnotation(modifiers: ModifiersTree, annotation: String): Boolean ={
        modifiers.getAnnotations.exists((at: AnnotationTree) => atypeFactory.getAnnotatedType(at.getAnnotationType) match {
            case adt: AnnotatedDeclaredType =>
                getQualifiedName(adt) == annotation
            case _ =>
                false
        })
    }
}
