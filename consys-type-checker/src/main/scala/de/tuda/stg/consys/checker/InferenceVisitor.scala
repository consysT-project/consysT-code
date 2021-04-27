package de.tuda.stg.consys.checker

import com.sun.source.tree.{AnnotationTree, ClassTree, IdentifierTree, MethodTree, ModifiersTree, Tree, VariableTree}
import com.sun.source.util.TreeScanner
import de.tuda.stg.consys.checker.TypeFactoryUtils.{annoPackageName, checkerPackageName, getQualifiedName}
import de.tuda.stg.consys.checker.qual.QualifierForOperation
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.AnnotatedDeclaredType
import org.checkerframework.framework.`type`.GenericAnnotatedTypeFactory
import org.checkerframework.javacutil.{AnnotationBuilder, AnnotationUtils, ElementUtils, TreeUtils, TypesUtils}

import java.lang.Class
import java.lang.annotation.Annotation
import javax.lang.model.`type`.DeclaredType
import javax.lang.model.element.{AnnotationMirror, AnnotationValue, ElementKind, TypeElement, VariableElement}
import scala.collection.convert.ImplicitConversions.`collection AsScalaIterable`
import scala.collection.mutable

class InferenceVisitor(atypeFactory: GenericAnnotatedTypeFactory[_, _, _, _]) extends TreeScanner[Void, Void] {

    var fieldTable: mutable.Map[VariableElement, AnnotationMirror] = mutable.Map[VariableElement, AnnotationMirror]()

    private var classContext = ""
    private var methodContext: Option[AnnotationMirror] = Option.empty

    //private val annnoMapping = mutable.Map(s"$annoPackageName.methods.WeakOp" -> s"$checkerPackageName.qual.Weak",
    //    s"$annoPackageName.methods.StrongOp" -> s"$checkerPackageName.qual.Strong")
    private val annnoMapping = mutable.Map.empty[String, String]
    //buildQualifierMap()

    override def visitClass(node: ClassTree, p: Void): Void = {
        if (annnoMapping.isEmpty)
            buildQualifierMap()
        val mixed = hasAnnotation(node.getModifiers, s"$checkerPackageName.qual.Mixed")
        if (mixed) {
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
                val (operation, qualifier) = mapping
                if (hasAnnotation(node.getModifiers, operation)) {
                    methodContext = Option(AnnotationBuilder.fromName(atypeFactory.getElementUtils, qualifier))
                }
            })

            val r = super.visitMethod(node, p)
            methodContext = Option.empty
            r
        } else {
            null
        }
    }

    override def visitIdentifier(node: IdentifierTree, p: Void): Void = {
        // TODO: check if ID belongs to this class
        methodContext match {
            case Some(methodLevel) => TreeUtils.elementFromUse(node) match {
                case field: VariableElement if field.getKind == ElementKind.FIELD => fieldTable.get(field) match {
                    case Some(fieldLevel) =>
                        val lup = atypeFactory.getQualifierHierarchy.leastUpperBound(fieldLevel, methodLevel)
                        fieldTable.update(field, lup)
                    case None =>
                        fieldTable.update(field, methodLevel)
                }
                case _ =>
            }
            case _ =>
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

     def buildQualifierMap(): Unit = {
        val qualifiers = atypeFactory.getSupportedTypeQualifiers

        qualifiers.
            map(q => atypeFactory.getAnnotatedType(q)).
            filter(p => p match {
                case adt: AnnotatedDeclaredType =>
                    ElementUtils.hasAnnotation(adt.getUnderlyingType.asElement(),
                        s"$checkerPackageName.qual.QualifierForOperation")
                case _ => false
            }).
            map(atm => atm.asInstanceOf[AnnotatedDeclaredType].getUnderlyingType.asElement()).
            foreach(elt => {
                val a = AnnotationUtils.getAnnotationByClass(elt.getAnnotationMirrors, classOf[QualifierForOperation])
                val value = a.getElementValues.values().head
                annnoMapping.update(value.getValue.toString, elt.toString)
            })
    }
}
