package de.tuda.stg.consys.checker

import com.sun.source.tree.{AnnotationTree, AssignmentTree, ClassTree, CompoundAssignmentTree, ExpressionTree, IdentifierTree, MemberSelectTree, MethodTree, ModifiersTree, Tree, VariableTree}
import com.sun.source.util.TreeScanner
import de.tuda.stg.consys.checker.TypeFactoryUtils.{annoPackageName, checkerPackageName, getQualifiedName}
import de.tuda.stg.consys.checker.qual.{Local, QualifierForOperation}
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.AnnotatedDeclaredType
import org.checkerframework.framework.`type`.GenericAnnotatedTypeFactory
import org.checkerframework.javacutil.{AnnotationBuilder, AnnotationUtils, ElementUtils, TreeUtils, TypesUtils}

import java.lang.Class
import java.lang.annotation.Annotation
import javax.lang.model.`type`.DeclaredType
import javax.lang.model.element.{AnnotationMirror, AnnotationValue, ElementKind, TypeElement, VariableElement}
import scala.collection.convert.ImplicitConversions.`collection AsScalaIterable`
import scala.collection.mutable

class InferenceVisitor(atypeFactory: GenericAnnotatedTypeFactory[_, _, _, _]) extends TreeScanner[Void, Boolean] {

    var fieldTable: mutable.Map[VariableElement, AnnotationMirror] = mutable.Map[VariableElement, AnnotationMirror]()

    private var classContext = ""
    private var methodContext: Option[AnnotationMirror] = Option.empty

    //private val annnoMapping = mutable.Map(s"$annoPackageName.methods.WeakOp" -> s"$checkerPackageName.qual.Weak",
    //    s"$annoPackageName.methods.StrongOp" -> s"$checkerPackageName.qual.Strong")
    private var annnoMapping: Map[String, String] = Map.empty
    //buildQualifierMap()

    override def visitClass(node: ClassTree, p: Boolean): Void = {
        if (annnoMapping.isEmpty)
            annnoMapping = buildQualifierMap()
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

    override def visitMethod(node: MethodTree, p: Boolean): Void = {
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

    override def visitAssignment(node: AssignmentTree, p: Boolean): Void = {
        var r = scan(node.getVariable, true)
        r = reduce(scan(node.getExpression, false), r)
        r
    }

    override def visitCompoundAssignment(node: CompoundAssignmentTree, p: Boolean): Void = {
        var r = scan(node.getVariable, true)
        r = reduce(scan(node.getExpression, false), r)
        r
    }

    // TODO: are there more tree types for field use other than IdentifierTree and MemberSelect?
    override def visitMemberSelect(node: MemberSelectTree, p: Boolean): Void = {
        processField(node, p)
        super.visitMemberSelect(node, p)
    }

    override def visitIdentifier(node: IdentifierTree, p: Boolean): Void = {
        processField(node, p)
        super.visitIdentifier(node, p)
    }

    private def processField(node: ExpressionTree, p: Boolean): Unit = {
        // TODO: check if ID belongs to this class
        methodContext match {
            case Some(methodLevel) => (TreeUtils.elementFromUse(node), p) match {
                case (field: VariableElement, true) if field.getKind == ElementKind.FIELD => fieldTable.get(field) match {
                    case Some(fieldLevel) =>
                        val lup = atypeFactory.getQualifierHierarchy.leastUpperBound(fieldLevel, methodLevel)
                        fieldTable.update(field, lup)
                    case None =>
                        fieldTable.update(field, methodLevel)
                }
                case (field: VariableElement, false) if field.getKind == ElementKind.FIELD => fieldTable.get(field) match {
                    case None => fieldTable.update(field, AnnotationBuilder.fromClass(atypeFactory.getElementUtils, classOf[Local]))
                    case _ =>
                }
                case _ =>
            }
            case _ =>
        }
    }

    private def hasAnnotation(modifiers: ModifiersTree, annotation: String): Boolean = {
        modifiers.getAnnotations.exists((at: AnnotationTree) => atypeFactory.getAnnotatedType(at.getAnnotationType) match {
            case adt: AnnotatedDeclaredType =>
                getQualifiedName(adt) == annotation
            case _ =>
                false
        })
    }

    def buildQualifierMap(): Map[String, String] =
        atypeFactory.getSupportedTypeQualifiers.
            map(q => atypeFactory.getAnnotatedType(q) match {
                case adt: AnnotatedDeclaredType => adt.getUnderlyingType.asElement
                case _ => null
            }).
            filter(x => x != null).
            foldLeft(Map.empty[String, String])((map, elt) => {
                atypeFactory.getAnnotationByClass(elt.getAnnotationMirrors, classOf[QualifierForOperation]) match {
                    case null => map
                    case annotation =>
                        val value = annotation.getElementValues.values().head
                        map + (value.getValue.toString -> elt.toString)
                }
            })
}
