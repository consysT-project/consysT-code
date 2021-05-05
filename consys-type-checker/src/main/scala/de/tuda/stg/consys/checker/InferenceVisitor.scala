package de.tuda.stg.consys.checker

import com.sun.source.tree.{AnnotationTree, AssignmentTree, ClassTree, CompoundAssignmentTree, ExpressionTree, IdentifierTree, MemberSelectTree, MethodTree, ModifiersTree, Tree, VariableTree}
import com.sun.source.util.TreeScanner
import de.tuda.stg.consys.checker.TypeFactoryUtils.{annoPackageName, checkerPackageName, getQualifiedName}
import de.tuda.stg.consys.checker.qual.{Local, Mixed, QualifierForOperation}
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.AnnotatedDeclaredType
import org.checkerframework.framework.`type`.GenericAnnotatedTypeFactory
import org.checkerframework.javacutil.{AnnotationBuilder, AnnotationUtils, ElementUtils, TreeUtils, TypesUtils}

import java.lang.annotation.Annotation
import javax.lang.model.`type`.DeclaredType
import javax.lang.model.element.{AnnotationMirror, AnnotationValue, ElementKind, TypeElement, VariableElement}
import scala.collection.convert.ImplicitConversions.`collection AsScalaIterable`
import scala.collection.mutable

class InferenceVisitor(atypeFactory: GenericAnnotatedTypeFactory[_, _, _, _]) extends TreeScanner[Void, Boolean] {

    // TODO: switch the keys to strings for performance
    type InferenceTable = mutable.Map[(TypeElement, VariableElement), AnnotationMirror]

    var inferenceTable: InferenceTable = mutable.Map.empty

    private var annoMapping: Map[String, String] = Map.empty

    private var classContext: Option[TypeElement] = Option.empty
    private var defaultOpLevel: Option[String] = Option.empty
    private var methodContext: Option[AnnotationMirror] = Option.empty


    override def visitClass(node: ClassTree, p: Boolean): Void = {
        if (annoMapping.isEmpty)
            annoMapping = buildQualifierMap()

        if (classContext.isDefined && classContext.get.equals(TreeUtils.elementFromDeclaration(node)))
            return null

        val prev = (classContext, defaultOpLevel)
        classContext = Option(TreeUtils.elementFromDeclaration(node))

        val adt = atypeFactory.getAnnotatedType(node)
        val mixed = adt.getAnnotation(classOf[Mixed])
        if (mixed != null) {
            TreeUtils.elementFromDeclaration(node).getSuperclass match {
                case dt: DeclaredType =>
                    val superclassTree = atypeFactory.getTreeUtils.getTree(dt.asElement().asInstanceOf[TypeElement])
                    // TODO: null when superclass not found -> possible causes?
                    if (superclassTree != null) {
                        visitClass(superclassTree, p)
                    }
                case _ =>
            }

            val a = atypeFactory.getAnnotatedType(node).getAnnotation(classOf[Mixed])
            //defaultOpLevel = Some(AnnotationBuilder.fromClass(
            //    atypeFactory.getElementUtils, a.getElementValues.values().head.getValue.asInstanceOf[Class[_ <: Annotation]]))
            defaultOpLevel = Some(AnnotationUtils.getElementValuesWithDefaults(a).values().head.getValue.toString)

            val r = super.visitClass(node, p)
            classContext = prev._1
            defaultOpLevel = prev._2
            r
        } else {
            classContext = prev._1
            defaultOpLevel = prev._2
            null
        }
    }

    override def visitMethod(node: MethodTree, isLHS: Boolean): Void = {
        if (classContext.nonEmpty) {
            annoMapping.foreach(mapping => {
                val (operation, qualifier) = mapping
                if (hasAnnotation(node.getModifiers, operation)) {
                    methodContext = Option(AnnotationBuilder.fromName(atypeFactory.getElementUtils, qualifier))
                    // TODO: handle case if more than one annotation given
                }
            })
            if (methodContext.isEmpty) {
                methodContext = Some(AnnotationBuilder.fromName(atypeFactory.getElementUtils, annoMapping.apply(defaultOpLevel.get)))
            }

            val r = super.visitMethod(node, isLHS)
            methodContext = Option.empty
            r
        } else {
            null
        }
    }

    override def visitAssignment(node: AssignmentTree, isLhs: Boolean): Void = {
        var r = scan(node.getVariable, true)
        r = reduce(scan(node.getExpression, false), r)
        r
    }

    override def visitCompoundAssignment(node: CompoundAssignmentTree, isLhs: Boolean): Void = {
        var r = scan(node.getVariable, true)
        r = reduce(scan(node.getExpression, false), r)
        r
    }

    // TODO: are there more tree types for field use other than IdentifierTree and MemberSelect?
    override def visitMemberSelect(node: MemberSelectTree, isLhs: Boolean): Void = {
        processField(node, isLhs)
        super.visitMemberSelect(node, isLhs)
    }

    override def visitIdentifier(node: IdentifierTree, isLhs: Boolean): Void = {
        processField(node, isLhs)
        super.visitIdentifier(node, isLhs)
    }

    private def processField(node: ExpressionTree, isLhs: Boolean): Unit = {
        // TODO: check if ID belongs to this class
        methodContext match {
            case Some(methodLevel) => (TreeUtils.elementFromUse(node), isLhs) match {
                case (field: VariableElement, true) if field.getKind == ElementKind.FIELD => getInferredFieldOrFromSuperclass(field, classContext.get) match {
                    case Some(fieldLevel) =>
                        val lup = atypeFactory.getQualifierHierarchy.leastUpperBound(fieldLevel, methodLevel)
                        inferenceTable.update((classContext.get, field), lup)
                    case None =>
                        inferenceTable.update((classContext.get, field), methodLevel)
                }
                case (field: VariableElement, false) if field.getKind == ElementKind.FIELD => getInferredFieldOrFromSuperclass(field, classContext.get) match {
                    case None => inferenceTable.update((classContext.get, field), AnnotationBuilder.fromClass(atypeFactory.getElementUtils, classOf[Local]))
                    case _ =>
                }
                case _ =>
            }
            case _ =>
        }
    }

    def getInferredFieldOrFromSuperclass(field: VariableElement, clazz: TypeElement): Option[AnnotationMirror] =
        inferenceTable.get(clazz, field) match {
            case value: Some[AnnotationMirror] => value
            case None => clazz.getSuperclass match {
                case superclass: DeclaredType =>
                    getInferredFieldOrFromSuperclass(field, superclass.asElement().asInstanceOf[TypeElement])
                case _ => None
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

    def getClassContext: Option[TypeElement] = classContext
}
