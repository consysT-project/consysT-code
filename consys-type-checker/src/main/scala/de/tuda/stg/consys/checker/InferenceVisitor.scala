package de.tuda.stg.consys.checker

import com.sun.source.tree.{AnnotationTree, AssignmentTree, ClassTree, CompoundAssignmentTree, ExpressionTree, IdentifierTree, MemberSelectTree, MethodTree, ModifiersTree, Tree, VariableTree}
import com.sun.source.util.TreeScanner
import de.tuda.stg.consys.checker.TypeFactoryUtils.{getDefaultOp, getExplicitAnnotation, getQualifiedName}
import de.tuda.stg.consys.checker.qual.{Local, Mixed, QualifierForOperation}
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.AnnotatedDeclaredType
import org.checkerframework.javacutil.{AnnotationBuilder, ElementUtils, TreeUtils}

import java.lang.annotation.Annotation
import javax.lang.model.`type`.DeclaredType
import javax.lang.model.element.{AnnotationMirror, ElementKind, TypeElement, VariableElement}
import scala.collection.convert.ImplicitConversions.`collection AsScalaIterable`
import scala.collection.mutable

class InferenceVisitor(atypeFactory: ConsistencyAnnotatedTypeFactory) extends TreeScanner[Void, Boolean] {

    // TODO: switch the keys to strings for performance?
    type InferenceTable = mutable.Map[(TypeElement, String, VariableElement), AnnotationMirror]

    var inferenceTable: InferenceTable = mutable.Map.empty

    /**
     * Stores each field read tree and the operation level of the method it occurs in
     */
    var refinementTable: mutable.Map[Tree, AnnotationMirror] = mutable.Map.empty

    private var annoMapping: Map[String, String] = Map.empty

    private var classContext: Option[TypeElement] = Option.empty
    private var defaultOpLevel: Option[String] = Option.empty
    private var methodContext: Option[AnnotationMirror] = Option.empty


    override def visitClass(node: ClassTree, isLHS: Boolean): Void = {
        if (annoMapping.isEmpty)
            annoMapping = buildQualifierMap()

        if (classContext.isDefined && classContext.get.equals(TreeUtils.elementFromDeclaration(node)))
            return null

        val prev = (classContext, defaultOpLevel)
        var r: Void = null
        classContext = Option(TreeUtils.elementFromDeclaration(node))

        (getAnnotationMirror(node, classOf[Mixed]), defaultOpLevel) match {
            case (Some(annotation), _) =>
                defaultOpLevel = Some(getDefaultOp(annotation))
                getSuperclassElement(node) match {
                    case Some(elt) =>
                        val superclassTree = getSourceOfElement(elt)
                        if (superclassTree != null) {
                            visitClass(superclassTree, isLHS)
                            atypeFactory.processClassWithoutCache(superclassTree, defaultOpLevel.get)
                        } else {
                            visitClass(elt, isLHS)
                        }
                    case None =>
                }
                r = super.visitClass(node, isLHS)

            case (None, Some(_)) =>
                getSuperclassElement(node) match {
                    case Some(elt) =>
                        val superclassTree = getSourceOfElement(elt)
                        if (superclassTree != null) {
                            visitClass(superclassTree, isLHS)
                            atypeFactory.processClassWithoutCache(superclassTree, defaultOpLevel.get)
                        } else {
                            visitClass(elt, isLHS)
                        }
                    case None =>
                }
                r = super.visitClass(node, isLHS)

            case (None, None) =>
        }

        classContext = prev._1
        defaultOpLevel = prev._2
        r
    }

    // TODO: combine duplicate code
    def visitClass(decl: TypeElement, isLHS: Boolean): Void = {
        if (annoMapping.isEmpty)
            annoMapping = buildQualifierMap()

        if (classContext.isDefined && classContext.get.equals(decl))
            return null

        val prev = (classContext, defaultOpLevel)
        var r: Void = null
        classContext = Option(decl)

        (getAnnotationMirror(decl, classOf[Mixed]), defaultOpLevel) match {
            case (Some(annotation), _) =>
                defaultOpLevel = Some(getDefaultOp(annotation))
                getSuperclassElement(decl) match {
                    case Some(elt) =>
                        val superclassTree = getSourceOfElement(elt)
                        if (superclassTree != null) {
                            visitClass(superclassTree, isLHS)
                            atypeFactory.processClassWithoutCache(superclassTree, defaultOpLevel.get)
                        } else {
                            visitClass(elt, isLHS)
                        }
                    case None =>
                }
                processClassDeclaration(decl)

            case (None, Some(_)) =>
                getSuperclassElement(decl) match {
                    case Some(elt) =>
                        val superclassTree = getSourceOfElement(elt)
                        if (superclassTree != null) {
                            visitClass(superclassTree, isLHS)
                            atypeFactory.processClassWithoutCache(superclassTree, defaultOpLevel.get)
                        } else {
                            visitClass(elt, isLHS)
                        }
                    case None =>
                }
                processClassDeclaration(decl)

            case (None, None) =>
        }

        classContext = prev._1
        defaultOpLevel = prev._2
        r
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

    private def processField(node: ExpressionTree, isLhs: Boolean): Unit =
        (methodContext, TreeUtils.elementFromUse(node)) match {
            case (Some(methodLevel), field: VariableElement)
                if field.getKind == ElementKind.FIELD
                    && ElementUtils.getAllFieldsIn(classContext.get, atypeFactory.getElementUtils).contains(field) =>

                getExplicitAnnotation(atypeFactory, field) match {
                    case Some(explicitAnnotation) if isLhs && !atypeFactory.getQualifierHierarchy.isSubtype(methodLevel, explicitAnnotation) =>
                        atypeFactory.getChecker.reportError(node, "mixed.field.incompatible",
                            explicitAnnotation.getAnnotationType.asElement().getSimpleName,
                            methodLevel.getAnnotationType.asElement().getSimpleName)

                    case None =>
                        updateField(classContext.get, defaultOpLevel.get, field, methodLevel, isLhs, node)

                    case _ =>
                }

                if (!isLhs) {
                    refinementTable.update(node, methodLevel)
                }
            case _ =>
        }

    private def updateField(clazz: TypeElement, defaultOp: String, field: VariableElement, annotation: AnnotationMirror, isLHS: Boolean, source: AnyRef): Unit = {
        if (field.getKind != ElementKind.FIELD)
            return

        (getInferredFieldOrFromSuperclass(field, clazz, defaultOp), isLHS) match {
            case ((Some(fieldLevel), d), true) if d == 0 =>
                val lup = atypeFactory.getQualifierHierarchy.leastUpperBound(fieldLevel, annotation)
                inferenceTable.update((clazz, defaultOp, field), lup)
            case ((Some(fieldLevel), d), true) if d > 0 =>
                val lup = atypeFactory.getQualifierHierarchy.leastUpperBound(fieldLevel, annotation)
                if (atypeFactory.getQualifierHierarchy.isSubtype(annotation, lup))
                    atypeFactory.getChecker.reportError(source, "inheritance.incorrect.lup")
            case ((None, _), true) =>
                inferenceTable.update((clazz, defaultOp, field), annotation)
            case ((None, _), false) =>
                inferenceTable.update((clazz, defaultOp, field), AnnotationBuilder.fromClass(atypeFactory.getElementUtils, classOf[Local]))
            case _ =>
        }
    }

    private def processClassDeclaration(elt: TypeElement): Unit = {
        val fields = elt.getEnclosedElements.filter({
            case _: VariableElement => true
            case _ => false
        })
        val level = AnnotationBuilder.fromName(atypeFactory.getElementUtils, annoMapping.apply(defaultOpLevel.get))
        fields.foreach(f => updateField(classContext.get, defaultOpLevel.get, f.asInstanceOf[VariableElement], level, isLHS = true, f))
    }

    def getInferredFieldOrFromSuperclass(field: VariableElement, clazz: TypeElement, defaultOpLevel: String): (Option[AnnotationMirror], Int) =
        inferenceTable.get(clazz, defaultOpLevel, field) match {
            case value: Some[AnnotationMirror] => (value, 0)
            case None => getSuperclassElement(clazz) match {
                case Some(superclass) =>
                    val (result, depth) = getInferredFieldOrFromSuperclass(field, superclass, defaultOpLevel)
                    (result, depth + 1)
                case None => (None, 0)
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

    private def getAnnotationMirror(tree: Tree, annotation: Class[_ <: Annotation]): Option[AnnotationMirror] =
        atypeFactory.getAnnotatedType(tree).getAnnotation(annotation) match {
            case null => None
            case value => Some(value)
        }

    private def getAnnotationMirror(element: TypeElement, annotation: Class[_ <: Annotation]): Option[AnnotationMirror] =
        atypeFactory.getAnnotatedType(element).getAnnotation(annotation) match {
            case null => None
            case value => Some(value)
        }

    private def getSuperclassElement(elt: TypeElement): Option[TypeElement] =
        elt.getSuperclass match {
            case dt: DeclaredType => dt.asElement().getKind match {
                case ElementKind.CLASS => Some(dt.asElement().asInstanceOf[TypeElement])
                case _ => None // TODO: when could this happen?
            }
            case _ => None
        }

    private def getSuperclassElement(classTree: ClassTree): Option[TypeElement] =
        getSuperclassElement(TreeUtils.elementFromDeclaration(classTree))

    private def getSourceOfElement(elt: TypeElement): ClassTree = atypeFactory.getTreeUtils.getTree(elt)

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
