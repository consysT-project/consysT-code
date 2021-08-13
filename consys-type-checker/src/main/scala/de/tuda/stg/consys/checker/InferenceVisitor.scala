package de.tuda.stg.consys.checker

import com.sun.source.tree.{AnnotationTree, AssignmentTree, ClassTree, CompoundAssignmentTree, ExpressionTree, IdentifierTree, MemberSelectTree, MethodInvocationTree, MethodTree, ModifiersTree, Tree, VariableTree}
import com.sun.source.util.TreeScanner
import de.tuda.stg.consys.annotations.ReadOnly
import de.tuda.stg.consys.checker.InferenceVisitor.{DefaultOpLevel, LHS, RHS, State}
import de.tuda.stg.consys.checker.TypeFactoryUtils.{getExplicitAnnotation, getMixedDefaultOp, getQualifiedName, getQualifierForOp, getQualifierForOpMap, getQualifierNameForOp}
import de.tuda.stg.consys.checker.qual.{Local, Mixed, QualifierForOperation}
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.AnnotatedDeclaredType
import org.checkerframework.javacutil.{AnnotationBuilder, ElementUtils, TreeUtils}

import java.lang.annotation.Annotation
import javax.lang.model.`type`.DeclaredType
import javax.lang.model.element
import javax.lang.model.element.{AnnotationMirror, ElementKind, Modifier, TypeElement, VariableElement}
import scala.collection.convert.ImplicitConversions.`collection AsScalaIterable`
import scala.collection.mutable

object InferenceVisitor {
    sealed trait AssignmentSide

    case object LHS extends AssignmentSide

    case object RHS extends AssignmentSide

    type DefaultOpLevel = String
    type State = (Option[TypeElement], Option[DefaultOpLevel], Option[AnnotationMirror], Option[AssignmentSide])
}

class InferenceVisitor(implicit atypeFactory: ConsistencyAnnotatedTypeFactory) extends TreeScanner[Void, State] {

    // TODO: switch the keys to strings for performance?
    type InferenceTable = mutable.Map[(TypeElement, String), mutable.Map[VariableElement, AnnotationMirror]]
    var inferenceTable: InferenceTable = mutable.Map.empty

    /**
     * Stores each field read tree and the operation level of the method it occurs in
     */
    var refinementTable: mutable.Map[Tree, AnnotationMirror] = mutable.Map.empty
    private var currentClass: Option[TypeElement] = None

    def visitClass(node: ClassTree): Unit = visitClass(node, (None, None, None, None))

    def visitClass(decl: TypeElement): Unit = visitClass(decl, (None, None, None, None))

    override def visitClass(node: ClassTree, state: State): Void = {
        val classDecl = TreeUtils.elementFromDeclaration(node)
        if (currentClass.isDefined && classDecl == currentClass.get)
            return null
        currentClass = Some(classDecl)

        var (_, defaultOpLevel, _, _) = state

        (getAnnotationMirror(node, classOf[Mixed]), defaultOpLevel) match {
            case (None, None) =>
                currentClass = None
                return null
            case (Some(annotation), _) =>
                defaultOpLevel = Some(getMixedDefaultOp(annotation))
            case (None, Some(_)) =>
        }

        if (inferenceTable.contains((classDecl, defaultOpLevel.get))) {
            currentClass = None
            return null
        }

        inferenceTable.put((classDecl, defaultOpLevel.get), mutable.Map.empty)
        val newState = (Some(classDecl), defaultOpLevel, None, None)
        checkSuperclass(getSuperclassElement(node), newState)
        processPublicFields(newState)

        val r = super.visitClass(node, newState)
        currentClass = None
        r
    }

    // TODO: combine duplicate code
    def visitClass(classDecl: TypeElement, state: State): Void = {
        if (currentClass.isDefined && classDecl == currentClass.get)
            return null
        currentClass = Some(classDecl)

        var (_, defaultOpLevel, _, _) = state

        (getAnnotationMirror(classDecl, classOf[Mixed]), defaultOpLevel) match {
            case (None, None) =>
                currentClass = None
                return null
            case (Some(annotation), _) =>
                defaultOpLevel = Some(getMixedDefaultOp(annotation))
            case (None, Some(_)) =>
        }

        if (inferenceTable.contains((classDecl, defaultOpLevel.get))) {
            currentClass = None
            return null
        }

        inferenceTable.put((classDecl, defaultOpLevel.get), mutable.Map.empty)
        val newState = (Some(classDecl), defaultOpLevel, None, None)
        checkSuperclass(getSuperclassElement(classDecl), newState)

        processClassDeclaration(classDecl, state)
        currentClass = None
        null
    }

    private def checkSuperclass(superclass: Option[TypeElement], state: State): Unit = {
        val (_, Some(defaultOpLevel), _, _) = state
        superclass match {
            case Some(elt) =>
                val superclassTree = getSourceOfElement(elt)
                if (superclassTree != null) {
                    visitClass(superclassTree, state)
                    atypeFactory.processClassWithoutCache(superclassTree, defaultOpLevel)
                } else {
                    visitClass(elt, state)
                }
            case None =>
        }
    }

    private def processPublicFields(state: State): Unit = {
        val (Some(clazz), Some(defaultOp), _, _) = state
        // set public and package fields to the default level
        ElementUtils.getAllFieldsIn(clazz, atypeFactory.getElementUtils).
            filter(field => !(field.getModifiers.contains(Modifier.PRIVATE) ||
                field.getModifiers.contains(Modifier.PROTECTED))).
            foreach(field => updateField(field, (Some(clazz), Some(defaultOp), getQualifierForOp(defaultOp), Some(LHS)), field))
    }

    override def visitMethod(node: MethodTree, state: State): Void = {
        if (TreeUtils.isConstructor(node))
            return null

        val (classContext, Some(defaultOpLevel), _, _) = state
        var methodLevel: Option[AnnotationMirror] = None

        // try to find an explicit supported op level on the method
        getQualifierForOpMap.foreach(mapping => {
            val (operation, qualifier) = mapping
            if (TypeFactoryUtils.hasAnnotation(atypeFactory, node.getModifiers, operation)) {
                methodLevel match {
                    case None =>
                        methodLevel = Option(AnnotationBuilder.fromName(atypeFactory.getElementUtils, qualifier))
                    case _ => // TODO: handle case if more than one annotation given
                }
            }
        })

        if (methodLevel.isEmpty) {
            getQualifierNameForOp(defaultOpLevel) match {
                case Some(qualifier) =>
                    methodLevel = Some(AnnotationBuilder.fromName(atypeFactory.getElementUtils, qualifier))
                case None => // TODO: handle case where given default operation level is not valid
            }
        }

        super.visitMethod(node, (classContext, Some(defaultOpLevel), methodLevel, None))
    }

    override def visitAssignment(node: AssignmentTree, state: State): Void = {
        val (clazz, defaultOpLevel, methodLevel, _) = state
        var r = scan(node.getVariable, (clazz, defaultOpLevel, methodLevel, Some(LHS)))
        r = reduce(scan(node.getExpression, (clazz, defaultOpLevel, methodLevel, Some(RHS))), r)
        r
    }

    override def visitCompoundAssignment(node: CompoundAssignmentTree, state: State): Void = {
        val (clazz, defaultOpLevel, methodLevel, _) = state
        var r = scan(node.getVariable, (clazz, defaultOpLevel, methodLevel, Some(LHS)))
        r = reduce(scan(node.getExpression, (clazz, defaultOpLevel, methodLevel, Some(RHS))), r)
        r
    }

    override def visitMethodInvocation(node: MethodInvocationTree, state: State): Void = {
        val (clazz, defaultOpLevel, methodLevel, _) = state
        val method = TreeUtils.elementFromUse(node)
        if (method.getAnnotation(classOf[ReadOnly]) != null)
            super.visitMethodInvocation(node, (clazz, defaultOpLevel, methodLevel, Some(RHS)))
        else
            super.visitMethodInvocation(node, (clazz, defaultOpLevel, methodLevel, Some(LHS)))
    }

    // TODO: are there more tree types for field use other than IdentifierTree and MemberSelect?
    override def visitMemberSelect(node: MemberSelectTree, state: State): Void = {
        processField(node, state)
        super.visitMemberSelect(node, state)
    }

    override def visitIdentifier(node: IdentifierTree, state: State): Void = {
        processField(node, state)
        super.visitIdentifier(node, state)
    }

    private def processField(node: ExpressionTree, state: State): Unit = {
        val (classContext, _, methodContext, _) = state

        (methodContext, TreeUtils.elementFromUse(node)) match {
            case (Some(methodLevel), field: VariableElement)
                if field.getKind == ElementKind.FIELD
                    && ElementUtils.getAllFieldsIn(classContext.get, atypeFactory.getElementUtils).contains(field) =>

                (getExplicitAnnotation(atypeFactory, field), state._4) match {
                    case (Some(explicitAnnotation), Some(LHS)) if !atypeFactory.getQualifierHierarchy.isSubtype(methodLevel, explicitAnnotation) =>
                        atypeFactory.getChecker.reportError(node, "mixed.field.incompatible",
                            explicitAnnotation.getAnnotationType.asElement().getSimpleName,
                            methodLevel.getAnnotationType.asElement().getSimpleName)

                    case (None, _) =>
                        updateField(field, state, node)

                    case _ =>
                }

                state match {
                    case (_, _, _, Some(LHS)) =>
                    case _ => refinementTable.update(node, methodLevel)
                }
            case _ =>
        }
    }

    private def updateField(field: VariableElement, state: State, source: AnyRef): Unit = {
        if (field.getKind != ElementKind.FIELD)
            return

        val (Some(clazz), Some(defaultOp), Some(annotation), side) = state

        (getInferredFieldOrFromSuperclass(field, clazz, defaultOp), side) match {
            case ((Some(fieldLevel), depth), Some(LHS)) if depth == 0 =>
                val lup = atypeFactory.getQualifierHierarchy.leastUpperBound(fieldLevel, annotation)
                inferenceTable.apply(clazz, defaultOp).update(field, lup)
            case ((Some(fieldLevel), depth), Some(LHS)) if depth > 0 =>
                // TODO: Do we need extra considerations for Mixed objects here?
                // checks if field level is a (non-reflexive) subtype of method level, i.e. if field would be weakened
                if (!atypeFactory.getQualifierHierarchy.isSubtype(annotation, fieldLevel))
                    atypeFactory.getChecker.reportError(source, "mixed.inheritance.field.overwrite",
                        fieldLevel, field.getSimpleName, annotation, source)
            case ((None, _), Some(LHS)) =>
                inferenceTable.apply(clazz, defaultOp).update(field, annotation)
            case ((None, _), Some(RHS)) =>
                inferenceTable.apply(clazz, defaultOp).update(field,
                    AnnotationBuilder.fromClass(atypeFactory.getElementUtils, classOf[Local]))
            case _ =>
        }
    }

    private def processClassDeclaration(elt: TypeElement, state: State): Unit = {
        val fields = elt.getEnclosedElements.filter({
            case _: VariableElement => true
            case _ => false
        })

        val (_, defaultOpLevel, _, _) = state
        getQualifierNameForOp(defaultOpLevel.get) match {
            case Some(qualifier) =>
                val level = AnnotationBuilder.fromName(atypeFactory.getElementUtils, qualifier)
                fields.foreach(f => {
                    updateField(f.asInstanceOf[VariableElement], (Some(elt), defaultOpLevel, Some(level), Some(LHS)), f)
                })

            case None => // TODO: handle case where given default operation level is not valid
        }
    }

    def getInferredFieldOrFromSuperclass(field: VariableElement, clazz: TypeElement, defaultOpLevel: String): (Option[AnnotationMirror], Int) = {
        inferenceTable.get(clazz, defaultOpLevel) match {
            case Some(map) => map.get(field) match {
                case value: Some[AnnotationMirror] =>
                    (value, 0)
                case None => getSuperclassElement(clazz) match {
                    case Some(superclass) =>
                        val (result, depth) = getInferredFieldOrFromSuperclass(field, superclass, defaultOpLevel)
                        /* TODO: if result is Local, then level should be determined by derived class:
                                 store the base class variable's level as undefined, if the base class does not write it
                                 and differentiate use in base class (-> Local) and use in derived classes
                                 (-> next defined use in class hierarchy). Shadowed fields may pose a problem
                         */
                        (result, depth + 1)
                    case None =>
                        (None, 0)
                }
            }
            case None => (None, 0)
        }
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
}
