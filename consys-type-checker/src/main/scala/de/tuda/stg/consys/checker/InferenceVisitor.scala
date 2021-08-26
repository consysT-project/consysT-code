package de.tuda.stg.consys.checker

import com.sun.source.tree._
import com.sun.source.util.TreeScanner
import de.tuda.stg.consys.checker.InferenceVisitor.{AnnotationName, ClassName, DefaultOpLevel, FieldName, LHS, RHS, State}
import de.tuda.stg.consys.checker.TypeFactoryUtils._
import de.tuda.stg.consys.checker.qual.{Inconsistent, Local, Mixed}
import org.checkerframework.dataflow.qual.{Pure, SideEffectFree}
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.AnnotatedDeclaredType
import org.checkerframework.javacutil.{AnnotationBuilder, AnnotationUtils, ElementUtils, TreeUtils}

import java.lang.annotation.Annotation
import java.util.Collections
import javax.lang.model.`type`.{DeclaredType, TypeKind}
import javax.lang.model.element.{AnnotationMirror, ElementKind, ExecutableElement, Modifier, TypeElement, VariableElement}
import scala.collection.convert.ImplicitConversions.`collection AsScalaIterable`
import scala.collection.mutable

object InferenceVisitor {
    sealed trait AssignmentSide

    case object LHS extends AssignmentSide

    case object RHS extends AssignmentSide

    type DefaultOpLevel = String
    type ClassName = String
    type FieldName = String
    type AnnotationName = String
    type State = (Option[TypeElement], Option[DefaultOpLevel], Option[AnnotationMirror], Option[AssignmentSide])
}

class InferenceVisitor(implicit atypeFactory: ConsistencyAnnotatedTypeFactory) extends TreeScanner[Void, State] {

    type InferenceTable = mutable.Map[(ClassName, DefaultOpLevel), mutable.Map[FieldName, AnnotationName]]
    var inferenceTable: InferenceTable = mutable.Map.empty

    /**
     * Stores each field read tree and the operation level of the method it occurs in
     */
    var refinementTable: mutable.Map[Tree, AnnotationMirror] = mutable.Map.empty
    private var currentClass: Option[TypeElement] = None

    def processClass(node: ClassTree, annotation: AnnotationMirror): Unit =
        processClass(node, (None, Some(getMixedDefaultOp(annotation)), None, None))

    def processClass(decl: TypeElement, annotation: AnnotationMirror): Unit =
        processClass(decl, (None, Some(getMixedDefaultOp(annotation)), None, None))

    def processClass(node: ClassTree, state: State): Void = {
        val classDecl = TreeUtils.elementFromDeclaration(node)
        if (currentClass.isDefined && classDecl == currentClass.get)
            return null
        currentClass = Some(classDecl)

        var (_, defaultOpLevel, _, _) = state

        if (defaultOpLevel.isEmpty)
            sys.error("inference")
        // TODO: should we rather not try to get the default from the node?
        /*
        (getAnnotationMirror(node, classOf[Mixed]), defaultOpLevel) match {
            case (None, None) =>
                currentClass = None
                return null
            case (Some(annotation), _) =>
                defaultOpLevel = Some(getMixedDefaultOp(annotation))
            case (None, Some(_)) =>
        }*/

        if (inferenceTable.contains((classDecl.getQualifiedName.toString, defaultOpLevel.get))) {
            currentClass = None
            return null
        }

        inferenceTable.put((classDecl.getQualifiedName.toString, defaultOpLevel.get), mutable.Map.empty)
        val newState = (Some(classDecl), defaultOpLevel, None, None)

        checkSuperclass(getSuperclassElement(node), newState)
        processPublicFields(newState)
        processExplicitFields(newState)
        processStaticFields(newState)
        val r = super.visitClass(node, newState)
        processUnusedFields(newState)

        atypeFactory.returnTypeVisitor.processClass(node,
            AnnotationBuilder.fromClass(atypeFactory.getElementUtils, classOf[Mixed],
                AnnotationBuilder.elementNamesValues("value", Class.forName(defaultOpLevel.get))))

        currentClass = None
        r
    }

    // TODO: combine duplicate code
    def processClass(classDecl: TypeElement, state: State): Void = {
        if (currentClass.isDefined && classDecl == currentClass.get)
            return null
        currentClass = Some(classDecl)

        var (_, defaultOpLevel, _, _) = state

        if (defaultOpLevel.isEmpty)
            sys.error("inference")
        /*
        (getAnnotationMirror(classDecl, classOf[Mixed]), defaultOpLevel) match {
            case (None, None) =>
                currentClass = None
                return null
            case (Some(annotation), _) =>
                defaultOpLevel = Some(getMixedDefaultOp(annotation))
            case (None, Some(_)) =>
        }
        */

        if (inferenceTable.contains((classDecl.getQualifiedName.toString, defaultOpLevel.get))) {
            currentClass = None
            return null
        }

        inferenceTable.put((classDecl.getQualifiedName.toString, defaultOpLevel.get), mutable.Map.empty)
        val newState = (Some(classDecl), defaultOpLevel, None, Some(RHS))
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
                    processClass(superclassTree, state)
                    atypeFactory.getVisitor.visitOrQueueClassTree(superclassTree,
                        AnnotationBuilder.fromClass(atypeFactory.getElementUtils, classOf[Mixed],
                            AnnotationBuilder.elementNamesValues("value", Class.forName(defaultOpLevel))))
                    // TODO: cache annotationmirror
                } else {
                    processClass(elt, state)
                }
            case None =>
        }
    }

    private def processPublicFields(state: State): Unit = {
        val (Some(clazz), Some(defaultOp), _, _) = state
        val isNestedClass = clazz.getEnclosingElement match {
            case _: TypeElement => true
            case _ => false
        }

        // set public and package fields to the default level,
        // or, for nested classes, do this for all levels
        getOwnFields(clazz).
            filter(field => isNestedClass || !(field.getModifiers.contains(Modifier.PRIVATE) ||
                field.getModifiers.contains(Modifier.PROTECTED))).
            foreach(field => updateField(field, (Some(clazz), Some(defaultOp), getQualifierForOp(defaultOp), Some(LHS)), field))
        // TODO: check for explicit annotations
    }

    private def processUnusedFields(state: State): Unit = {
        val (Some(clazz), Some(defaultOp), _, _) = state
        // set all unused unannotated fields to Local
        getOwnFields(clazz).
            filter(field => !inferenceTable.get(clazz.getQualifiedName.toString, defaultOp).get.
                contains(getQualifiedName(field)) && getExplicitAnnotation(field).isEmpty).
            foreach(field => updateField(field, (Some(clazz), Some(defaultOp), Some(localAnnotation), Some(LHS)), field))
    }

    private def processStaticFields(state: State): Unit = {
        val (Some(clazz), Some(defaultOp), _, _) = state
        // set all static fields to Inconsistent and check for forbidden explicit annotations
        getOwnFields(clazz).
            filter(field => field.getModifiers.contains(Modifier.STATIC)).
            foreach(field => {
                getExplicitAnnotation(field) match {
                    case Some(value) if !atypeFactory.areSameByClass(value, classOf[Inconsistent]) =>
                        atypeFactory.getChecker.reportError(field, "mixed.field.static.incompatible")
                    case _ =>
                }
                updateField(field, (Some(clazz), Some(defaultOp), Some(inconsistentAnnotation), Some(LHS)), field)
            })
    }

    private def processExplicitFields(state: State): Unit = {
        val (Some(clazz), Some(defaultOp), _, _) = state

        getOwnFields(clazz).foreach(field => getExplicitAnnotation(field) match {
                case Some(annotation) => inferenceTable.apply(clazz.getQualifiedName.toString, defaultOp).
                    update(getQualifiedName(field), getQualifiedName(annotation))
                case None =>
        })
    }

    override def visitMethod(node: MethodTree, state: State): Void = {
        // ignore constructors and static methods
        if (TreeUtils.isConstructor(node) || node.getModifiers.getFlags.contains(Modifier.STATIC))
            return null

        val (classContext, Some(defaultOpLevel), _, side) = state
        var methodLevel: Option[AnnotationMirror] = None

        // try to find an explicit supported op level on the method
        getQualifierForOpMap.foreach(mapping => {
            val (operation, qualifier) = mapping
            if (hasAnnotation(node.getModifiers, operation)) {
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

        super.visitMethod(node, (classContext, Some(defaultOpLevel), methodLevel, side))
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
        if (method.getAnnotation(classOf[SideEffectFree]) != null || method.getAnnotation(classOf[Pure]) != null)
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
        val (classContext, _, methodContext, side) = state

        (methodContext, TreeUtils.elementFromUse(node)) match {
            case (Some(methodLevel), field: VariableElement)
                if field.getKind == ElementKind.FIELD // ignore element if it is a field of a field
                    && ElementUtils.getAllFieldsIn(classContext.get, atypeFactory.getElementUtils).contains(field) =>

                (getExplicitAnnotation(field), side) match {
                    // check compatibility between explicit type and operation level
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
                inferenceTable.apply(clazz.getQualifiedName.toString, defaultOp).update(getQualifiedName(field), getQualifiedName(lup))
            case ((Some(fieldLevel), depth), Some(LHS)) if depth > 0 =>
                // checks if field level is a (non-reflexive) subtype of method level, i.e. if field would be weakened
                if (!atypeFactory.getQualifierHierarchy.isSubtype(annotation, fieldLevel))
                    atypeFactory.getChecker.reportError(source, "mixed.inheritance.field.overwrite",
                        fieldLevel, field.getSimpleName, annotation, source)
            case ((None, _), Some(LHS)) =>
                inferenceTable.apply(clazz.getQualifiedName.toString, defaultOp).update(getQualifiedName(field), getQualifiedName(annotation))
            case ((None, _), Some(RHS)) =>
                inferenceTable.apply(clazz.getQualifiedName.toString, defaultOp).update(getQualifiedName(field), classOf[Local].getCanonicalName)
            case _ =>
        }
    }

    private def processClassDeclaration(elt: TypeElement, state: State): Unit = {
        val fields = getOwnFields(elt)

        val (_, defaultOpLevel, _, _) = state
        getQualifierNameForOp(defaultOpLevel.get) match {
            case Some(qualifier) =>
                val level = AnnotationBuilder.fromName(atypeFactory.getElementUtils, qualifier)
                fields.foreach(f => {
                    updateField(f, (Some(elt), defaultOpLevel, Some(level), Some(LHS)), f)
                })

            case None => // TODO: handle case where given default operation level is not valid
        }
    }

    def getInferredFieldOrFromSuperclass(field: VariableElement, clazz: TypeElement, defaultOpLevel: String): (Option[AnnotationMirror], Int) = {
        inferenceTable.get(clazz.getQualifiedName.toString, defaultOpLevel) match {
            case Some(map) => map.get(getQualifiedName(field)) match {
                case Some(name) =>
                    (Some(fromName(name)), 0)
                case None => getSuperclassElement(clazz) match {
                    case Some(superclass) =>
                        var (result, depth) = getInferredFieldOrFromSuperclass(field, superclass, defaultOpLevel)
                        // change Local superclass field to Strong for the subclass
                        result = result match {
                            case Some(value) if AnnotationUtils.areSame(value, localAnnotation) => Some(strongAnnotation)
                            case _ => result
                        }
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
                case _ => None // ignore interfaces
            }
            case _ => None
        }

    private def getSuperclassElement(classTree: ClassTree): Option[TypeElement] =
        getSuperclassElement(TreeUtils.elementFromDeclaration(classTree))

    private def getSourceOfElement(elt: TypeElement): ClassTree = atypeFactory.getTreeUtils.getTree(elt)

    private def getOwnFields(elt: TypeElement): Iterable[VariableElement] = {
        elt.getEnclosedElements.filter({
            case _: VariableElement => true
            case _ => false
        }).map(f => f.asInstanceOf[VariableElement])
    }

    private def fromName(name: String): AnnotationMirror =
        AnnotationBuilder.fromName(atypeFactory.getElementUtils, name)
}
