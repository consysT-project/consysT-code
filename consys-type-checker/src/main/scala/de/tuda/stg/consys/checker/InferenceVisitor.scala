package de.tuda.stg.consys.checker

import com.sun.source.tree._
import com.sun.source.util.TreeScanner
import de.tuda.stg.consys.checker.qual.{Inconsistent, Local, Mixed}
import org.checkerframework.dataflow.qual.{Pure, SideEffectFree}
import org.checkerframework.javacutil.{AnnotationBuilder, AnnotationUtils, ElementUtils, TreeUtils}
import de.tuda.stg.consys.checker.InferenceVisitor._

import java.lang.annotation.Annotation
import javax.lang.model.`type`.{DeclaredType, TypeKind}
import javax.lang.model.element.{AnnotationMirror, ElementKind, Modifier, TypeElement, VariableElement}
import scala.collection.convert.ImplicitConversions.`collection AsScalaIterable`
import scala.collection.mutable

object InferenceVisitor {
    sealed trait AccessType
    case object Write extends AccessType
    case object Read extends AccessType

    type DefaultOp = String
    type State = (Option[TypeElement], Option[DefaultOp], Option[AnnotationMirror], Option[AccessType])
}

// TODO: checkSuperclass and checkSubclass without findTree
// TODO: infer for all default levels in one run
class InferenceVisitor(implicit tf: ConsistencyAnnotatedTypeFactory) extends TreeScanner[Void, State] {
    import de.tuda.stg.consys.checker.TypeFactoryUtils._

    sealed trait VisitMode
    case object Full extends VisitMode
    case object Partial extends VisitMode
    type ClassName = String
    type FieldName = String
    type AnnotationName = String
    type InferenceTable = mutable.Map[(ClassName, DefaultOp), (VisitMode, mutable.Map[FieldName, AnnotationName])]

    /**
     * Stores the inference results for each class and default operation combination.
     */
    private val inferenceTable: InferenceTable = mutable.Map.empty

    /**
     * Stores each field read tree and the operation level of the method it occurs in.
     */
    private val readAccessTable: mutable.Map[Tree, AnnotationMirror] = mutable.Map.empty

    def getInferred(clazz: TypeElement, qual: AnnotationMirror, field: VariableElement): Option[AnnotationMirror] =
        getInferredFieldOrFromSuperclass(field, clazz, getNameForMixedDefaultOp(qual))._1

    def getReadAccess(tree: Tree): Option[AnnotationMirror] =
        readAccessTable.get(tree)

    def processClass(tree: ClassTree, qualifier: AnnotationMirror): Unit =
        processClass(tree, (None, Some(getNameForMixedDefaultOp(qualifier)), None, None))

    def processClass(elt: TypeElement, qualifier: AnnotationMirror): Unit =
        processClass(elt, (None, Some(getNameForMixedDefaultOp(qualifier)), None, None))

    private def processClass(node: ClassTree, state: State): Unit = {
        val (_, maybeDefaultOp, _, _) = state
        val defaultOp = maybeDefaultOp match {
            case None => sys.error("ConSysT type checker bug: no default level for mixed inference")
            case Some(value) => value // TODO: validation here?
        }

        val classElement = TreeUtils.elementFromDeclaration(node)
        val className = getQualifiedName(classElement)

        // check if we already processed this class tree
        // if we only processed the element, we still want to process the tree
        inferenceTable.get((className, defaultOp)) match {
            case Some((visitMode, _)) => visitMode match {
                case Full => return
                case Partial =>
            }
            case None =>
        }
        inferenceTable.put((className, defaultOp), (Full, mutable.Map.empty))

        val newState = (Some(classElement), maybeDefaultOp, None, Some(Read))
        checkSuperclass(getSuperclassElement(node), newState)
        processPublicFields(newState)
        processExplicitFields(newState)
        processStaticFields(newState)
        super.visitClass(node, newState)
        processUnusedFields(newState)
    }

    private def processClass(classElement: TypeElement, state: State): Unit = {
        val (_, maybeDefaultOp, _, _) = state
        val defaultOp = maybeDefaultOp match {
            case None => sys.error("ConSysT type checker bug: no default level for mixed inference")
            case Some(value) => value // TODO: validation here?
        }

        val className = getQualifiedName(classElement)
        if (inferenceTable.contains((className, defaultOp)))
            return
        inferenceTable.put((className, defaultOp), (Partial, mutable.Map.empty))

        val newState = (Some(classElement), maybeDefaultOp, None, Some(Read))
        checkSuperclass(getSuperclassElement(classElement), newState)
        processClassDeclaration(classElement, state)
    }

    private def checkSuperclass(superclass: Option[TypeElement], state: State): Unit = {
        val (_, Some(defaultOp), _, _) = state
        superclass match {
            case Some(elt) =>
                // if the superclass is declared in the same compilation unit, we can immediately visit the tree
                tf.getTreeUtils.getTree(elt) match {
                    case null => processClass(elt, state)
                    case tree => processClass(tree, state)
                }
                // type check the superclass for the mixed qualifier of the subclass
                tf.getVisitor.visitOrQueueClassTree(elt, mixedAnnotation(Class.forName(defaultOp).asInstanceOf[Class[_ <: Annotation]]))
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
            foreach(field => {
                getExplicitConsistencyAnnotation(field) match {
                    case Some(value) if !AnnotationUtils.areSame(value, getQualifierForOp(defaultOp).get) =>
                        tf.getChecker.reportError(field, "mixed.field.public.incompatible", defaultOp)
                    case _ =>
                }
                updateField(field, (Some(clazz), Some(defaultOp), getQualifierForOp(defaultOp), Some(Write)), field)
            })
    }

    private def processUnusedFields(state: State): Unit = {
        val (Some(clazz), Some(defaultOp), _, _) = state
        // set all unused unannotated fields to Local
        getOwnFields(clazz).
            filter(field => !inferenceTable.get(clazz.getQualifiedName.toString, defaultOp).get._2.
                contains(getQualifiedName(field)) && getExplicitConsistencyAnnotation(field).isEmpty).
            foreach(field => updateField(field, (Some(clazz), Some(defaultOp), Some(localAnnotation), Some(Write)), field))
    }

    private def processStaticFields(state: State): Unit = {
        val (Some(clazz), Some(defaultOp), _, _) = state
        // set all static fields to Inconsistent and check for forbidden explicit annotations
        getOwnFields(clazz).
            filter(field => field.getModifiers.contains(Modifier.STATIC)).
            foreach(field => {
                getExplicitConsistencyAnnotation(field) match {
                    case Some(value) if !tf.areSameByClass(value, classOf[Inconsistent]) =>
                        tf.getChecker.reportError(field, "mixed.field.static.incompatible")
                    case _ =>
                }
                updateField(field, (Some(clazz), Some(defaultOp), Some(inconsistentAnnotation), Some(Write)), field)
            })
    }

    private def processExplicitFields(state: State): Unit = {
        val (Some(clazz), Some(defaultOp), _, _) = state

        getOwnFields(clazz).foreach(field => getExplicitConsistencyAnnotation(field) match {
                case Some(annotation) => inferenceTable.apply(clazz.getQualifiedName.toString, defaultOp)._2.
                    update(getQualifiedName(field), getQualifiedName(annotation))
                case None =>
        })
    }

    override def visitMethod(node: MethodTree, state: State): Void = {
        // ignore constructors and static methods
        if (TreeUtils.isConstructor(node) || node.getModifiers.getFlags.contains(Modifier.STATIC))
            return null

        val (_, Some(defaultOp), _, _) = state
        var methodLevel: Option[AnnotationMirror] = None

        // try to find an explicit supported operation level on the method
        getQualifierForOpMap.keys.foreach(operation => {
            if (hasAnnotation(node.getModifiers, operation)) {
                methodLevel match {
                    case None =>
                        methodLevel = getQualifierForOp(operation)
                    case _ =>
                        tf.getChecker.reportError(node, "mixed.operation.ambiguous")
                }
            }
        })

        // use default level if no operation was found
        if (methodLevel.isEmpty) {
            methodLevel = getQualifierForOp(defaultOp) match {
                case Some(value) => Some(value)
                case None => sys.error("ConSysT type checker bug: invalid default operation") // TODO: should this be a user error instead?
            }
        }

        super.visitMethod(node, state.copy(_3 = methodLevel))
    }

    override def visitAssignment(node: AssignmentTree, state: State): Void = {
        val r = scan(node.getVariable, state.copy(_4 = Some(Write)))
        reduce(scan(node.getExpression, state.copy(_4 = Some(Read))), r)
    }

    override def visitUnary(node: UnaryTree, state: State): Void = {
        super.visitUnary(node, state.copy(_4 = Some(Write)))
    }

    override def visitCompoundAssignment(node: CompoundAssignmentTree, state: State): Void = {
        val r = scan(node.getVariable, state.copy(_4 = Some(Write)))
        reduce(scan(node.getExpression, state.copy(_4 = Some(Read))), r)
    }

    override def visitMethodInvocation(node: MethodInvocationTree, state: State): Void = {
        val method = TreeUtils.elementFromUse(node)
        if (method.getAnnotation(classOf[SideEffectFree]) != null || method.getAnnotation(classOf[Pure]) != null)
            super.visitMethodInvocation(node, state.copy(_4 = Some(Read)))
        else
            super.visitMethodInvocation(node, state.copy(_4 = Some(Write)))
    }

    // TODO: are there more tree types for field use other than IdentifierTree and MemberSelect?
    override def visitMemberSelect(node: MemberSelectTree, state: State): Void = {
        processField(node, state)
        super.visitMemberSelect(node, state)
    }

    override def visitIdentifier(node: IdentifierTree, state: State): Void = {
        processField(node, state)
        null
    }

    private def processField(node: ExpressionTree, state: State): Unit = {
        val (classContext, _, methodContext, side) = state

        (methodContext, TreeUtils.elementFromUse(node)) match {
            case (Some(methodLevel), field: VariableElement)
                if field.getKind == ElementKind.FIELD // ignore element if it is a field of a field
                    && ElementUtils.getAllFieldsIn(classContext.get, tf.getElementUtils).contains(field) =>

                (getExplicitConsistencyAnnotation(field), side) match {
                    // check compatibility between explicit type and operation level
                    case (Some(explicitAnnotation), Some(Write)) if !tf.getQualifierHierarchy.isSubtype(methodLevel, explicitAnnotation) =>
                        tf.getChecker.reportError(node, "mixed.field.incompatible",
                            getQualifiedName(explicitAnnotation),
                            getQualifiedName(methodLevel))

                    case (None, _) =>
                        updateField(field, state, node)

                    case _ =>
                }

                state match {
                    case (_, _, _, Some(Write)) =>
                    case _ => readAccessTable.update(node, methodLevel)
                }
            case _ =>
        }
    }

    private def updateField(field: VariableElement, state: State, source: AnyRef): Unit = {
        if (field.getKind != ElementKind.FIELD)
            return

        val (Some(clazz), Some(defaultOp), Some(annotation), side) = state
        val className = getQualifiedName(clazz)
        val fieldName = getQualifiedName(field)

        (getInferredFieldOrFromSuperclass(field, clazz, defaultOp), side) match {
            case ((Some(fieldLevel), depth), Some(Write)) if depth == 0 =>
                val lup = tf.getQualifierHierarchy.leastUpperBound(fieldLevel, annotation)
                inferenceTable.apply(clazz.getQualifiedName.toString, defaultOp)._2.update(getQualifiedName(field), getQualifiedName(lup))
            case ((Some(fieldLevel), depth), Some(Write)) if depth > 0 =>
                // checks if field level is a (non-reflexive) subtype of method level, i.e. if field would be weakened
                if (!tf.getQualifierHierarchy.isSubtype(annotation, fieldLevel))
                    tf.getChecker.reportError(source, "mixed.inheritance.field.overwrite",
                        fieldLevel, field.getSimpleName, annotation, source)
            case ((None, _), Some(Write)) =>
                inferenceTable.apply(className, defaultOp)._2.update(fieldName, getQualifiedName(annotation))
            case ((None, _), Some(Read)) =>
                inferenceTable.apply(className, defaultOp)._2.update(fieldName, classOf[Local].getCanonicalName)
            case _ =>
        }

        // TODO: check subclass fields for inheritance violations, in case we process classes out of order
    }

    private def processClassDeclaration(elt: TypeElement, state: State): Unit = {
        val (_, defaultOpLevel, _, _) = state
        getQualifierNameForOp(defaultOpLevel.get) match {
            case Some(qualifier) =>
                val level = AnnotationBuilder.fromName(tf.getElementUtils, qualifier)
                getOwnFields(elt).foreach(f => {
                    updateField(f, (Some(elt), defaultOpLevel, Some(level), Some(Write)), f)
                })

            case None => // TODO: handle case where given default operation level is not valid
        }
    }

    def getInferredFieldOrFromSuperclass(field: VariableElement, clazz: TypeElement, defaultOpLevel: String): (Option[AnnotationMirror], Int) = {
        inferenceTable.get(clazz.getQualifiedName.toString, defaultOpLevel) match {
            case Some(map) => map._2.get(getQualifiedName(field)) match {
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

    private def getOwnFields(elt: TypeElement): Iterable[VariableElement] = {
        elt.getEnclosedElements.filter({
            case _: VariableElement => true
            case _ => false
        }).map(f => f.asInstanceOf[VariableElement])
    }

    private def fromName(name: String): AnnotationMirror =
        AnnotationBuilder.fromName(tf.getElementUtils, name)
}
