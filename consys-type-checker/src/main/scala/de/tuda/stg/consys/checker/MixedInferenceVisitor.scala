package de.tuda.stg.consys.checker

import com.sun.source.tree._
import com.sun.source.util.TreeScanner
import de.tuda.stg.consys.checker.qual.{Inconsistent, Local}
import org.checkerframework.javacutil.{AnnotationBuilder, AnnotationUtils, ElementUtils, TreeUtils}
import de.tuda.stg.consys.checker.MixedInferenceVisitor._

import java.lang.annotation.Annotation
import javax.lang.model.`type`.DeclaredType
import javax.lang.model.element.{AnnotationMirror, ElementKind, ExecutableElement, Modifier, TypeElement, VariableElement}
import scala.collection.convert.ImplicitConversions.`collection AsScalaIterable`
import scala.collection.mutable

object MixedInferenceVisitor {
    sealed trait AccessType
    case object Write extends AccessType
    case object Read extends AccessType

    type DefaultOp = String
    type State = (Option[TypeElement], Option[DefaultOp], Option[AnnotationMirror], Option[AccessType], Option[ExecutableElement])
}

class MixedInferenceVisitor(implicit tf: ConsistencyAnnotatedTypeFactory) extends TreeScanner[Void, State] {
    import TypeFactoryUtils._

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

    private val methodWriteTable: mutable.Map[ExecutableElement, Set[VariableElement]] = mutable.Map.empty

    def getMethodWriteList(method: ExecutableElement): Option[Set[VariableElement]] =
        methodWriteTable.get(method)

    def getInferred(clazz: TypeElement, qual: AnnotationMirror, field: VariableElement): Option[AnnotationMirror] =
        getInferredFieldOrFromSuperclass(field, clazz, getNameForMixedDefaultOp(qual)) match {
            case Some((qualifier, _, _)) => Some(qualifier)
            case None => None
        }

    def getReadAccess(tree: Tree): Option[AnnotationMirror] =
        readAccessTable.get(tree)

    def processClass(tree: ClassTree, qualifier: AnnotationMirror): Unit =
        processClass(tree, (None, Some(getNameForMixedDefaultOp(qualifier)), None, None, None))

    def processClass(elt: TypeElement, qualifier: AnnotationMirror): Unit =
        processClass(elt, (None, Some(getNameForMixedDefaultOp(qualifier)), None, None, None))

    private def processClass(node: ClassTree, state: State): Unit = {
        val (_, maybeDefaultOp, _, _, _) = state
        val defaultOp = maybeDefaultOp match {
            case None => sys.error("ConSysT type checker bug: no default level for mixed inference given")
            case Some(value) => value
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

        val newState = (Some(classElement), maybeDefaultOp, None, Some(Read), None)
        checkSuperclass(getSuperclassElement(node), newState)
        processPublicFields(newState)
        processExplicitFields(newState)
        processStaticFields(newState)
        super.visitClass(node, newState)
        processUnusedFields(newState)
        checkSubclasses(newState)
    }

    private def processClass(classElement: TypeElement, state: State): Unit = {
        val (_, maybeDefaultOp, _, _, _) = state
        val defaultOp = maybeDefaultOp match {
            case None => sys.error("ConSysT type checker bug: no default level for mixed inference")
            case Some(value) => value
        }

        val className = getQualifiedName(classElement)
        if (inferenceTable.contains((className, defaultOp)))
            return
        inferenceTable.put((className, defaultOp), (Partial, mutable.Map.empty))

        val newState = (Some(classElement), maybeDefaultOp, None, Some(Read), None)
        checkSuperclass(getSuperclassElement(classElement), newState)
        processClassDeclaration(classElement, state)
    }

    private def checkSuperclass(superclass: Option[TypeElement], state: State): Unit = {
        val (_, Some(defaultOp), _, _, _) = state
        superclass match {
            case Some(elt) =>
                // if the superclass is declared in the same compilation unit, we can immediately visit the tree
                tf.getTreeUtils.getTree(elt) match {
                    case null => processClass(elt, state)
                    case tree => processClass(tree, state)
                }
                // type check the superclass for the mixed qualifier of the subclass
                tf.getVisitor.queueClassVisit(elt, mixedAnnotation(Class.forName(defaultOp).asInstanceOf[Class[_ <: Annotation]]))
            case None =>
        }
    }

    private def checkSubclasses(state: State): Unit = {
        // returns a set of tuples with a class and field qualifier for all subclasses with an explicit entry for that field
        def getInferredFieldInSubclasses(field: VariableElement, clazz: TypeElement, defaultOpLevel: String): Set[(ClassName, AnnotationName)] = {
            val className = getQualifiedName(clazz)
            val fieldName = getQualifiedName(field)
            inferenceTable.filter(entry => {
                val ((foundClass, foundDefaultOp), (foundVisitMode, fieldMap)) = entry
                foundClass != className &&
                    foundDefaultOp == defaultOpLevel &&
                    foundVisitMode == Full &&
                    fieldMap.contains(fieldName)
            }).map(entry => {
                val ((foundClass, _), (_, fieldMap)) = entry
                (foundClass, fieldMap(fieldName))
            }).toSet
        }

        val (Some(clazz), Some(defaultOp), _, _, _) = state

        // check subclass fields for inheritance violations, in case we process classes out of order
        getOwnFields(clazz).foreach(field => {
            getInferredFieldInSubclasses(field, clazz, defaultOp).foreach(entry => {
                val (subclass, subclassQualifier) = entry
                val superclassQualifier = getInferredFieldOrFromSuperclass(field, clazz, defaultOp).get._1

                tf.getChecker.reportError(field, "mixed.inheritance.field.overwrite",
                    superclassQualifier, field, subclassQualifier, subclass)
            })
        })
    }

    private def processPublicFields(state: State): Unit = {
        val (Some(clazz), Some(defaultOp), _, _, _) = state

        // set public and package fields to the default level
        getOwnFields(clazz).
            filter(field => !isPrivateOrProtected(field)).
            foreach(field => {
                getExplicitConsistencyAnnotation(field) match {
                    case Some(value) if !AnnotationUtils.areSame(value, getQualifierForOp(defaultOp).get) =>
                        tf.getChecker.reportError(field, "mixed.field.public.incompatible", defaultOp)
                    case _ =>
                }
                updateField(field, (Some(clazz), Some(defaultOp), getQualifierForOp(defaultOp), Some(Write), None), field)
            })
    }

    private def processUnusedFields(state: State): Unit = {
        val (Some(clazz), Some(defaultOp), _, _, _) = state
        // set all unused unannotated fields to Local
        getOwnFields(clazz).
            filter(field => !inferenceTable.get(clazz.getQualifiedName.toString, defaultOp).get._2.
                contains(getQualifiedName(field)) && getExplicitConsistencyAnnotation(field).isEmpty).
            foreach(field => updateField(field, (Some(clazz), Some(defaultOp), Some(localAnnotation), Some(Write), None), field))
    }

    private def processStaticFields(state: State): Unit = {
        val (Some(clazz), Some(defaultOp), _, _, _) = state
        // set all static fields to Inconsistent and check for forbidden explicit annotations
        getOwnFields(clazz).
            filter(field => field.getModifiers.contains(Modifier.STATIC)).
            foreach(field => {
                getExplicitConsistencyAnnotation(field) match {
                    case Some(value) if !tf.areSameByClass(value, classOf[Inconsistent]) =>
                        tf.getChecker.reportError(field, "mixed.field.static.incompatible")
                    case _ =>
                }
                updateField(field, (Some(clazz), Some(defaultOp), Some(inconsistentAnnotation), Some(Write), None), field)
            })
    }

    private def processExplicitFields(state: State): Unit = {
        val (Some(clazz), Some(defaultOp), _, _, _) = state
        // set all fields with explicit annotations to the given annotation
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

        val (_, Some(defaultOp), _, _, _) = state

        val methodElt = TreeUtils.elementFromDeclaration(node)
        val methodLevel = getQualifierForOp(getMixedOpForMethod(methodElt, defaultOp))

        super.visitMethod(node, state.copy(_3 = methodLevel, _5 = Some(methodElt)))
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
        if (isSideEffectFree(method))
            super.visitMethodInvocation(node, state.copy(_4 = Some(Read)))
        else
            super.visitMethodInvocation(node, state.copy(_4 = Some(Write)))
    }

    override def visitMemberSelect(node: MemberSelectTree, state: State): Void = {
        processField(node, state)
        super.visitMemberSelect(node, state)
    }

    override def visitIdentifier(node: IdentifierTree, state: State): Void = {
        processField(node, state)
        null
    }

    private def processField(node: ExpressionTree, state: State): Unit = {
        val (Some(clazz), _, maybeMethodLevel, Some(accessMode), maybeMethod) = state
        // ignore fields outside methods (i.e. field declarations)
        if (maybeMethodLevel.isEmpty)
            return
        val methodLevel = maybeMethodLevel.get

        TreeUtils.elementFromUse(node) match {
            case field: VariableElement if field.getKind == ElementKind.FIELD
                && ElementUtils.getAllFieldsIn(clazz, tf.getElementUtils).contains(field) => // ignore element if it is a field of a field

                // update inference table
                (getExplicitOrPublicQualifier(field, state), accessMode) match {
                    // check compatibility between explicit type and operation level
                    case (Some(explicitAnnotation), Write) if !tf.getQualifierHierarchy.isSubtype(methodLevel, explicitAnnotation) =>
                        tf.getChecker.reportError(node, "mixed.field.incompatible",
                            getQualifiedName(explicitAnnotation),
                            getQualifiedName(methodLevel))

                    case (None, _) =>
                        updateField(field, state, node)

                    case _ =>
                }

                // update read access table
                accessMode match {
                    case Read => readAccessTable.update(node, methodLevel)
                    case _ =>
                }

                // update write access table
                maybeMethod match {
                    case Some(method) => (accessMode, methodWriteTable.get(method)) match {
                        case (Write, Some(value)) => methodWriteTable.update(method, value + field)
                        case (Write, None) => methodWriteTable.update(method, Set(field))
                        case (Read, None) => methodWriteTable.update(method, Set.empty)
                        case _ =>
                    }
                    case None =>
                }

            case _ =>
        }
    }

    private def updateField(field: VariableElement, state: State, source: AnyRef): Unit = {
        if (field.getKind != ElementKind.FIELD)
            return

        val (Some(clazz), Some(defaultOp), Some(annotation), Some(accessMode), _) = state
        val className = getQualifiedName(clazz)
        val fieldName = getQualifiedName(field)

        (getInferredFieldOrFromSuperclass(field, clazz, defaultOp), accessMode) match {
            case (Some((fieldLevel, superclass, _)), Write) if superclass == className =>
                // field is not inherited, so update inference result
                val lup = tf.getQualifierHierarchy.leastUpperBound(fieldLevel, annotation)
                inferenceTable.apply(clazz.getQualifiedName.toString, defaultOp)._2.update(getQualifiedName(field), getQualifiedName(lup))

            case (Some((fieldLevel, superclass, Full)), Write) if superclass != className =>
                // field is inherited, so only check compatibility, i.e. if field would be weakened
                if (!tf.getQualifierHierarchy.isSubtype(annotation, fieldLevel))
                    tf.getChecker.reportError(source, "mixed.inheritance.field.overwrite",
                        fieldLevel, field.getSimpleName, annotation, className)

            case (Some((fieldLevel, superclass, Partial)), Write) if !isInProjectPackage(superclass) =>
                // field is inherited, but from a third-party class
                if (!tf.getQualifierHierarchy.isSubtype(annotation, fieldLevel))
                    tf.getChecker.reportWarning(source, "mixed.inheritance.field.overwrite",
                        fieldLevel, field.getSimpleName, annotation, className)

            case (None, Write) =>
                // field is encountered for the first time
                inferenceTable.apply(className, defaultOp)._2.update(fieldName, getQualifiedName(annotation))

            case (None, Read) =>
                // field is encountered for the first time
                inferenceTable.apply(className, defaultOp)._2.update(fieldName, classOf[Local].getCanonicalName)

            case _ =>
        }
    }

    private def processClassDeclaration(clazz: TypeElement, state: State): Unit = {
        val (_, Some(defaultOp), _, _, _) = state
        getQualifierNameForOp(defaultOp) match {
            case Some(qualifier) =>
                // set inherited fields to default level
                val level = AnnotationBuilder.fromName(tf.getElementUtils, qualifier)
                getOwnFields(clazz).foreach(f => {
                    updateField(f, (Some(clazz), Some(defaultOp), Some(level), Some(Write), None), f)
                })
            case None =>
                sys.error("ConSysT type checker bug: invalid default operation on Mixed qualifier")
        }
    }

    // recursively searches for a given field in the inference table
    private def getInferredFieldOrFromSuperclass(field: VariableElement, clazz: TypeElement, defaultOpLevel: String): Option[(AnnotationMirror, ClassName, VisitMode)] = {
        inferenceTable.get(getQualifiedName(clazz), defaultOpLevel) match {
            case Some(entry) => entry._2.get(getQualifiedName(field)) match {
                case Some(name) =>
                    Some(fromName(name), getQualifiedName(clazz), entry._1)
                case None => getSuperclassElement(clazz) match {
                    case Some(superclass) =>
                        // change Local superclass field to Strong for the subclass
                        getInferredFieldOrFromSuperclass(field, superclass, defaultOpLevel) match {
                            case Some((value, resultSuperclass, visitMode)) if AnnotationUtils.areSame(value, localAnnotation) =>
                                Some(strongAnnotation, resultSuperclass, visitMode)
                            case result => result
                        }
                    case None => None
                }
            }
            case None => None
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

    // returns the fields that the given class defines (i.e. excluding inherited fields)
    private def getOwnFields(elt: TypeElement): Iterable[VariableElement] = {
        elt.getEnclosedElements.filter({
            case _: VariableElement => true
            case _ => false
        }).map(f => f.asInstanceOf[VariableElement])
    }

    private def fromName(name: String): AnnotationMirror =
        AnnotationBuilder.fromName(tf.getElementUtils, name)

    // returns the explicit or public qualifier for a field if it exists
    private def getExplicitOrPublicQualifier(field: VariableElement, state: State): Option[AnnotationMirror] = {
        val (_, Some(defaultOp), _, _, _) = state
        field.getEnclosingElement match {
            case clazz: TypeElement =>
                if (!isPrivateOrProtected(field)) {
                    getInferredFieldOrFromSuperclass(field, clazz, defaultOp) match {
                        case Some((qualifier, _, _)) => Some(qualifier)
                        case None => None
                    }
                } else {
                    getExplicitConsistencyAnnotation(field)
                }
            case _ => None
        }
    }

    private def isInProjectPackage(className: String): Boolean = {
        val packageName = tf.getChecker.getOption("projectPackage", "")
        packageName.nonEmpty && className.startsWith(packageName)
    }
}
