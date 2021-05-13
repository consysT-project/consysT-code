package de.tuda.stg.consys.checker

import com.sun.source.tree.{AnnotationTree, AssignmentTree, ClassTree, CompoundAssignmentTree, ExpressionTree, IdentifierTree, MemberSelectTree, MethodTree, ModifiersTree, Tree, VariableTree}
import com.sun.source.util.TreeScanner
import de.tuda.stg.consys.checker.TypeFactoryUtils.{annoPackageName, checkerPackageName, getDefaultOp, getQualifiedName}
import de.tuda.stg.consys.checker.qual.{Local, Mixed, QualifierForOperation}
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.AnnotatedDeclaredType
import org.checkerframework.framework.`type`.GenericAnnotatedTypeFactory
import org.checkerframework.javacutil.{AnnotationBuilder, AnnotationUtils, ElementUtils, TreeUtils, TypesUtils}

import java.lang.annotation.Annotation
import javax.lang.model.`type`.DeclaredType
import javax.lang.model.element.{AnnotationMirror, AnnotationValue, ElementKind, TypeElement, VariableElement}
import scala.collection.convert.ImplicitConversions.`collection AsScalaIterable`
import scala.collection.mutable

class InferenceVisitor(atypeFactory: ConsistencyAnnotatedTypeFactory) extends TreeScanner[Void, Boolean] {

    // TODO: switch the keys to strings for performance?
    type InferenceTable = mutable.Map[(TypeElement, String, VariableElement), AnnotationMirror]
    type ExtendsTable = mutable.Map[(TypeElement, String), (TypeElement, String)]

    var inferenceTable: InferenceTable = mutable.Map.empty
    var extendsTable: ExtendsTable = mutable.Map.empty

    private var annoMapping: Map[String, String] = Map.empty

    private var classContext: Option[TypeElement] = Option.empty
    private var defaultOpLevel: Option[String] = Option.empty
    //private var extendsDefaultOpLevel: Option[String] = Option.empty
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
                        }

                        r = super.visitClass(node, isLHS)

                    case None =>
                }

            case (None, Some(_)) =>
                getSuperclassElement(node) match {
                    case Some(elt) =>
                        val superclassTree = getSourceOfElement(elt)
                        if (superclassTree != null) {
                            visitClass(superclassTree, isLHS)
                            atypeFactory.processClassWithoutCache(superclassTree, defaultOpLevel.get)
                        }

                        r = super.visitClass(node, isLHS)

                    case None =>
                }

            case (None, None) =>
        }

        classContext = prev._1
        defaultOpLevel = prev._2
        r

        /*
        val mixed = getAnnotationMirror(node, classOf[Mixed])
        if (mixed.isDefined) {
            defaultOpLevel = Some(AnnotationUtils.getElementValuesWithDefaults(mixed).values().head.getValue.toString)

            TreeUtils.elementFromDeclaration(node).getSuperclass match {
                case dt: DeclaredType =>
                    val superclassTree = atypeFactory.getTreeUtils.getTree(dt.asElement().asInstanceOf[TypeElement])
                    // TODO: null when superclass not found -> possible causes?
                    if (superclassTree != null) {
                        val extendsMixed = atypeFactory.getAnnotatedType(node.getExtendsClause).getAnnotation(classOf[Mixed])
                        if (extendsMixed == null) {
                            atypeFactory.getChecker.reportError(node.getExtendsClause, "Mixed must extends Mixed")
                            return null
                        }

                        extendsDefaultOpLevel = Some(AnnotationUtils.getElementValuesWithDefaults(extendsMixed).values().head.getValue.toString)
                        extendsTable.update((classContext.get, defaultOpLevel.get), (dt.asElement().asInstanceOf[TypeElement], extendsDefaultOpLevel.get))
                        visitClass(superclassTree, isLHS, extendsDefaultOpLevel.get)
                        atypeFactory.processClassWithoutCache(superclassTree, extendsDefaultOpLevel.get)
                    }
                case _ =>
            }

            val r = super.visitClass(node, isLHS)
            classContext = prev._1
            defaultOpLevel = prev._2
            extendsDefaultOpLevel = prev._3
            r
        } else if (defaultOpLevel.isDefined) {
            val r = super.visitClass(node, isLHS)
            classContext = prev._1
            defaultOpLevel = prev._2
            extendsDefaultOpLevel = prev._3
            r
        } else {
            classContext = prev._1
            defaultOpLevel = prev._2
            extendsDefaultOpLevel = prev._3
            null
        }
        */
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
                case (field: VariableElement, true) if field.getKind == ElementKind.FIELD => getInferredFieldOrFromSuperclass(field, classContext.get, defaultOpLevel.get) match {
                    case Some(fieldLevel) =>
                        val lup = atypeFactory.getQualifierHierarchy.leastUpperBound(fieldLevel, methodLevel)
                        inferenceTable.update((classContext.get, defaultOpLevel.get, field), lup)
                    case None =>
                        inferenceTable.update((classContext.get, defaultOpLevel.get, field), methodLevel)
                }
                case (field: VariableElement, false) if field.getKind == ElementKind.FIELD => getInferredFieldOrFromSuperclass(field, classContext.get, defaultOpLevel.get) match {
                    case None => inferenceTable.update((classContext.get, defaultOpLevel.get, field), AnnotationBuilder.fromClass(atypeFactory.getElementUtils, classOf[Local]))
                    case _ =>
                }
                case _ =>
            }
            case _ =>
        }
    }

    def getInferredFieldOrFromSuperclass(field: VariableElement, clazz: TypeElement, defaultOpLevel: String): Option[AnnotationMirror] =
        inferenceTable.get(clazz, defaultOpLevel, field) match {
            case value: Some[AnnotationMirror] => value
            case None => getSuperclassElement(clazz) match {
                case Some(superclass) => getInferredFieldOrFromSuperclass(field, superclass, defaultOpLevel)
                case None => None
            }
            /*
            extendsTable.get(clazz, defaultOpLevel) match {
                case Some((superclass, superclassDefaultOpLevel)) =>
                    getInferredFieldOrFromSuperclass(field, superclass, superclassDefaultOpLevel)
                case _ => None
            }
            */
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
