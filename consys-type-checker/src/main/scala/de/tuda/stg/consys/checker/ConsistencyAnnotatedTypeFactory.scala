package de.tuda.stg.consys.checker

import com.sun.source.tree.{MemberSelectTree, MethodInvocationTree, MethodTree, Tree}
import de.tuda.stg.consys.annotations.methods.{StrongOp, WeakOp}
import de.tuda.stg.consys.annotations.MethodWriteList
import de.tuda.stg.consys.checker.jdk.Utils
import de.tuda.stg.consys.checker.TypeFactoryUtils._
import de.tuda.stg.consys.checker.qual.ThisConsistent
import org.checkerframework.common.basetype.{BaseAnnotatedTypeFactory, BaseTypeChecker}
import org.checkerframework.framework.`type`.{AnnotatedTypeMirror, DefaultTypeHierarchy, QualifierHierarchy, TypeHierarchy}
import org.checkerframework.framework.`type`.treeannotator.{ListTreeAnnotator, TreeAnnotator}
import org.checkerframework.framework.`type`.typeannotator.{ListTypeAnnotator, TypeAnnotator}
import org.checkerframework.javacutil.AnnotationBuilder
import org.checkerframework.javacutil.TreeUtils._

import java.util
import javax.lang.model.element.{AnnotationMirror, AnnotationValue, Element, ElementKind, ExecutableElement, TypeElement, VariableElement}
import scala.collection.mutable
import scala.jdk.CollectionConverters._

//Set useFlow to false if the flow analysis should be used.
class ConsistencyAnnotatedTypeFactory(checker: BaseTypeChecker) extends BaseAnnotatedTypeFactory(checker, false) {
    // force initialization of dependant classes (TreeAnnotator, TypeAnnotator, TypeHierarchy, etc.)
    this.postInit()
    shouldCache = false

    var mixedInferenceVisitor: MixedInferenceVisitor = new MixedInferenceVisitor()(this)

    private val visitClassContext: mutable.Stack[(TypeElement, AnnotationMirror)] = mutable.Stack.empty
    private var methodReceiverContext: Option[AnnotationMirror] = None


    override protected def createTreeAnnotator: TreeAnnotator = {
        val others = super.createTreeAnnotator
        new ListTreeAnnotator(others, new ConsistencyTreeAnnotator()(this))
    }

    override protected def createTypeAnnotator: TypeAnnotator = {
        val others = super.createTypeAnnotator
        new ListTypeAnnotator(others, new ConsistencyTypeAnnotator()(this))
    }

    override protected def createTypeHierarchy: TypeHierarchy = {
        val hierarchy = new DefaultTypeHierarchy(checker, getQualifierHierarchy,
            checker.getBooleanOption("ignoreRawTypeArguments", true),
            checker.hasOption("invariantArrays"))
        new ConsistencyTypeHierarchy(hierarchy, this)
    }

    override protected def createQualifierHierarchy: QualifierHierarchy =
        new ConsistencyQualifierHierarchy(getSupportedTypeQualifiers, getElementUtils, this)

    override def getAnnotatedType(tree: Tree): AnnotatedTypeMirror = tree match {
        // TODO: disable cache completely, since we can have @ThisConsistent in method body?
        case mt: MethodTree if containsSameByClass(elementFromDeclaration(mt).getReturnType.getAnnotationMirrors, classOf[ThisConsistent]) =>
            // disable cache when querying methods, so that we don't skip the @ThisConsistent type adaptation
            // fields are never cached, so we don't need additional rules there
            val prevShouldCache = shouldCache
            shouldCache = false
            val result = super.getAnnotatedType(tree)
            shouldCache = prevShouldCache
            result

        case _ =>
            super.getAnnotatedType(tree)
    }

    def getAnnotatedTypeWithContext(elt: ExecutableElement, context: MethodInvocationTree): AnnotatedTypeMirror.AnnotatedExecutableType = {
        val prevMethodReceiverContext = methodReceiverContext

        context.getMethodSelect match {
            case mst: MemberSelectTree if !isExplicitThisDereference(mst.getExpression) =>
                methodReceiverContext = Some(getAnnotatedType(mst.getExpression).
                    getAnnotationInHierarchy(TypeFactoryUtils.inconsistentAnnotation(this)))
            case _ =>
                methodReceiverContext = Some(visitClassContext.top._2)
        }

        val result = getAnnotatedType(elt)
        methodReceiverContext = prevMethodReceiverContext
        result
    }

    override protected def addComputedTypeAnnotations(tree: Tree, typ: AnnotatedTypeMirror, iUseFlow: Boolean): Unit = {
        val prevMethodReceiverContext = methodReceiverContext

        // adapts the receiver context, so that the TypeAnnotator has the correct information when inferring
        // return types on mixed getters
        tree match {
            case _: MethodTree if visitClassContext.nonEmpty =>
                methodReceiverContext = Some(visitClassContext.top._2)
            case mit: MethodInvocationTree =>
                mit.getMethodSelect match {
                    case mst: MemberSelectTree if !isExplicitThisDereference(mst.getExpression) =>
                        methodReceiverContext = Some(getAnnotatedType(mst.getExpression).
                            getAnnotationInHierarchy(TypeFactoryUtils.inconsistentAnnotation(this)))
                    case _ =>
                        methodReceiverContext = Some(visitClassContext.top._2)
                }
            case _ => // nothing to do
        }

        super.addComputedTypeAnnotations(tree, typ, iUseFlow)
        methodReceiverContext = prevMethodReceiverContext
    }

    override def addComputedTypeAnnotations(elt: Element, typ: AnnotatedTypeMirror): Unit = {
        val prevMethodReceiverContext = methodReceiverContext

        super.addComputedTypeAnnotations(elt, typ)
        methodReceiverContext = prevMethodReceiverContext
    }

    override def getDeclAnnotations(elt: Element): util.Set[AnnotationMirror] = {
        val result = super.getDeclAnnotations(elt)

        elt match {
            case method: ExecutableElement =>
                // add @MethodWriteList annotation containing each field the method updates (persists in .class files)
                mixedInferenceVisitor.getMethodWriteList(method) match {
                    case Some(fields) =>
                        val annotationValues = fields.map(f =>
                            AnnotationBuilder.elementNamesValues("", f.getSimpleName.toString).get(""))
                        result.add(AnnotationBuilder.fromClass(getElementUtils, classOf[MethodWriteList],
                            AnnotationBuilder.elementNamesValues("value", annotationValues.toList.asJava)))
                    case None => // nothing to do
                }

            case field: VariableElement if field.getKind == ElementKind.FIELD =>
                // add runtime @MixedField annotation
                val clazz = elt.getEnclosingElement.asInstanceOf[TypeElement]
                val withWeakDefault = mixedInferenceVisitor.getInferred(clazz, mixedAnnotation(classOf[WeakOp])(this), field)
                val withStrongDefault = mixedInferenceVisitor.getInferred(clazz, mixedAnnotation(classOf[StrongOp])(this), field)

                val values = mutable.Map.empty[String, AnnotationValue]
                if (withWeakDefault.isDefined)
                    values ++= AnnotationBuilder.elementNamesValues("consistencyForWeakDefault",
                        withWeakDefault.get.getAnnotationType.asElement.getSimpleName.toString).asScala
                if (withStrongDefault.isDefined)
                    values ++= AnnotationBuilder.elementNamesValues("consistencyForStrongDefault",
                        withStrongDefault.get.getAnnotationType.asElement.getSimpleName.toString).asScala

                // only add if annotation is fully constructable
                if (values.size > 1) Utils.storeDeclarationAnnotation(elt, values.asJava, this)

            case _ => // nothing to do
        }

        result
    }

    def isInMixedClassContext: Boolean =
        visitClassContext.nonEmpty && TypeFactoryUtils.isMixedQualifier(visitClassContext.top._2)( this)

    def pushVisitClassContext(clazz: TypeElement, typ: AnnotationMirror): Unit = visitClassContext.push((clazz, typ))

    def popVisitClassContext(): Unit = visitClassContext.pop

    def peekVisitClassContext: (TypeElement, AnnotationMirror) = visitClassContext.top

    def isVisitClassContextEmpty: Boolean = visitClassContext.isEmpty

    def getMethodReceiverContext: Option[AnnotationMirror] = methodReceiverContext

    def getVisitor: ConsistencyVisitor = checker.getVisitor.asInstanceOf[ConsistencyVisitor]
}
