package de.tuda.stg.consys.checker

import com.sun.source.tree.{MemberSelectTree, MethodInvocationTree, Tree}
import de.tuda.stg.consys.annotations.MethodWriteList
import de.tuda.stg.consys.annotations.methods.{StrongOp, WeakOp}
import de.tuda.stg.consys.checker.TypeFactoryUtils._
import de.tuda.stg.consys.checker.jdk.Utils
import de.tuda.stg.consys.checker.qual.ThisConsistent
import org.checkerframework.common.basetype.{BaseAnnotatedTypeFactory, BaseTypeChecker}
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.{AnnotatedDeclaredType, AnnotatedExecutableType}
import org.checkerframework.framework.`type`._
import org.checkerframework.framework.`type`.treeannotator.{ListTreeAnnotator, TreeAnnotator}
import org.checkerframework.framework.`type`.typeannotator.{ListTypeAnnotator, TypeAnnotator}
import org.checkerframework.javacutil.TreeUtils._
import org.checkerframework.javacutil.{AnnotationBuilder, AnnotationUtils, TreeUtils}

import java.util
import javax.lang.model.element._
import scala.collection.mutable
import scala.jdk.CollectionConverters._

//Set useFlow to false if the flow analysis should be used.
class ConsistencyAnnotatedTypeFactory(checker: BaseTypeChecker) extends BaseAnnotatedTypeFactory(checker, false) {
    // force initialization of dependant classes (TreeAnnotator, TypeAnnotator, TypeHierarchy, etc.)
    this.postInit()
    // disable caching for the annotated type factory, so that we can do multiple runs on the same
    // compilation unit with different targets for @ThisConsistent
    // TODO: see if we can instead manually clear all caches when reanalysing a compilation unit
    shouldCache = false

    var mixedInferenceVisitor: MixedInferenceVisitor = new MixedInferenceVisitor()(this)

    /**
     * Class and qualifier pair that is currently being visited by the ConsistencyVisitor.
     */
    private val visitClassContext: mutable.Stack[(TypeElement, AnnotationMirror)] = mutable.Stack.empty

    // TODO: this should be the thisConsistentContext instead, i.e. Mixed should already be resolved
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

    def pushVisitClassContext(clazz: TypeElement, typ: AnnotationMirror): Unit = visitClassContext.push((clazz, typ))

    def popVisitClassContext(): Unit = visitClassContext.pop

    def peekVisitClassContext: (TypeElement, AnnotationMirror) = visitClassContext.top

    def isVisitClassContextEmpty: Boolean = visitClassContext.isEmpty

    def isInMixedClassContext: Boolean =
        visitClassContext.nonEmpty && TypeFactoryUtils.isMixedQualifier(visitClassContext.top._2)(this)

    def isInInconsistentClassContext: Boolean =
        visitClassContext.nonEmpty && AnnotationUtils.areSame(visitClassContext.top._2, inconsistentAnnotation(this))

    /**
     * @inheritdoc
     * Resolves @ThisConsistent for local variable declarations.
     */
    override def getAnnotatedTypeLhs(lhsTree: Tree): AnnotatedTypeMirror = {
        val result = super.getAnnotatedTypeLhs(lhsTree)
        val element = TreeUtils.elementFromTree(lhsTree)
        element.getKind match {
            case ElementKind.LOCAL_VARIABLE if result.hasAnnotation(classOf[ThisConsistent]) =>
                deepReplaceThisConsistent(result, inferThisTypeFromEnclosingMethod(element)(this))
            case _ =>
        }
        result
    }

    /**
     * @inheritdoc
     * Resolves @ThisConsistent for method invocations (in return types, parameters)
     */
    override def methodFromUse(tree: MethodInvocationTree): AnnotatedTypeFactory.ParameterizedExecutableType = {
        withContext(tree) {
            val typ = super.methodFromUse(tree)
            replaceThisConsistent(typ.executableType)
            typ
        }
    }

    /**
     * @inheritdoc
     * Called from getAnnotatedType after the annotations from the code and stub files are computed.
     */
    override protected def addComputedTypeAnnotations(tree: Tree, typ: AnnotatedTypeMirror, iUseFlow: Boolean): Unit = {
        val prevMethodReceiverContext = methodReceiverContext

        // adapts the receiver context, so that the TypeAnnotator has the correct information when
        // inferring @ThisConsistent
        tree match {
            case mit: MethodInvocationTree =>
                setMethodReceiverContext(mit)
            case _ if visitClassContext.nonEmpty =>
                // TODO: resolve Mixed, based on enclosing element from tree
                methodReceiverContext = Some(visitClassContext.top._2)
            case _ => // TODO: what to do here? Can we rule this out?
        }

        super.addComputedTypeAnnotations(tree, typ, iUseFlow)
        methodReceiverContext = prevMethodReceiverContext
    }

    override protected def addComputedTypeAnnotations(elt: Element, typ: AnnotatedTypeMirror): Unit = {
        // TODO: same as above
        super.addComputedTypeAnnotations(elt, typ)
    }

    /**
     * Adds runtime annotations (@MethodWriteList, @MixedField) to compilation output.
     */
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

    def withContext[R](context: MethodInvocationTree)(f: => R): R = {
        val prevMethodReceiverContext = methodReceiverContext
        setMethodReceiverContext(context)
        val result = f
        methodReceiverContext = prevMethodReceiverContext
        result
    }

    def withContext[R](context: AnnotationMirror)(f: => R): R = {
        val prevMethodReceiverContext = methodReceiverContext
        methodReceiverContext = Some(context)
        val result = f
        methodReceiverContext = prevMethodReceiverContext
        result
    }

    def replaceThisConsistent(methodType: AnnotatedExecutableType): Unit = {
        // return & parameter type adaptation for @ThisConsistent
        methodReceiverContext match {
            case Some(recvQualifier) =>
                deepReplaceThisConsistent(methodType, inferThisTypeFromReceiver(recvQualifier, methodType.getElement)(this))

            case _ =>
        }
    }

    def deepReplaceThisConsistent(typ: AnnotatedTypeMirror, newType: AnnotationMirror): Unit = typ match {
        case adt: AnnotatedDeclaredType =>
            adt.getTypeArguments.forEach(typeArg => {
                if (typeArg.hasAnnotation(classOf[ThisConsistent])) {
                    deepReplaceThisConsistent(typeArg, newType)
                }
            })
            if (adt.hasAnnotation(classOf[ThisConsistent])) {
                adt.replaceAnnotation(newType)
            }

        case aet: AnnotatedExecutableType =>
            // return type
            if (aet.getReturnType.hasAnnotation(classOf[ThisConsistent])) {
                deepReplaceThisConsistent(aet.getReturnType, newType)
            }
            // parameter types
            aet.getParameterTypes.asScala.foreach(paramType => {
                if (paramType.hasAnnotation(classOf[ThisConsistent])) {
                    deepReplaceThisConsistent(paramType, newType)
                }
            })

        case _ =>
            typ.replaceAnnotation(newType)
    }

    def getVisitor: ConsistencyVisitor = checker.getVisitor.asInstanceOf[ConsistencyVisitor]

    private def setMethodReceiverContext(tree: MethodInvocationTree): Unit = tree.getMethodSelect match {
        case mst: MemberSelectTree if !isExplicitThisDereference(mst.getExpression) =>
            methodReceiverContext = Some(getAnnotatedType(mst.getExpression).
                getAnnotationInHierarchy(TypeFactoryUtils.inconsistentAnnotation(this)))
        case _ =>
            methodReceiverContext = Some(visitClassContext.top._2)
    }
}
