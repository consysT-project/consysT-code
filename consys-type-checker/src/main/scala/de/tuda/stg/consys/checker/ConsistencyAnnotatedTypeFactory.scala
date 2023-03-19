package de.tuda.stg.consys.checker

import com.sun.source.tree.{MethodInvocationTree, MethodTree, Tree}
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
import org.checkerframework.javacutil.{AnnotationBuilder, AnnotationUtils, TreeUtils}

import java.util
import javax.lang.model.element._
import scala.collection.mutable
import scala.jdk.CollectionConverters._

// Flow analysis (useFlow) is disabled
class ConsistencyAnnotatedTypeFactory(checker: BaseTypeChecker) extends BaseAnnotatedTypeFactory(checker, false) {
    // force initialization of dependant classes (TreeAnnotator, TypeAnnotator, TypeHierarchy, etc.)
    this.postInit()
    // disable caching for the annotated type factory, so that we can do multiple runs on the same
    // compilation unit with different targets for @ThisConsistent
    // TODO: see if we can instead manually clear all caches when reanalysing a compilation unit
    shouldCache = true

    private val methodTreeCache: mutable.Stack[mutable.Set[MethodTree]] = mutable.Stack.empty
    private val methodInvocationTreeCache: mutable.Stack[mutable.Set[MethodInvocationTree]] = mutable.Stack.empty
    pushNewCache() // populate cache for pre-class-visit operations

    var mixedInferenceVisitor: MixedInferenceVisitor = new MixedInferenceVisitor()(this)

    /**
     * Class and qualifier pair that is currently being visited by the ConsistencyVisitor.
     */
    val visitClassContext: mutable.Stack[(TypeElement, AnnotationMirror)] = mutable.Stack.empty

    /**
     * The qualifier that is currently being used to substitute @ThisConsistent.
     */
    val thisConsistentContext: mutable.Stack[AnnotationMirror] = mutable.Stack.empty


    def getVisitor: ConsistencyVisitor = checker.getVisitor.asInstanceOf[ConsistencyVisitor]

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
            case ElementKind.LOCAL_VARIABLE =>
                replaceThisConsistent(result)
            case _ =>
        }
        result
    }

    /**
     * @inheritdoc
     * Resolves @ThisConsistent for method invocations (in return types, parameters)
     */
    override def methodFromUse(tree: MethodInvocationTree): AnnotatedTypeFactory.ParameterizedExecutableType = {
        val useCache = methodInvocationTreeCache.top.contains(tree)
        if (!useCache) {
            methodInvocationTreeCache.top.add(tree)
        }

        withThisConsistentContext(tree, useCache) {
            val typ = super.methodFromUse(tree)
            replaceThisConsistent(typ.executableType)
            typ
        }
    }

    override def getAnnotatedType(tree: Tree): AnnotatedTypeMirror = tree match {
        case methodTree: MethodTree =>
            val useCache = methodTreeCache.top.contains(methodTree)
            if (!useCache) {
                methodTreeCache.top.add(methodTree)
            }
            withCache(useCache) {
                super.getAnnotatedType(tree)
            }
        case _ =>
            super.getAnnotatedType(tree)
    }

    /**
     * @inheritdoc
     * Called from getAnnotatedType after the annotations from the code and stub files are computed. In turn, calls
     * tree and type visitors.
     */
    override def addComputedTypeAnnotations(tree: Tree, typ: AnnotatedTypeMirror, iUseFlow: Boolean): Unit = {
        tree match {
            case invocation: MethodInvocationTree =>
                val useCache = methodInvocationTreeCache.top.contains(invocation)
                if (!useCache) {
                    methodInvocationTreeCache.top.add(invocation)
                }
                // the type of an invocation is the return type, which depends on the receiver object
                // for other types of trees, the context is set by the consistency visitor when entering a method tree
                withThisConsistentContext(invocation, useCache) {
                    super.addComputedTypeAnnotations(tree, typ, iUseFlow)
                }
            case _ =>
                super.addComputedTypeAnnotations(tree, typ, iUseFlow)
        }
    }

    override def addComputedTypeAnnotations(elt: Element, typ: AnnotatedTypeMirror): Unit = {
        // TODO: same as above, but we don't know the receiver, so the context must be set manually
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

    // #################################################################################################################
    // ### @ThisConsistent helpers
    // #################################################################################################################

    def withCache[R](useCache: Boolean)(f: => R): R = {
        val oldShouldCache = shouldCache
        shouldCache = useCache
        val result = f
        shouldCache = oldShouldCache
        result
    }

    /**
     * Executes a given function under a @ThisConsistent-context inferred from the given method invocation tree.
     * @param context the context under which to execute the function
     * @param f the function to execute
     * @return the result of the executed function
     */
    def withThisConsistentContext[R](context: MethodInvocationTree, useCache: Boolean = false)(f: => R): R = withCache(useCache) {
        thisConsistentContext.push(inferThisConsistentContext(context)(this))
        val result = f
        thisConsistentContext.pop()
        result
    }

    /**
     * Replaces all occurrences of @ThisConsistent in the given type if any are present. If the type is a
     * composite (e.g. generic type, method type) all components are searched for @ThisConsistent. The substitution
     * type is taken from the currently active context.
     * @param typ the type in which to substitute @ThisConsistent
     */
    def replaceThisConsistent(typ: AnnotatedTypeMirror): Unit = {
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

            case t if t.hasAnnotation(classOf[ThisConsistent]) =>
                typ.replaceAnnotation(newType)

            case _ => // nothing to do
        }

        if (thisConsistentContext.nonEmpty) {
            deepReplaceThisConsistent(typ, thisConsistentContext.top)
        }
    }

    def pushNewCache(): Unit = {
        methodTreeCache.push(mutable.Set.empty)
        methodInvocationTreeCache.push(mutable.Set.empty)
    }

    def popCache(): Unit = {
        methodTreeCache.pop()
        methodInvocationTreeCache.pop()
    }

    // #################################################################################################################
    // ### Checker-framework builder methods
    // #################################################################################################################

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
}
