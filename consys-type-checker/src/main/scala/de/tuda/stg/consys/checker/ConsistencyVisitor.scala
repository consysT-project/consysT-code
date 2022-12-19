package de.tuda.stg.consys.checker

import com.sun.source.tree._
import de.tuda.stg.consys.checker.qual.Mixed
import org.checkerframework.common.basetype.BaseTypeChecker
import org.checkerframework.framework.`type`.{AnnotatedTypeMirror, AnnotatedTypeParameterBounds}
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.{AnnotatedDeclaredType, AnnotatedExecutableType}
import org.checkerframework.javacutil.{AnnotationUtils, ElementUtils, TreeUtils, TypesUtils}

import java.util
import javax.lang.model.`type`.TypeKind
import javax.lang.model.element.{AnnotationMirror, ElementKind, TypeElement}
import scala.collection.mutable
import scala.jdk.CollectionConverters._

/**
	* Created on 05.03.19.
	*
	* @author Mirko Köhler
	*/
class ConsistencyVisitor(baseChecker : BaseTypeChecker) extends InformationFlowTypeVisitor[ConsistencyAnnotatedTypeFactory](baseChecker){
	import TypeFactoryUtils._

	private val consistencyChecker = baseChecker.asInstanceOf[ConsistencyChecker]

	type ClassName = String
	/**
	 * Tuple from (qualifier name, default op name if qualifier=Mixed else empty)
	 */
	type QualifierName = (String, String)
	type Errors = String
	type Warnings = String

	private val classVisitCache: mutable.Map[(ClassName, QualifierName), (Errors, Warnings)] = mutable.Map.empty
	private val classVisitQueue: mutable.Set[(ClassName, QualifierName)] = mutable.Set.empty
	private val classVisitQueueReported: mutable.Set[(ClassName, QualifierName)] = mutable.Set.empty

	private var isInConstructor: Boolean = false

	override def processClassTree(classTree: ClassTree): Unit = {
		val className = getQualifiedName(TreeUtils.elementFromDeclaration(classTree))
		var upperBound = atypeFactory.getAnnotatedType(classTree.asInstanceOf[Tree]).getAnnotationInHierarchy(inconsistentAnnotation)
		upperBound = repairMixed(upperBound)

		// process class for upper bound with directly throwing errors
		processClassTree(classTree, upperBound)

		getConsistencyQualifiers.
			filter(q => tf.getQualifierHierarchy.isSubtype(q, upperBound) && !AnnotationUtils.areSame(q, upperBound)).
			foreach(q => {
				val qualifier = repairMixed(q)

				// process class without throwing errors (but caching them)
				consistencyChecker.enableLogCapture()
				processClassTree(classTree, qualifier)
				val (errors, warnings) = consistencyChecker.disableLogCapture()
				classVisitCache.put((className, toQualifierName(qualifier)), (errors, warnings))

				// report errors if the class is queued
				if (classVisitQueue.contains((className, toQualifierName(qualifier)))) {
					reportQueuedErrors(classTree, className, qualifier, errors, warnings)
					classVisitQueueReported.add((className, toQualifierName(qualifier)))
				}
			})
	}

	def queueClassVisit(classElement: TypeElement, annotation: AnnotationMirror): Unit = {
		val className = getQualifiedName(classElement)
		val qualifierName = toQualifierName(annotation)

		if (classVisitQueueReported.contains((className, qualifierName)))
			return

		classVisitCache.get(className, qualifierName) match {
			case Some((errors, warnings)) =>
				reportQueuedErrors(classElement, className, annotation, errors, warnings)
				classVisitQueueReported.add((className, qualifierName))

			case None if !classVisitQueue.contains(className, toQualifierName(annotation)) =>
				classVisitQueue.add(className, qualifierName)

			case _ =>
		}
	}

	private def reportQueuedErrors(source: Object, className: String, annotation: AnnotationMirror, errors: String, warnings: String): Unit = {
		if (errors.nonEmpty)
			checker.reportError(source, "consistency.type.use.incompatible",
				getQualifiedName(annotation), className, errors)
		if (warnings.nonEmpty)
			checker.reportWarning(source, "consistency.type.use.incompatible",
				getQualifiedName(annotation), className, errors)
	}

	/**
	 * Visits a class tree under a specific consistency qualifier
	 */
	private def processClassTree(classTree: ClassTree, annotation: AnnotationMirror): Unit = {
		val classElement = TreeUtils.elementFromDeclaration(classTree)
		val className = getQualifiedName(classElement)
		val qualifierName = toQualifierName(annotation)

		if (classVisitCache.contains(className, qualifierName)) return
		else classVisitCache.put((className, qualifierName), ("", ""))

		tf.pushVisitClassContext(classElement, annotation)
		if (isMixedQualifier(annotation))
			tf.mixedInferenceVisitor.processClass(classTree, annotation)
		super.processClassTree(classTree)
		tf.popVisitClassContext()
	}

	private def toQualifierName(qualifier: AnnotationMirror): QualifierName = {
		if (isMixedQualifier(qualifier))
			(getQualifiedName(qualifier), getNameForMixedDefaultOp(repairMixed(qualifier)))
		else
			(getQualifiedName(qualifier), "")
	}


	// #################################################################################################################
	// ### Assignment checks
	// #################################################################################################################

	/**
	 * @inheritdoc
	 * Standard assignment (e.g. i = 1)
	 */
	override def visitAssignment(node : AssignmentTree, p : Void) : Void = {
		checkAssignment(atypeFactory.getAnnotatedType(node.getVariable), atypeFactory.getAnnotatedType(node.getExpression), node)
		super.visitAssignment(node, p)
	}

	/**
	 * @inheritdoc
	 * Compound assignment (e.g. i += 1)
	 */
	override def visitCompoundAssignment(node : CompoundAssignmentTree, p : Void) : Void = {
		checkAssignment(atypeFactory.getAnnotatedType(node.getVariable), atypeFactory.getAnnotatedType(node.getExpression), node)
		super.visitCompoundAssignment(node, p)
	}

	/**
	 * @inheritdoc
	 * Assignment at the initialization of a variable declaration (e.g. int i = 1)
	 */
	override def visitVariable(node : VariableTree, p : Void) : Void = {
		val initializer: ExpressionTree = node.getInitializer
		if (initializer != null) checkAssignment(atypeFactory.getAnnotatedType(node), atypeFactory.getAnnotatedType(initializer), node)
		super.visitVariable(node, p)
	}

	/**
	 * Checks implicit flow and immutability constraints for assignment operations.
	 */
	private def checkAssignment(lhsType : AnnotatedTypeMirror, rhsType : AnnotatedTypeMirror, tree : Tree) : Unit = {
		// check implicit context constraints
		if (transactionContext && (!implicitContext.allowsUpdatesTo(lhsType, tree)))
			checker.reportError(tree, "assignment.type.implicitflow", lhsType, implicitContext.get, tree)

		// check immutability constraints
		tree match {
			case _: VariableTree => // allows immutable variable initialization at declaration
			case assign: AssignmentTree => assign.getVariable match {
				case id: IdentifierTree if TreeUtils.elementFromUse(id).getKind != ElementKind.FIELD => // allows reassigning local immutable variables
				case id: IdentifierTree if isInConstructor && TreeUtils.elementFromUse(id).getKind == ElementKind.FIELD => // allows field initialization in constructor
				case mst: MemberSelectTree => mst.getExpression match {
					case id: IdentifierTree if isInConstructor && TreeUtils.isExplicitThisDereference(id) => // allows field initialization in constructor
					case _ => if (lhsType.hasEffectiveAnnotation(classOf[qual.Immutable]) && !TypesUtils.isPrimitiveOrBoxed(lhsType.getUnderlyingType))
						checker.reportError(tree, "immutability.assignment.type")
				}
				case _ => if (lhsType.hasEffectiveAnnotation(classOf[qual.Immutable]) && !TypesUtils.isPrimitiveOrBoxed(lhsType.getUnderlyingType))
					checker.reportError(tree, "immutability.assignment.type")
			}
			case _ =>
		}
	}


	// #################################################################################################################
	// ### Member access & method invocation checks
	// #################################################################################################################

	/**
	 * @inheritdoc
	 * Restricts private and protected member access through Ref objects (e.g. obj.ref().i)
	 */
	override def visitMemberSelect(node: MemberSelectTree, p: Void): Void = {
		// node is <expression.identifier>, so we check if <expression> is a ref() call and
		// then examine the concrete element that is accessed by <identifier>
		node.getExpression match {
			case mTree: MethodInvocationTree if isRefDereference(mTree) =>
				val elt = TreeUtils.elementFromUse(node)
				if ((elt.getKind == ElementKind.FIELD || elt.getKind == ElementKind.METHOD) && isPrivateOrProtected(elt))
					checker.reportWarning(node, "ref.member.access")
			case _ =>
		}

		super.visitMemberSelect(node, p)
	}

	/**
	 * @inheritdoc
	 *   - Checks that a method call does not violate transactional rules.
	 *   - Checks that the receiver does not violate implicit flow and immutability constraints.
	 *   - Checks that method invocation arguments do not violate implicit flow constraints
	 */
	override def visitMethodInvocation(node : MethodInvocationTree, p : Void) : Void = {
		val prevIsTransactionContext = transactionContext
		if (isTransaction(node))
			transactionContext = true

		val callee = TreeUtils.elementFromUse(node)

		// check transaction violations
		if (!transactionContext) {
			if (isReplicateOrLookup(node))
				checker.reportError(node, "invocation.replicate.transaction", node)
			if (isAnyRefAccess(node))
				checker.reportError(node, "invocation.ref.transaction", node)
			if (isDeclaredTransactional(callee))
				checker.reportError(node, "invocation.method.transaction", node)
		}

		// check that no Ref methods other than ref() are used (i.e. invoke(), getField(), setField()), as these are
		// generated by the compiler and should therefore not be present during type checking
		if (isCompiledRefAccess(node))
			checker.reportWarning(node, "compiler.ref")

		node.getMethodSelect match {
			case memberSelectTree : MemberSelectTree =>
				val expr : ExpressionTree = memberSelectTree.getExpression
				val recvType = atypeFactory.getAnnotatedType(expr)

				// check receiver w.r.t. implicit context and mutability
				if (!isRefDereference(node) && !isReplicateOrLookup(node))
					checkMethodInvocationReceiver(recvType, node)

			case _: IdentifierTree => // implicit this receiver
				// construct type for implicit 'this'
				val objectMirror = TypesUtils.typeFromClass(classOf[Object], atypeFactory.types, atypeFactory.getElementUtils)
				val recvType = AnnotatedTypeMirror.createType(objectMirror, atypeFactory, true)
				// 'this' has the type of the current class
				recvType.addAnnotation(tf.peekVisitClassContext._2)
				// 'this' is always mutable
				recvType.addAnnotation(mutableAnnotation)

				// check receiver w.r.t. implicit context and mutability
				checkMethodInvocationReceiver(recvType, node)
		}

		// @ThisConsistent in method type must be adapted to the context of the invocation
		val methodType = atypeFactory.withContext(node) {
			atypeFactory.getAnnotatedType(callee)
		}
		// check arguments w.r.t. implicit context
		(methodType.getParameterTypes.asScala zip node.getArguments.asScala).foreach(entry => {
			val (paramType, argExpr) = entry
			// arguments taken as immutable parameters cannot violate implicit context
			if (!paramType.hasAnnotation(immutableAnnotation))
				checkMethodInvocationArgument(atypeFactory.getAnnotatedType(argExpr), node)
		})

		val r = super.visitMethodInvocation(node, p)

		if (isTransaction(node))
			transactionContext = prevIsTransactionContext
		r
	}

	/**
	 * Checks implicit flow and immutability constraints on a receiver type.
	 * Constraints are only checked inside transactions.
	 */
	private def checkMethodInvocationReceiver(recvType: AnnotatedTypeMirror, tree: MethodInvocationTree): Unit = {
		// implicit context and immutability constraints are only checked in transactions
		if (!transactionContext) return

		val method = TreeUtils.elementFromUse(tree)

		// check implicit context constraints
		val mixedQualifier = recvType.getEffectiveAnnotation(classOf[Mixed])
		if (mixedQualifier != null && !implicitContext.allowsAsMixedInvocation(recvType, tree)) {
			checker.reportError(tree, "invocation.operation.implicitflow",
				getMixedOpForMethod(method, getNameForMixedDefaultOp(mixedQualifier)), implicitContext.get, tree)
		} else if (mixedQualifier == null && !implicitContext.allowsAsReceiver(recvType, tree)) {
			checker.reportError(tree, "invocation.receiver.implicitflow", recvType, implicitContext.get, tree)
		}

		// check immutability constraints
		if (recvType.hasEffectiveAnnotation(classOf[qual.Immutable]) && !isDeclaredSideEffectFree(method) && !isStatic(method))
			checker.reportError(tree, "immutability.invocation.receiver")
	}

	/**
	 * Checks implicit flow constraints for method invocations arguments.
	 * Constraints are only checked inside transactions.
	 */
	private def checkMethodInvocationArgument(argType: AnnotatedTypeMirror, tree: Tree): Unit = {
		if (transactionContext && !implicitContext.allowsAsArgument(argType, tree))
			checker.reportError(tree, "invocation.argument.implicitflow", argType, implicitContext.get, tree)
	}


	// #################################################################################################################
	// ### Method declarations
	// #################################################################################################################

	/**
	 * @inheritdoc
	 *   - Checks override rules for transactional methods
	 *   - Checks override rules for mixed operation levels
	 */
	override def visitMethod(node: MethodTree, p: Void): Void = {
		var shouldClose = false
		val prevIsTransactionContext = transactionContext

		val method = TreeUtils.elementFromDeclaration(node)

		if (!transactionContext && isDeclaredTransactional(method)) {
			transactionContext = true
			shouldClose = true
		}

		val prevIsConstructor = isInConstructor
		if (TreeUtils.isConstructor(node)) {
			isInConstructor = true
		}

		val overrides = ElementUtils.getOverriddenMethods(method, tf.types).asScala

		// check transaction override rules
		if (isDeclaredTransactional(method)) {
			overrides.foreach(overridden => {
				if (!isDeclaredTransactional(overridden))
					checker.reportError(node, "transaction.override", overridden.getEnclosingElement)
			})
		}

		// check operation level override rules
		if (tf.isInMixedClassContext && !isDeclaredSideEffectFree(method)) {
			overrides.foreach(overridden => {
				if (isDeclaredWeakOp(overridden) && !isDeclaredWeakOp(method))
					checker.reportError(node, "mixed.inheritance.operation.incompatible",
						if (isDeclaredStrongOp(method)) "StrongOp" else "Default",
						"WeakOp", overridden.getReceiverType)
				else if (isDeclaredDefaultOp(overridden) && isDeclaredStrongOp(method))
					checker.reportError(node, "mixed.inheritance.operation.incompatible",
						"StrongOp", "Default", overridden.getReceiverType)
			})
		}

		// check that return type is not mutable for side-effect-free method
		// return types can't be mutable, since we could then return fields through immutable references
		if (!tf.isInInconsistentClassContext) {
			val annotatedReturnType = tf.getAnnotatedType(node.asInstanceOf[Tree]).asInstanceOf[AnnotatedExecutableType].getReturnType
			val returnType = annotatedReturnType.getUnderlyingType
			if (!(TreeUtils.isConstructor(node) ||
				returnType.getKind == TypeKind.VOID ||
				TypesUtils.isPrimitiveOrBoxed(returnType) ||
				isStatic(method) ||
				isPrivateOrProtected(method)) &&
				isDeclaredSideEffectFree(method) &&
				annotatedReturnType.hasEffectiveAnnotation(mutableAnnotation))
			{
				checker.reportError(node.getReturnType, "immutability.return.type")
			}
		}

		val r = super.visitMethod(node, p)

		if (TreeUtils.isConstructor(node))
			isInConstructor = prevIsConstructor
		if (shouldClose)
			transactionContext = prevIsTransactionContext
		r
	}

	/**
	 * @inheritdoc
	 * Adapts [[de.tuda.stg.consys.checker.qual.ThisConsistent]] for method override checks.
	 */
	override def checkOverride(overriderTree: MethodTree,
							   overriderMethodType: AnnotatedExecutableType,
							   overriderType: AnnotatedDeclaredType,
							   overriddenMethodType: AnnotatedExecutableType,
							   overriddenType: AnnotatedDeclaredType): Boolean = {
		// Adapt @ThisConsistent based on currently visited class, since checkOverride is only called for methods
		// implemented in the current class.
		atypeFactory.withContext(atypeFactory.peekVisitClassContext._2) {
			atypeFactory.replaceThisConsistent(overriderMethodType)
			atypeFactory.replaceThisConsistent(overriddenMethodType)
		}
		super.checkOverride(overriderTree, overriderMethodType, overriderType, overriddenMethodType, overriddenType)
	}

	override def checkTypeArguments(toptree: Tree,
									paramBounds: util.List[_ <: AnnotatedTypeParameterBounds],
									typeargs: util.List[_ <: AnnotatedTypeMirror],
									typeargTrees: util.List[_ <: Tree],
									typeOrMethodName: CharSequence,
									paramNames: util.List[_]): Unit = {
		atypeFactory.withContext(atypeFactory.peekVisitClassContext._2) {
			typeargs.forEach(typeArg => {
				//atypeFactory.deepReplaceThisConsistent(typeArg)
			})
		}
		super.checkTypeArguments(toptree, paramBounds, typeargs, typeargTrees, typeOrMethodName, paramNames)
	}


	// #################################################################################################################
	// ### InformationFlowTypeVisitor overrides
	// #################################################################################################################

	override protected def getAnnotation(typ : AnnotatedTypeMirror) : AnnotationMirror = {
		typ.getEffectiveAnnotationInHierarchy(getTopAnnotation)
	}

	override protected def getEmptyContextAnnotation : AnnotationMirror = localAnnotation

	override protected def getTopAnnotation : AnnotationMirror = inconsistentAnnotation


	// #################################################################################################################
	// ### Misc
	// #################################################################################################################

	override def createTypeFactory(): ConsistencyAnnotatedTypeFactory = new ConsistencyAnnotatedTypeFactory(baseChecker)

	// TODO: this is a hack to circumvent a possible bug in the checkerframework, where type arguments with multiple
	//		 annotations get erased and can't be inferred. If we remove this, ref() calls crash the checker
	override def skipReceiverSubtypeCheck(node: MethodInvocationTree,
										  methodDefinitionReceiver: AnnotatedTypeMirror,
										  methodCallReceiver: AnnotatedTypeMirror): Boolean = true
}
