package de.tuda.stg.consys.checker

import com.sun.source.tree._
import de.tuda.stg.consys.annotations.Transactional
import de.tuda.stg.consys.annotations.methods.{StrongOp, WeakOp}
import de.tuda.stg.consys.checker.qual.Mixed

import javax.lang.model.element.{AnnotationMirror, ElementKind, Modifier, TypeElement}
import org.checkerframework.common.basetype.BaseTypeChecker
import org.checkerframework.dataflow.qual.SideEffectFree
import org.checkerframework.framework.`type`.AnnotatedTypeMirror
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.AnnotatedExecutableType
import org.checkerframework.javacutil.{AnnotationUtils, ElementUtils, TreeUtils, TypesUtils}
import org.jmlspecs.annotation.Pure

import javax.lang.model.`type`.TypeKind
import scala.collection.convert.ImplicitConversions.`iterable AsScalaIterable`
import scala.collection.mutable

/**
	* Created on 05.03.19.
	*
	* @author Mirko Köhler
	*/
class ConsistencyVisitor(baseChecker : BaseTypeChecker) extends InformationFlowTypeVisitor[ConsistencyAnnotatedTypeFactory](baseChecker){
	import TypeFactoryUtils._

	private val consistencyChecker = baseChecker.asInstanceOf[ConsistencyChecker]

	private var isInConstructor: Boolean = false

	type ClassName = String
	type QualifierName = (String, String)
	private val classVisitCache: mutable.Map[(ClassName, QualifierName), (String, String)] = mutable.Map.empty
	private val classVisitQueue: mutable.Set[(ClassName, QualifierName)] = mutable.Set.empty
	private val classVisitQueueReported: mutable.Set[(ClassName, QualifierName)] = mutable.Set.empty

	override def createTypeFactory(): ConsistencyAnnotatedTypeFactory = new ConsistencyAnnotatedTypeFactory(baseChecker)

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

	/*
		Check that implicit contexts are correct.
	 */
	override def visitAssignment(node : AssignmentTree, p : Void) : Void = {
		checkAssignment(atypeFactory.getAnnotatedType(node.getVariable), atypeFactory.getAnnotatedType(node.getExpression), node)
		super.visitAssignment(node, p)
	}

	//compound assignment is, e.g., i += 23
	override def visitCompoundAssignment(node : CompoundAssignmentTree, p : Void) : Void = {
		checkAssignment(atypeFactory.getAnnotatedType(node.getVariable), atypeFactory.getAnnotatedType(node.getExpression), node)
		super.visitCompoundAssignment(node, p)
	}

	override def visitVariable(node : VariableTree, p : Void) : Void = {
		val initializer: ExpressionTree = node.getInitializer
		if (initializer != null) checkAssignment(atypeFactory.getAnnotatedType(node), atypeFactory.getAnnotatedType(initializer), node)
		super.visitVariable(node, p)
	}

	private def checkAssignment(lhsType : AnnotatedTypeMirror, rhsType : AnnotatedTypeMirror, tree : Tree) : Unit = {
		// check implicit context constraints
		if (transactionContext && (!implicitContext.allowsUpdatesTo(lhsType, tree)))
			checker.reportError(tree, "assignment.type.implicitflow", lhsType, implicitContext.get, tree)

		// check immutability constraints
		tree match {
			case _: VariableTree => // variable initialization at declaration is allowed
			case assign: AssignmentTree => assign.getVariable match {
				case id: IdentifierTree if TreeUtils.elementFromUse(id).getKind != ElementKind.FIELD => // reassigning variables is allowed
				case id: IdentifierTree if isInConstructor && TreeUtils.elementFromUse(id).getKind == ElementKind.FIELD => // allow field initialization in constructor
				case mst: MemberSelectTree => mst.getExpression match {
					case id: IdentifierTree if isInConstructor && TreeUtils.isExplicitThisDereference(id) => // allow field initialization in constructor
					case _ => if (lhsType.hasEffectiveAnnotation(classOf[qual.Immutable]) && !TypesUtils.isPrimitiveOrBoxed(lhsType.getUnderlyingType))
						checker.reportError(tree, "immutability.assignment.type")
				}
				case _ => if (lhsType.hasEffectiveAnnotation(classOf[qual.Immutable]) && !TypesUtils.isPrimitiveOrBoxed(lhsType.getUnderlyingType))
					checker.reportError(tree, "immutability.assignment.type")
			}
			case _ =>
		}
	}

	override def visitMemberSelect(node: MemberSelectTree, p: Void): Void = {
		// restrict private and protected field access through Ref objects
		node.getExpression match {
			case mTree: MethodInvocationTree if isRefDereference(mTree) =>
				val elt = TreeUtils.elementFromUse(node)
				if ((elt.getKind == ElementKind.FIELD || elt.getKind == ElementKind.METHOD) && isPrivateOrProtected(elt))
					checker.reportWarning(node, "ref.member.access")
			case _ =>
		}

		super.visitMemberSelect(node, p)
	}

	override def visitMethodInvocation(node : MethodInvocationTree, p : Void) : Void = {
		val prevIsTransactionContext = transactionContext
		if (isTransaction(node))
			transactionContext = true

		// check transaction violations
		if (!transactionContext) {
			if (isReplicateOrLookup(node))
				checker.reportError(node, "invocation.replicate.transaction", node)
			if (isAnyRefAccess(node))
				checker.reportError(node, "invocation.ref.transaction", node)
			if (methodInvocationIsTransactional(node))
				checker.reportError(node, "invocation.method.transaction", node)
		}

		if (methodInvocationIsCompiledRef(node))
			checker.reportWarning(node, "compiler.ref")

		node.getMethodSelect match {
			case memberSelectTree : MemberSelectTree =>
				val expr : ExpressionTree = memberSelectTree.getExpression
				val recvType = atypeFactory.getAnnotatedType(expr)
				val methodType = atypeFactory.getAnnotatedType(TreeUtils.elementFromUse(node))

				// check receiver w.r.t. implicit context
				if (expr != null && !methodInvocationIsRefOrGetField(node)) {
					if (recvType.hasEffectiveAnnotation(classOf[Mixed]))
						checkMethodInvocationOpLevel(recvType, node)
					else
						checkMethodInvocationReceiver(recvType, node)
				}

				// check immutability on receiver
				if (!isAnyRefAccess(node) &&
					!isReplicateOrLookup(node) &&
					!methodType.getElement.getModifiers.contains(Modifier.STATIC)) {

					checkMethodInvocationReceiverMutability(recvType, methodType, node)
				}

			case _: IdentifierTree => // implicit this receiver
				// construct type for implicit this
				val objectMirror = TypesUtils.typeFromClass(classOf[Object], atypeFactory.types, atypeFactory.getElementUtils)
				val recvType = AnnotatedTypeMirror.createType(objectMirror, atypeFactory, true)
				recvType.addAnnotation(tf.peekVisitClassContext._2)
				recvType.addAnnotation(mutableAnnotation)

				// check receiver w.r.t. implicit context
				if (!methodInvocationIsRefOrGetField(node)) {
					if (recvType.hasEffectiveAnnotation(classOf[Mixed]))
						checkMethodInvocationOpLevel(recvType, node)
					else
						checkMethodInvocationReceiver(recvType, node)
				}

				// no immutability check since 'this' is always mutable
		}

		// check arguments w.r.t. implicit context
		val methodType = atypeFactory.getAnnotatedTypeWithContext(TreeUtils.elementFromUse(node), node)
		(methodType.getParameterTypes zip node.getArguments).foreach(entry => {
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

	override def visitMethod(node: MethodTree, p: Void): Void = {
		var shouldClose = false
		val prevIsTransactionContext = transactionContext
		if (!transactionContext && methodDeclarationIsTransactional(node)) {
			transactionContext = true
			shouldClose = true
		}

		val prevIsConstructor = isInConstructor
		if (TreeUtils.isConstructor(node)) {
			isInConstructor = true
		}

		// check transaction inheritance rules
		if (hasAnnotation(node.getModifiers, classOf[Transactional])) {
			val overrides = ElementUtils.getOverriddenMethods(TreeUtils.elementFromDeclaration(node), tf.types)
			overrides.foreach(overridden => {
				if (!hasAnnotation(overridden, classOf[Transactional])) {
					checker.reportError(node, "transaction.override", overridden.getEnclosingElement)
				}
			})
		}

		// check operation level override rules
		if (tf.isInMixedClassContext && !(hasAnnotation(node.getModifiers, classOf[SideEffectFree]) ||
			hasAnnotation(node.getModifiers, classOf[Pure]))) {

			val overrides = ElementUtils.getOverriddenMethods(TreeUtils.elementFromDeclaration(node), tf.types)
			overrides.foreach(m => {
				if (hasAnnotation(m, classOf[WeakOp]) && !hasAnnotation(node.getModifiers, classOf[WeakOp]))
					checker.reportError(node, "mixed.inheritance.operation.incompatible",
						if (hasAnnotation(node.getModifiers, classOf[StrongOp])) "StrongOp" else "Default",
						"WeakOp", m.getReceiverType)
				else if (!hasAnnotation(m, classOf[StrongOp]) && !hasAnnotation(m, classOf[WeakOp]) &&
					hasAnnotation(node.getModifiers, classOf[StrongOp]))
					checker.reportError(node, "mixed.inheritance.operation.incompatible",
						"StrongOp", "Default", m.getReceiverType)
			})
		}

		// check mutable on return type
		if (!AnnotationUtils.areSame(tf.peekVisitClassContext._2, inconsistentAnnotation)) {
			val mods = TreeUtils.elementFromDeclaration(node).getModifiers
			val annotatedReturnType = tf.getAnnotatedType(node.asInstanceOf[Tree]).asInstanceOf[AnnotatedExecutableType].getReturnType
			val returnType = annotatedReturnType.getUnderlyingType
			if (!(TreeUtils.isConstructor(node) ||
				returnType.getKind == TypeKind.VOID ||
				TypesUtils.isPrimitiveOrBoxed(returnType) ||
				mods.contains(Modifier.STATIC) ||
				mods.contains(Modifier.PRIVATE) ||
				mods.contains(Modifier.PROTECTED)) &&
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

	override def checkOverride(overriderTree: MethodTree,
							   overriderMethodType: AnnotatedExecutableType,
							   overriderType: AnnotatedTypeMirror.AnnotatedDeclaredType,
							   overriddenMethodType: AnnotatedExecutableType,
							   overriddenType: AnnotatedTypeMirror.AnnotatedDeclaredType): Boolean = {
		// Adapt @ThisConsistent based on currently visited class, since checkOverride is only called for methods
		// implemented in the current class.
		atypeFactory.withContext(atypeFactory.peekVisitClassContext._2) {
			atypeFactory.replaceThisConsistent(overriderMethodType)
			atypeFactory.replaceThisConsistent(overriddenMethodType)
		}
		super.checkOverride(overriderTree, overriderMethodType, overriderType, overriddenMethodType, overriddenType)
	}

	private def methodInvocationIsRefOrGetField(node: MethodInvocationTree): Boolean =
		methodInvocationIsAny(node, s"$japiPackageName.Ref", List("ref", "getField"))

	private def methodInvocationIsCompiledRef(node: MethodInvocationTree): Boolean =
		methodInvocationIsAny(node, s"$japiPackageName.Ref", List("invoke", "getField", "setField"))

	private def methodDeclarationIsTransactional(node: MethodTree) : Boolean = {
		val execElem = TreeUtils.elementFromDeclaration(node)
		null != atypeFactory.getDeclAnnotation(execElem, classOf[Transactional])
	}

	private def methodInvocationIsTransactional(node: MethodInvocationTree) : Boolean = {
		val execElem = TreeUtils.elementFromUse(node)
		null != atypeFactory.getDeclAnnotation(execElem, classOf[Transactional])
	}

	private def checkMethodInvocationReceiver(receiverType : AnnotatedTypeMirror, tree : Tree) : Unit = {
		if (transactionContext && !implicitContext.allowsAsReceiver(receiverType, tree))
			checker.reportError(tree, "invocation.receiver.implicitflow", receiverType, implicitContext.get, tree)
	}

	private def checkMethodInvocationReceiverMutability(receiverType : AnnotatedTypeMirror, methodType: AnnotatedExecutableType, tree : MethodInvocationTree) : Unit = {
		if (!(transactionContext ||
			!tf.isVisitClassContextEmpty && !AnnotationUtils.areSame(tf.peekVisitClassContext._2, inconsistentAnnotation)))
			return

		if (receiverType.hasEffectiveAnnotation(classOf[qual.Immutable]) && !isSideEffectFree(methodType.getElement))
			checker.reportError(tree, "immutability.invocation.receiver")
	}

	private def checkMethodInvocationArgument(argType : AnnotatedTypeMirror, tree : Tree) : Unit = {
		if (transactionContext && !implicitContext.allowsAsArgument(argType, tree))
			checker.reportError(tree, "invocation.argument.implicitflow", argType, implicitContext.get, tree)
	}

	private def checkMethodInvocationOpLevel(recvType: AnnotatedTypeMirror, tree: MethodInvocationTree): Unit = {
		if (transactionContext && recvType.hasEffectiveAnnotation(classOf[Mixed]) && !implicitContext.allowsAsMixedInvocation(recvType, tree))
			checker.reportError(tree, "invocation.operation.implicitflow",
				getMixedOpForMethod(TreeUtils.elementFromUse(tree), getNameForMixedDefaultOp(recvType.getEffectiveAnnotation(classOf[Mixed]))),
				implicitContext.get, tree)
	}

	private def toQualifierName(qualifier: AnnotationMirror): QualifierName = {
		if (isMixedQualifier(qualifier))
			(getQualifiedName(qualifier), getNameForMixedDefaultOp(repairMixed(qualifier)))
		else
			(getQualifiedName(qualifier), "")
	}


	override protected def getAnnotation(typ : AnnotatedTypeMirror) : AnnotationMirror = {
		typ.getEffectiveAnnotationInHierarchy(getTopAnnotation)
	}

	override protected def getEmptyContextAnnotation : AnnotationMirror = localAnnotation

	override protected def getTopAnnotation : AnnotationMirror = inconsistentAnnotation

	// TODO: this is a hack to circumvent a possible bug in the checkerframework, where type arguments with multiple
	//		 annotations get erased and can't be inferred. If we remove this, ref() calls crash the checker
	override def skipReceiverSubtypeCheck(node: MethodInvocationTree, methodDefinitionReceiver: AnnotatedTypeMirror, methodCallReceiver: AnnotatedTypeMirror): Boolean =
		true
}
