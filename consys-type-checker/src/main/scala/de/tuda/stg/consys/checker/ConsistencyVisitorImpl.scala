package de.tuda.stg.consys.checker

import java.util
import com.sun.source.tree._
import SubConsistencyChecker.{StrongSubConsistencyChecker, WeakSubConsistencyChecker}
import de.tuda.stg.consys.annotations.{ReadOnly, Transactional}
import de.tuda.stg.consys.checker.qual.Mixed

import javax.lang.model.element.{AnnotationMirror, TypeElement}
import org.checkerframework.common.basetype.BaseTypeChecker
import org.checkerframework.framework.`type`.AnnotatedTypeMirror
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.{AnnotatedDeclaredType, AnnotatedExecutableType}
import org.checkerframework.javacutil.{AnnotationUtils, ElementUtils, TreeUtils}

import javax.lang.model.`type`.{DeclaredType, NoType}
import scala.collection.convert.ImplicitConversions.`iterable AsScalaIterable`

/**
	* Created on 05.03.19.
	*
	* @author Mirko Köhler
	*/
class ConsistencyVisitorImpl(baseChecker : BaseTypeChecker) extends InformationFlowTypeVisitor[ConsistencyAnnotatedTypeFactory](baseChecker){
	import TypeFactoryUtils._
	private implicit val tf: ConsistencyAnnotatedTypeFactory = atypeFactory

	val subCheckerMap: Map[String, Class[_ <: SubConsistencyChecker]] =
		Map(s"$checkerPackageName.qual.Strong" -> classOf[StrongSubConsistencyChecker],
			s"$checkerPackageName.qual.Weak" -> classOf[WeakSubConsistencyChecker])


	override def visitMemberSelect(node : MemberSelectTree, p : Void) : Void = {
		val recvType = atypeFactory.getAnnotatedType(node.getExpression)
		if (recvType.hasAnnotation(classOf[Mixed])
			&& TreeUtils.isFieldAccess(node)
			&& !TreeUtils.isExplicitThisDereference(node.getExpression)
			// class literals are treated as fields
			&& !TreeUtils.isClassLiteral(node)) {

			//checker.reportError(node, "mixed.field.access")
		}

		super.visitMemberSelect(node, p)
	}

	override def processClassTree(classTree: ClassTree): Unit = {
		println(">Class decl:  " + getQualifiedName(classTree))
		// TODO: clean up + we should explicitly run the inference here before moving on
		val mixed = atypeFactory.getAnnotatedType(classTree).getAnnotation(classOf[Mixed])
		val defaultOpLevel = if (mixed != null) TypeFactoryUtils.getMixedDefaultOp(mixed) else ""
		if (mixed != null) {
			atypeFactory.pushMixedClassContext(TreeUtils.elementFromDeclaration(classTree), defaultOpLevel)
			atypeFactory.inferenceVisitor.visitClass(classTree)
		}
		super.processClassTree(classTree)
		if (mixed != null)
			atypeFactory.popMixedClassContext()
	}

	def processMixedClassTree(classTree: ClassTree, defaultOpLevel: String): Unit = {
		println(">Class decl (noCache):  " + getQualifiedName(classTree))
		atypeFactory.pushMixedClassContext(TreeUtils.elementFromDeclaration(classTree), defaultOpLevel)
		super.processClassTree(classTree)
		atypeFactory.popMixedClassContext()
	}

	/*
		Check that implicit contexts are correct.
	 */
	override def visitAssignment(node : AssignmentTree, p : Void) : Void = {
		println(s"  >Var assign:\n" +
				s"   <$node>\n" +
				s"      where ${node.getVariable} -> ${atypeFactory.getAnnotatedType(node.getVariable)}\n" +
				s"      where ${node.getExpression} -> ${atypeFactory.getAnnotatedType(node.getExpression)}")

		checkAssignment(atypeFactory.getAnnotatedType(node.getVariable), atypeFactory.getAnnotatedType(node.getExpression), node)
		super.visitAssignment(node, p)
	}

	//compound assignment is, e.g., i += 23
	override def visitCompoundAssignment(node : CompoundAssignmentTree, p : Void) : Void = {
		checkAssignment(atypeFactory.getAnnotatedType(node.getVariable), atypeFactory.getAnnotatedType(node.getExpression), node)
		super.visitCompoundAssignment(node, p)
	}


	override def visitVariable(node : VariableTree, p : Void) : Void = {
		println(s"  >Var decl:\n" +
			s"   ${atypeFactory.getAnnotatedType(node)} ${node.getName}")

		val initializer: ExpressionTree = node.getInitializer
		if (initializer != null) checkAssignment(atypeFactory.getAnnotatedType(node), atypeFactory.getAnnotatedType(initializer), node)
		super.visitVariable(node, p)
	}

	private def checkAssignment(lhsType : AnnotatedTypeMirror, rhsType : AnnotatedTypeMirror, tree : Tree) : Unit = {
		if (transactionContext && (!implicitContext.allowsUpdatesTo(lhsType, tree))) //|| !implicitContext.allowsUpdatesFrom(rhsType, tree)))
			checker.reportError(tree, "assignment.type.implicitflow", lhsType, implicitContext.get, tree)

		if (lhsType.hasAnnotation(classOf[qual.Immutable]))
			checker.reportError(tree, "immutability.assignment.type")
	}

	override def visitMethodInvocation(node : MethodInvocationTree, p : Void) : Void = {
		if (methodInvocationIsTransaction(node)) {
			transactionContext = true
		}

		if (!transactionContext && methodInvocationIsReplicateOrLookup(node)) {
			checker.reportError(node, "invocation.replicate.transaction", node)
		}
		if (!transactionContext && methodInvocationIsRefAccess(node)) {
			checker.reportError(node, "invocation.ref.transaction", node)
		}
		if (!transactionContext && methodInvocationIsTransactional(node)) {
			checker.reportError(node, "invocation.method.transaction", node)
		}

		node.getMethodSelect match {
			case memberSelectTree : MemberSelectTree =>
				val expr : ExpressionTree = memberSelectTree.getExpression
				val recvType = atypeFactory.getAnnotatedType(expr)
				val methodType = atypeFactory.getAnnotatedType(TreeUtils.elementFromUse(node))

				if (expr != null && !methodInvocationIsRefOrGetField(node) && !recvType.hasAnnotation(classOf[Mixed]))
					checkMethodInvocationReceiver(recvType, methodType, node)

				if (recvType.hasAnnotation(classOf[Mixed]) && methodInvocationIsRefFieldAccess(node)) {
					//checker.reportError(node, "mixed.field.access")
				}

				// check implicit context on mixed method invocation
				if (recvType.hasAnnotation(classOf[Mixed])) {
					checkMethodInvocationOpLevel(recvType, node)
				}

			case _ =>
		}

		node.getArguments.forEach(argExpr =>
			checkMethodInvocationArgument(atypeFactory.getAnnotatedType(argExpr), node)
		)

		if (methodInvocationIsReplicate(node)) {
			val (isAllowed, src) = replicateIsAllowedForLevel(node)
			if (!isAllowed) checker.reportError(node, "replicate.class", node, src)
		}

		val r = super.visitMethodInvocation(node, p)

		if (methodInvocationIsTransaction(node)) {
			transactionContext = false
		}
		r
	}

	override def visitMethod(node: MethodTree, p: Void): Void = {
		var shouldClose = false
		if (!transactionContext && methodDeclarationIsTransactional(node)) {
			transactionContext = true
			shouldClose = true
		}

		val method = TreeUtils.elementFromDeclaration(node)
		if (method.getAnnotation(classOf[ReadOnly]) == null) {
			// enforce ReadOnly inheritance
			val overridden = ElementUtils.getOverriddenMethods(method, types).exists(m =>
				m.getAnnotation(classOf[ReadOnly]) != null)

			new ReadOnlyVisitor().visitMethod(node) match {
				case Nil if !overridden => // checker.reportWarning(node, "readonly.inference", node.getName)
				case _ if overridden => checker.reportError(node, "readonly.override", node.getName)
				case _ =>
			}
		} else {
			new ReadOnlyVisitor().visitMethod(node) match {
				case Nil =>
				case errors => errors.foreach(e =>
					checker.reportError(e, "readonly.declaration", node.getName, e))
			}
		}

		val r = super.visitMethod(node, p)
		if (shouldClose) {
			transactionContext = false
		}
		r
	}

	private def replicateIsAllowedForLevel(node: MethodInvocationTree): (Boolean, Object) = {
		// match 'classType' in 'ctx.replicate(_, _, Class<classType>)'
		val argType = atypeFactory.getAnnotatedType(node.getArguments.get(2))
		argType match {
			case adt: AnnotatedDeclaredType => adt.getTypeArguments.get(0) match {
				case classType: AnnotatedDeclaredType =>
					val qualifierName = AnnotationUtils.annotationName(classType.getAnnotationInHierarchy(getTopAnnotation))

					subCheckerMap.get(qualifierName) match {
						case Some(subChecker) =>
							val subCheckerTypeFactory: SubConsistencyAnnotatedTypeFactory = checker.getTypeFactoryOfSubchecker(subChecker)
							// having no sub checker means we are currently in a sub checker so we don't need to test replicate
							if (subCheckerTypeFactory == null)
								(true, null)
							else
								(subCheckerTypeFactory.isAllowed(classType.getUnderlyingType),
									subCheckerTypeFactory.getSrcForDisallowed(classType.getUnderlyingType))
						case None => (true, null)
					}
				}
				case _ => (true, null)
			case _ => (true, null)
		}
	}

	private def methodInvocationIsX(node: MethodInvocationTree, receiverName: String, methodNames: List[String]) : Boolean = {
		def checkMethodName(memberSelectTree: MemberSelectTree): Boolean = {
			val methodId = memberSelectTree.getIdentifier.toString
			methodNames.map(x => x == methodId).fold(false)(_ || _)
		}
		def checkReceiverNameInInterfaces(dt: DeclaredType, mst: MemberSelectTree): Boolean = dt.asElement() match {
			case te: TypeElement => te.getInterfaces.exists {
				case interfaceType: DeclaredType if getQualifiedName(interfaceType) == receiverName =>
					checkMethodName(mst)
				case interfaceType: DeclaredType =>
					checkReceiverNameInInterfaces(interfaceType, mst)
				case _ => false
			}
			case _ => false
		}
		def checkReceiverNameInSuperClass(dt: DeclaredType, mst: MemberSelectTree): Boolean = dt.asElement() match {
			case te: TypeElement => te.getSuperclass match {
				case _: NoType => false
				case dt: DeclaredType if getQualifiedName(dt) == receiverName =>
					checkMethodName(mst)
				case dt: DeclaredType =>
					checkReceiverNameInInterfaces(dt, mst) || checkReceiverNameInSuperClass(dt, mst)
				case _ => false
			}
			case _ => false
		}

		node.getMethodSelect match {
			case memberSelectTree : MemberSelectTree =>
				val receiverType = atypeFactory.getAnnotatedType(memberSelectTree.getExpression)
				receiverType match {
					// check for a direct name match
					case adt : AnnotatedDeclaredType if getQualifiedName(adt) == receiverName =>
						checkMethodName(memberSelectTree)
					// check for name match in interfaces or superclass
					case adt: AnnotatedDeclaredType =>
						checkReceiverNameInInterfaces(adt.getUnderlyingType, memberSelectTree) ||
							checkReceiverNameInSuperClass(adt.getUnderlyingType, memberSelectTree)
					case _ => false
				}
			case _ => false
		}
	}

	private def methodInvocationIsRefOrGetField(node: MethodInvocationTree): Boolean =
		methodInvocationIsX(node, s"$japiPackageName.Ref", List("ref", "getField"))

	private def methodInvocationIsRefAccess(node: MethodInvocationTree): Boolean =
		methodInvocationIsX(node, s"$japiPackageName.Ref", List("ref", "getField", "setField", "invoke"))

	private def methodInvocationIsReplicateOrLookup(node: MethodInvocationTree): Boolean =
		methodInvocationIsX(node, s"$japiPackageName.TransactionContext", List("replicate", "lookup"))

	private def methodInvocationIsReplicate(node: MethodInvocationTree): Boolean =
		methodInvocationIsX(node, s"$japiPackageName.TransactionContext", List("replicate"))

	private def methodInvocationIsTransaction(node: MethodInvocationTree): Boolean =
		methodInvocationIsX(node, s"$japiPackageName.Store", List("transaction"))

	private def methodInvocationIsRefFieldAccess(node: MethodInvocationTree): Boolean =
		methodInvocationIsX(node, s"$japiPackageName.Ref", List("setField", "getField"))

	private def methodInvocationIsSetField(node : MethodInvocationTree) : Boolean = node.getMethodSelect match {
		case memberSelectTree : MemberSelectTree =>
			val expr : ExpressionTree = memberSelectTree.getExpression
			val recvType = atypeFactory.getAnnotatedType(expr)

			println(s"expr = $expr, recvType = $recvType, method = ${memberSelectTree.getIdentifier}")
			println(recvType.asInstanceOf[AnnotatedDeclaredType].getUnderlyingType.asElement().getSimpleName.toString == "JRef")
			println(memberSelectTree.getIdentifier.toString == "setField")

			recvType match {
				case adt : AnnotatedDeclaredType if adt.getUnderlyingType.asElement().getSimpleName.toString == "JRef" =>
					if (memberSelectTree.getIdentifier.toString == "setField") {
						val setArg = node.getArguments.get(1)

						val setArgT = atypeFactory.getAnnotatedType(setArg)

						val annos = setArgT.getAnnotations

						println(s"args = ${node.getArguments}, argT = $annos")
					}
				case _ =>
			}

			false

		case _ =>
			false
	}

	private def methodDeclarationIsTransactional(node: MethodTree) : Boolean = {
		val annotations = node.getModifiers.getAnnotations
		annotations.exists((at: AnnotationTree) => atypeFactory.getAnnotatedType(at.getAnnotationType) match {
			case adt: AnnotatedDeclaredType =>
				getQualifiedName(adt) == s"$annoPackageName.Transactional"
			case _ =>
				false
		})
	}

	private def methodInvocationIsTransactional(node: MethodInvocationTree) : Boolean = {
		// get the correct method declaration for this invocation and check for annotation
		val execElem = TreeUtils.elementFromUse(node)
		null != atypeFactory.getDeclAnnotation(execElem, classOf[Transactional])
	}

	private def checkMethodInvocationReceiver(receiverType : AnnotatedTypeMirror, methodType: AnnotatedExecutableType, tree : Tree) : Unit = {
		if (transactionContext && !implicitContext.allowsAsReceiver(receiverType, tree))
			checker.reportError(tree, "invocation.receiver.implicitflow", receiverType, implicitContext.get, tree)

		if (receiverType.hasAnnotation(classOf[qual.Immutable]) &&
			ElementUtils.hasAnnotation(methodType.getElement, classOf[ReadOnly].getName))
			checker.reportError(tree, "immutability.invocation.receiver")
	}

	private def checkMethodInvocationArgument(argType : AnnotatedTypeMirror, tree : Tree) : Unit = {
		if (transactionContext && !implicitContext.allowsAsArgument(argType, tree))
			checker.reportError(tree, "invocation.argument.implicitflow", argType, implicitContext.get, tree)
	}

	private def checkMethodInvocationOpLevel(recvType: AnnotatedTypeMirror, tree: MethodInvocationTree): Unit = {
		if (transactionContext && recvType.hasAnnotation(classOf[Mixed]) && !implicitContext.allowsAsMixedInvocation(recvType, tree))
			checker.reportError(tree, "invocation.operation.implicitflow",
				getMixedOpForMethod(TreeUtils.elementFromUse(tree), getMixedDefaultOp(recvType.getAnnotation(classOf[Mixed]))),
				implicitContext.get, tree)
	}



	override protected def getAnnotation(typ : AnnotatedTypeMirror) : AnnotationMirror = { //can only include consistency annotations
		return typ.getAnnotationInHierarchy(getTopAnnotation)

		val annotations : util.Set[AnnotationMirror] = typ.getAnnotations
		if (annotations.size == 1) return annotations.iterator.next
		else if (annotations.isEmpty) return null
		throw new AssertionError("inferred an unexpected number of annotations. Expected 1 annotation, but got: " + annotations)
	}

	override protected def getEmptyContextAnnotation : AnnotationMirror = localAnnotation(atypeFactory)

	override protected def getTopAnnotation : AnnotationMirror = inconsistentAnnotation(atypeFactory)

	// TODO: this is a hack to circumvent a possible bug in the checkerframework, where type arguments with multiple
	//		 annotations get erased and can't be inferred. If we remove this, ref() calls crash the checker
	override def skipReceiverSubtypeCheck(node: MethodInvocationTree, methodDefinitionReceiver: AnnotatedTypeMirror, methodCallReceiver: AnnotatedTypeMirror): Boolean =
		true
}
