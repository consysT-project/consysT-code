package de.tuda.stg.consys.checker

import java.util
import com.sun.source.tree._
import SubConsistencyChecker.{StrongSubConsistencyChecker, WeakSubConsistencyChecker}
import de.tuda.stg.consys.annotations.Transactional
import de.tuda.stg.consys.annotations.methods.{StrongOp, WeakOp}
import de.tuda.stg.consys.checker.qual.Mixed
import de.tuda.stg.consys.checker.TypeFactoryUtils._

import javax.lang.model.element.{AnnotationMirror, ElementKind, TypeElement}
import org.checkerframework.common.basetype.BaseTypeChecker
import org.checkerframework.dataflow.qual.SideEffectFree
import org.checkerframework.framework.`type`.AnnotatedTypeMirror
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.{AnnotatedDeclaredType, AnnotatedExecutableType}
import org.checkerframework.javacutil
import org.checkerframework.javacutil.{AnnotationUtils, ElementUtils, TreeUtils, TypesUtils}
import org.jmlspecs.annotation.Pure

import java.lang.annotation.Annotation
import javax.lang.model.`type`.{DeclaredType, NoType}
import scala.collection.convert.ImplicitConversions.`iterable AsScalaIterable`
import scala.collection.mutable

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

	val classVisitCache: mutable.Set[(TypeElement, AnnotationMirror)] = mutable.Set.empty
	val classVisitQueue: mutable.Set[(TypeElement, AnnotationMirror)] = mutable.Set.empty
	val treeMap: mutable.Map[TypeElement, ClassTree] = mutable.Map.empty

	override def processClassTree(classTree: ClassTree): Unit = {
		/*
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

		//return

		 */

		val upperBound = atypeFactory.getAnnotatedType(classTree).getAnnotationInHierarchy(inconsistentAnnotation)
		processClassTree(classTree, upperBound, checker.getLintOption("libMode"))

		val classElement = TreeUtils.elementFromDeclaration(classTree)
		classVisitQueue.filter(pair => pair._1 == classElement).foreach(pair => processClassTree(classTree, pair._2))
	}

	def visitOrQueueClassTree(classTree: ClassTree, annotation: AnnotationMirror): Unit = {
		val classElement = TreeUtils.elementFromDeclaration(classTree)
		if (classVisitCache.exists(pair => pair._1 == classElement)) {
			processClassTree(classTree, annotation)
		} else {
			classVisitQueue.update((classElement, annotation), included = true)
			treeMap.update(classElement, classTree)
		}
	}



	/**
	 * Visits a class tree under a specific consistency qualifier
	 */
	private def processClassTree(classTree: ClassTree, annotation: AnnotationMirror, libMode: Boolean = false): Unit = {
		// TODO
		//----------------------------------------------------------------
		// set class context in type factory to upper bound of class tree, then visit class
		// include class context in error output, so that we know which version of the class produces errors
		// in lib mode, also do this for all lower consistencies (w/o cache)
		// if mixed, then run inference before visiting
		// cache visited classes somewhere (name + consistency should be enough)
		// in type factory: - if use of class found somewhere, check cache and visit early if not cached
		// 					- for strong and weak classes: possibly no further action needed, treeannotator already takes care of adaptation
		//                  - for mixed classes: do what we do already

		val classElement = TreeUtils.elementFromDeclaration(classTree)
		if (classVisitCache.exists(entry => classElement.equals(entry._1) && AnnotationUtils.areSame(annotation, entry._2)))
			return
		else classVisitCache.update((classElement, annotation), included = true)

		if (tf.areSameByClass(annotation, classOf[Mixed])) {
			println(s">Class decl: @${annotation.getAnnotationType.asElement().getSimpleName}(${Class.forName(getMixedDefaultOp(annotation)).getSimpleName}) ${getQualifiedName(classTree)}")
		} else {
			println(s">Class decl: @${annotation.getAnnotationType.asElement().getSimpleName} ${getQualifiedName(classTree)}")
		}

		tf.pushVisitClassContext(classElement, annotation)
		if (tf.areSameByClass(annotation, classOf[Mixed])) {
			tf.inferenceVisitor.processClass(classTree, annotation)
			//tf.returnTypeVisitor.processClass(classTree, annotation)
		}
		// TODO: how should we handle the cache?
		super.processClassTree(classTree)
		tf.popVisitClassContext()

		if (checker.getLintOption("libMode")) {
			// TODO
		}
	}

	/*
		Check that implicit contexts are correct.
	 */
	override def visitAssignment(node : AssignmentTree, p : Void) : Void = {
		//println(s"  >Var assign:\n" +
		//		s"   <$node>\n" +
		//		s"      where ${node.getVariable} -> ${atypeFactory.getAnnotatedType(node.getVariable)}\n" +
		//		s"      where ${node.getExpression} -> ${atypeFactory.getAnnotatedType(node.getExpression)}")

		checkAssignment(atypeFactory.getAnnotatedType(node.getVariable), atypeFactory.getAnnotatedType(node.getExpression), node)
		super.visitAssignment(node, p)
	}

	//compound assignment is, e.g., i += 23
	override def visitCompoundAssignment(node : CompoundAssignmentTree, p : Void) : Void = {
		checkAssignment(atypeFactory.getAnnotatedType(node.getVariable), atypeFactory.getAnnotatedType(node.getExpression), node)
		super.visitCompoundAssignment(node, p)
	}


	override def visitVariable(node : VariableTree, p : Void) : Void = {
		/*
		if (node.getInitializer != null)
			println(s"  >Var decl:\n" +
				s"   ${atypeFactory.getAnnotatedType(node)} ${node.getName}\n" +
				s"   <$node>\n" +
				s"      where ${node.getName} -> ${atypeFactory.getAnnotatedType(node)}\n" +
				s"      where ${node.getInitializer} -> ${atypeFactory.getAnnotatedType(node.getInitializer)}")
		else
			println(s"  >Var decl:\n" +
				s"   ${atypeFactory.getAnnotatedType(node)} ${node.getName}")
		 */

		val initializer: ExpressionTree = node.getInitializer
		if (initializer != null) checkAssignment(atypeFactory.getAnnotatedType(node), atypeFactory.getAnnotatedType(initializer), node)
		super.visitVariable(node, p)
	}

	private def checkAssignment(lhsType : AnnotatedTypeMirror, rhsType : AnnotatedTypeMirror, tree : Tree) : Unit = {
		if (transactionContext && (!implicitContext.allowsUpdatesTo(lhsType, tree))) //|| !implicitContext.allowsUpdatesFrom(rhsType, tree)))
			checker.reportError(tree, "assignment.type.implicitflow", lhsType, implicitContext.get, tree)

		tree match {
			case _: VariableTree => // variable initialization at declaration is allowed
			case assign: AssignmentTree => assign.getVariable match {
				case id: IdentifierTree if TreeUtils.elementFromUse(id).getKind != ElementKind.FIELD => // reassigning variables is allowed
				case _ => if (lhsType.hasEffectiveAnnotation(classOf[qual.Immutable]) && !TypesUtils.isPrimitiveOrBoxed(lhsType.getUnderlyingType))
					checker.reportError(tree, "immutability.assignment.type")
			}
			case _ =>
		}
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

				// check implicit context on non-mixed method invocation
				if (expr != null && !methodInvocationIsRefOrGetField(node) && !recvType.hasEffectiveAnnotation(classOf[Mixed]))
					checkMethodInvocationReceiver(recvType, node)

				// check implicit context on mixed method invocation
				if (recvType.hasEffectiveAnnotation(classOf[Mixed]))
					checkMethodInvocationOpLevel(recvType, node)

				// check immutability
				checkMethodInvocationReceiverMutability(recvType, methodType, node)

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

	def methodInvocationIsRefAccess(node: MethodInvocationTree): Boolean =
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

	private def checkMethodInvocationReceiver(receiverType : AnnotatedTypeMirror, tree : Tree) : Unit = {
		if (transactionContext && !implicitContext.allowsAsReceiver(receiverType, tree))
			checker.reportError(tree, "invocation.receiver.implicitflow", receiverType, implicitContext.get, tree)
	}

	private def checkMethodInvocationReceiverMutability(receiverType : AnnotatedTypeMirror, methodType: AnnotatedExecutableType, tree : MethodInvocationTree) : Unit = {
		if (!(methodInvocationIsRefAccess(tree) || methodInvocationIsReplicate(tree)) &&
			receiverType.hasEffectiveAnnotation(classOf[qual.Immutable]) &&
			!(ElementUtils.hasAnnotation(methodType.getElement, classOf[SideEffectFree].getName) ||
				ElementUtils.hasAnnotation(methodType.getElement, classOf[Pure].getName)))
			checker.reportError(tree, "immutability.invocation.receiver")
	}

	private def checkMethodInvocationArgument(argType : AnnotatedTypeMirror, tree : Tree) : Unit = {
		if (transactionContext && !implicitContext.allowsAsArgument(argType, tree))
			checker.reportError(tree, "invocation.argument.implicitflow", argType, implicitContext.get, tree)
	}

	private def checkMethodInvocationOpLevel(recvType: AnnotatedTypeMirror, tree: MethodInvocationTree): Unit = {
		if (transactionContext && recvType.hasEffectiveAnnotation(classOf[Mixed]) && !implicitContext.allowsAsMixedInvocation(recvType, tree))
			checker.reportError(tree, "invocation.operation.implicitflow",
				getMixedOpForMethod(TreeUtils.elementFromUse(tree), getMixedDefaultOp(recvType.getAnnotation(classOf[Mixed]))),
				implicitContext.get, tree)
	}



	override protected def getAnnotation(typ : AnnotatedTypeMirror) : AnnotationMirror = {
		return typ.getEffectiveAnnotationInHierarchy(getTopAnnotation)

		//can only include consistency annotations
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
