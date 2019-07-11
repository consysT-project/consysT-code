package de.tuda.stg.consys.checker

import java.util

import com.sun.source.tree._
import javax.lang.model.element.AnnotationMirror
import org.checkerframework.common.basetype.{BaseTypeChecker, BaseTypeVisitor}
import org.checkerframework.framework.`type`.AnnotatedTypeMirror
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.AnnotatedDeclaredType
import org.checkerframework.framework.source.Result

import scala.collection.{JavaConverters, mutable}

/**
	* Created on 05.03.19.
	*
	* @author Mirko Köhler
	*/
class ConsistencyVisitorImpl(checker : BaseTypeChecker) extends InformationFlowTypeVisitor[ConsistencyAnnotatedTypeFactory](checker){
	import TypeFactoryUtils._



	override def visitMemberSelect(node : MemberSelectTree, p : Void) : Void = {
		node.getIdentifier

		super.visitMemberSelect(node, p)

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
		val initializer : ExpressionTree = node.getInitializer
		if (initializer != null) checkAssignment(atypeFactory.getAnnotatedType(node), atypeFactory.getAnnotatedType(initializer), node)
		super.visitVariable(node, p)
	}

	private def checkAssignment(lhsType : AnnotatedTypeMirror, rhsType : AnnotatedTypeMirror, tree : Tree) : Unit = {
		if (!implicitContext.allowsUpdatesTo(lhsType, tree) || !implicitContext.allowsUpdatesFrom(rhsType, tree))
			checker.report(Result.failure("assignment.type.implicitflow", lhsType, implicitContext.get, tree), tree)
	}

	override def visitMethodInvocation(node : MethodInvocationTree, p : Void) : Void = {


		if (methodInvocationIsReplicate(node)) {
			println("FOUND SET FIELD")
		}

		node.getMethodSelect match {
			case memberSelectTree : MemberSelectTree =>

				val expr : ExpressionTree = memberSelectTree.getExpression
				val recvType = atypeFactory.getAnnotatedType(expr)



				if (expr != null)
					checkMethodInvocationReceiver(atypeFactory.getAnnotatedType(expr), node)

			case _ =>
		}

		node.getArguments.forEach(argExpr =>
			checkMethodInvocationArgument(atypeFactory.getAnnotatedType(argExpr), node)
		)

		super.visitMethodInvocation(node, p)
	}

	private def methodInvocationIsReplicate(node : MethodInvocationTree) : Boolean = node.getMethodSelect match {
		case memberSelectTree : MemberSelectTree =>
			val expr : ExpressionTree = memberSelectTree.getExpression
			val recvType = atypeFactory.getAnnotatedType(expr)

//			println(s"expr = $expr, recvType = $recvType, method = ${memberSelectTree.getIdentifier}")

			recvType match {
				case adt : AnnotatedDeclaredType if adt.getUnderlyingType.asElement().getSimpleName.toString == "JReplicaSystem" =>
					if (memberSelectTree.getIdentifier.toString == "replicate") {

						val setArg = node.getArguments.get(1)
						val setArgT = atypeFactory.getAnnotatedType(setArg)

						if (!setArgT.getAnnotations.contains(localAnnotation(atypeFactory))) {
							println("WARNING: Non-local value replicated")
						}

						val targs = node.getTypeArguments



						println(s"args = ${node.getArguments}, targs = $targs")
					}
				case _ =>
			}

			false

		case _ =>
			false
	}

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

	private def checkMethodInvocationReceiver(receiverType : AnnotatedTypeMirror, tree : Tree) : Unit = {
		if (!implicitContext.allowsAsReceiver(receiverType, tree))
			checker.report(Result.failure("invocation.receiver.implicitflow", receiverType, implicitContext.get, tree), tree)
	}

	private def checkMethodInvocationArgument(argType : AnnotatedTypeMirror, tree : Tree) : Unit = {
		if (!implicitContext.allowsAsArgument(argType, tree))
			checker.report(Result.failure("invocation.argument.implicitflow", argType, implicitContext.get, tree), tree)
	}





	override protected def getAnnotation(typ : AnnotatedTypeMirror) : AnnotationMirror = { //can only include consistency annotations
		val annotations : util.Set[AnnotationMirror] = typ.getAnnotations
		if (annotations.size == 1) return annotations.iterator.next
		else if (annotations.isEmpty) return null
		throw new AssertionError("inferred an unexpected number of annotations. Expected 1 annotation, but got: " + annotations)
	}

	override protected def getEmptyContextAnnotation : AnnotationMirror = localAnnotation(atypeFactory)

	override protected def getTopAnnotation : AnnotationMirror = inconsistentAnnotation(atypeFactory)
}
