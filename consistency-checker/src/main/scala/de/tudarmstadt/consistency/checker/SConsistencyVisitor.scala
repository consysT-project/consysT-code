package de.tudarmstadt.consistency.checker

import java.util
import java.util.{Set, Stack}

import com.sun.source.tree._
import javax.lang.model.element.AnnotationMirror
import org.checkerframework.common.basetype.{BaseTypeChecker, BaseTypeVisitor}
import org.checkerframework.framework.`type`.AnnotatedTypeMirror
import org.checkerframework.framework.source.Result
import org.checkerframework.javacutil.AnnotationUtils

/**
	* Created on 05.03.19.
	*
	* @author Mirko Köhler
	*/
class SConsistencyVisitor(checker : BaseTypeChecker) extends BaseTypeVisitor[ConsistencyAnnotatedTypeFactory](checker){


	private def localAnnotation : AnnotationMirror = AnnotationUtils.getAnnotationByName(atypeFactory.getQualifierHierarchy.getBottomAnnotations, "de.tudarmstadt.consistency.checker.qual.Local")

	private def inconsistentAnnotation : AnnotationMirror = {
		new SomeClass
		AnnotationUtils.getAnnotationByName(atypeFactory.getQualifierHierarchy.getTopAnnotations, "de.tudarmstadt.consistency.checker.qual.Inconsistent")
	}


	private class ImplicitContext private[checker]() {

		final private var implicitContexts : util.Stack[AnnotationMirror] = null

		implicitContexts = new util.Stack[AnnotationMirror]
		implicitContexts.push(localAnnotation)

		private[checker] def set(annotation : AnnotationMirror) : Unit = {
			val implicitContext : AnnotationMirror = atypeFactory.getQualifierHierarchy.leastUpperBound(annotation, get)
			implicitContexts.push(implicitContext)
		}
		private[checker] def get : AnnotationMirror = implicitContexts.peek
		private[checker] def reset() : Unit = {
			implicitContexts.pop
		}
		private def lowerBound(a : AnnotationMirror, b : AnnotationMirror) : AnnotationMirror = atypeFactory.getQualifierHierarchy.greatestLowerBound(a, b)
		private def getStrongestNonLocalAnnotationIn(`type` : AnnotatedTypeMirror, annotation : AnnotationMirror) : AnnotationMirror = {
			if (`type`.isInstanceOf[AnnotatedTypeMirror.AnnotatedDeclaredType]) {
				val declaredType : AnnotatedTypeMirror.AnnotatedDeclaredType = `type`.asInstanceOf[AnnotatedTypeMirror.AnnotatedDeclaredType]
				var temp : AnnotationMirror = lowerBound(getAnnotation(`type`), annotation)
				import scala.collection.JavaConversions._
				for (typeArg <- declaredType.getTypeArguments) {
					temp = lowerBound(temp, getStrongestNonLocalAnnotationIn(typeArg, temp))
				}
				return temp
			}
			else if (`type`.isInstanceOf[AnnotatedTypeMirror.AnnotatedWildcardType]) {
				val wildcardType : AnnotatedTypeMirror.AnnotatedWildcardType = `type`.asInstanceOf[AnnotatedTypeMirror.AnnotatedWildcardType]
				var temp : AnnotationMirror = lowerBound(getAnnotation(`type`), annotation)
				temp = lowerBound(temp, getStrongestNonLocalAnnotationIn(wildcardType.getSuperBound, temp))
				temp = lowerBound(temp, getStrongestNonLocalAnnotationIn(wildcardType.getExtendsBound, temp))
				return temp
			}
			//May be null
			getAnnotation(`type`)
		}
		private def canBeAccessed(`type` : AnnotatedTypeMirror, tree : Tree) : Boolean = {
			val typeAnnotation : AnnotationMirror = getStrongestNonLocalAnnotationIn(`type`, inconsistentAnnotation)
			if (typeAnnotation == null) {
				checker.report(Result.warning("consistency.inferred", `type`, tree), tree)
				//Log.info(getClass(), String.format("consistency.inferred: consistency level of {%s} unknown and has been inferred to @Inconsistent.\nin: %s", type, tree));
				return true
			}
			atypeFactory.getQualifierHierarchy.isSubtype(get, typeAnnotation) || atypeFactory.getQualifierHierarchy.getBottomAnnotations.contains(typeAnnotation)
		}
		private[checker] def allowsUpdatesTo(`type` : AnnotatedTypeMirror, tree : Tree) : Boolean = canBeAccessed(`type`, tree)
		private[checker] def allowsUpdatesFrom(`type` : AnnotatedTypeMirror, tree : Tree) : Boolean = canBeAccessed(`type`, tree)
		private[checker] def allowsAsReceiver(`type` : AnnotatedTypeMirror, tree : Tree) : Boolean = canBeAccessed(`type`, tree)
		private[checker] def allowsAsArgument(`type` : AnnotatedTypeMirror, tree : Tree) : Boolean = canBeAccessed(`type`, tree)
	}


	private val implicitContext : ImplicitContext = new ImplicitContext

	/*
		Increase implicit context.
	 */ override def visitIf(node : IfTree, p : Void) : Void = {
		val conditionAnnotation : AnnotationMirror = weakestConsistencyInExpression(node.getCondition)
		implicitContext.set(conditionAnnotation)
		//The condition is executed under the implicit context as well .
		var r : Void = scan(node.getCondition, p)
		r = reduce(scan(node.getThenStatement, p), r)
		r = reduce(scan(node.getElseStatement, p), r)
		implicitContext.reset()
		r
	}

	override def visitWhileLoop(node : WhileLoopTree, p : Void) : Void = {
		val conditionAnnotation : AnnotationMirror = weakestConsistencyInExpression(node.getCondition)
		implicitContext.set(conditionAnnotation)
		var r : Void = scan(node.getCondition, p)
		r = reduce(scan(node.getStatement, p), r)
		implicitContext.reset()
		r
	}

	override def visitDoWhileLoop(node : DoWhileLoopTree, p : Void) : Void = {
		val conditionAnnotation : AnnotationMirror = weakestConsistencyInExpression(node.getCondition)
		implicitContext.set(conditionAnnotation)
		var r : Void = scan(node.getCondition, p)
		r = reduce(scan(node.getStatement, p), r)
		implicitContext.reset()
		r
	}

	override def visitForLoop(node : ForLoopTree, p : Void) : Void = {
		val conditionAnnotation : AnnotationMirror = weakestConsistencyInExpression(node.getCondition)
		var r : Void = scan(node.getInitializer, p)
		r = reduce(scan(node.getCondition, p), r)
		implicitContext.set(conditionAnnotation)
		r = reduce(scan(node.getUpdate, p), r)
		r = reduce(scan(node.getStatement, p), r)
		implicitContext.reset()
		r
	}

	override def visitEnhancedForLoop(node : EnhancedForLoopTree, p : Void) : Void = { //TODO: add variable to implicit context?
		val conditionAnnotation : AnnotationMirror = weakestConsistencyInExpression(node.getExpression)
		var r : Void = scan(node.getVariable, p)
		r = reduce(scan(node.getExpression, p), r)
		implicitContext.set(conditionAnnotation)
		r = reduce(scan(node.getStatement, p), r)
		implicitContext.reset()
		r
	}

	override def visitSwitch(node : SwitchTree, p : Void) : Void = {
		val conditionAnnotation : AnnotationMirror = weakestConsistencyInExpression(node.getExpression)
		var r : Void = scan(node.getExpression, p)
		implicitContext.set(conditionAnnotation)
		r = reduce(scan(node.getCases, p), r)
		implicitContext.reset()
		r
	}


	/*
		Check that implicit contexts are correct.
	 */ override def visitAssignment(node : AssignmentTree, p : Void) : Void = {
		checkAssignment(atypeFactory.getAnnotatedType(node.getVariable), atypeFactory.getAnnotatedType(node.getExpression), node)
		super.visitAssignment(node, p)
	}


	override //compound assignment is, e.g., i += 23
	def visitCompoundAssignment(node : CompoundAssignmentTree, p : Void) : Void = {
		checkAssignment(atypeFactory.getAnnotatedType(node.getVariable), atypeFactory.getAnnotatedType(node.getExpression), node)
		super.visitCompoundAssignment(node, p)
	}


	override def visitVariable(node : VariableTree, p : Void) : Void = {
		val initializer : ExpressionTree = node.getInitializer
		if (initializer != null) checkAssignment(atypeFactory.getAnnotatedType(node), atypeFactory.getAnnotatedType(initializer), node)
		super.visitVariable(node, p)
	}

	private def checkAssignment(lhsType : AnnotatedTypeMirror, rhsType : AnnotatedTypeMirror, tree : Tree) : Unit = {
		if (!implicitContext.allowsUpdatesTo(lhsType, tree) || !implicitContext.allowsUpdatesFrom(rhsType, tree)) checker.report(Result.failure("assignment.type.implicitflow", lhsType, implicitContext.get, tree), tree)
	}

	override def visitMethodInvocation(node : MethodInvocationTree, p : Void) : Void = {
		val methodSelect : ExpressionTree = node.getMethodSelect
		if (methodSelect.isInstanceOf[MemberSelectTree]) {
			val memberSelectTree : MemberSelectTree = methodSelect.asInstanceOf[MemberSelectTree]
			val expr : ExpressionTree = memberSelectTree.getExpression
			if (expr != null) checkMethodInvocationReceiver(atypeFactory.getAnnotatedType(expr), node)
		}
		//implicit context is not used when checking a method implementation.
		//Thus, disallow methods that use weak contexts.
		//TODO: Methods can still have assignments to strong variables. How do we rule out those cases?
		import scala.collection.JavaConversions._
		for (argExpr <- node.getArguments) {
			checkMethodInvocationArgument(atypeFactory.getAnnotatedType(argExpr), node)
		}
		super.visitMethodInvocation(node, p)
	}

	private def checkMethodInvocationReceiver(receiverType : AnnotatedTypeMirror, tree : Tree) : Unit = {
		if (!implicitContext.allowsAsReceiver(receiverType, tree)) checker.report(Result.failure("invocation.receiver.implicitflow", receiverType, implicitContext.get, tree), tree)
	}

	private def checkMethodInvocationArgument(argType : AnnotatedTypeMirror, tree : Tree) : Unit = {
		if (!implicitContext.allowsAsArgument(argType, tree)) checker.report(Result.failure("invocation.argument.implicitflow", argType, implicitContext.get, tree), tree)
	}


	private def weakestConsistencyInExpression(node : ExpressionTree) : AnnotationMirror = {
		/*
				 TODO: This requires an annotated JDK in order to work correctly.

				 With an unannotated JDK we have the following behavior:

				 Definitions:
					 @Strong String s1
					 @Weak String s2
					 public static @PolyConsistent boolean equals(@PolyConsistent Object o1, @PolyConsistent Object o2)

				 s1.equals("hello") --> inconsistent (the normal equals method is always @inconsistent because it is not annotated)
				 equals(s1, "hello") --> strong
				 equals(s1, s2) --> weak
					*/
		//Retrieve the (inferred) annotated type
		getAnnotation(atypeFactory.getAnnotatedType(node))
	}

	private def getAnnotation(`type` : AnnotatedTypeMirror) : AnnotationMirror = { //can only include consistency annotations
		val annotations : util.Set[AnnotationMirror] = `type`.getAnnotations
		if (annotations.size == 1) return annotations.iterator.next
		else if (annotations.isEmpty) return null
		throw new AssertionError("inferred an unexpected number of annotations. Expected 1 annotation, but got: " + annotations)
	}

}
