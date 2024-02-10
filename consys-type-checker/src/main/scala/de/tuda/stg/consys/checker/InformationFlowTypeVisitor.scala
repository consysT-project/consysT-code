package de.tuda.stg.consys.checker

import com.sun.source.tree._
import de.tuda.stg.consys.checker.qual.{Mixed, Weak}
import org.checkerframework.common.basetype.{BaseTypeChecker, BaseTypeVisitor}
import org.checkerframework.framework.`type`.{AnnotatedTypeMirror, GenericAnnotatedTypeFactory}
import org.checkerframework.javacutil.{AnnotationBuilder, TreeUtils}

import javax.lang.model.element.AnnotationMirror
import scala.collection.mutable
import scala.jdk.CollectionConverters._

/**
	* Created on 03.07.19.
	*
	* @author Mirko Köhler
	*/
abstract class InformationFlowTypeVisitor[TypeFactory <: GenericAnnotatedTypeFactory[_, _, _, _]](baseChecker : BaseTypeChecker) extends BaseTypeVisitor[TypeFactory](baseChecker) {
	import TypeFactoryUtils._
	protected implicit val tf: TypeFactory = atypeFactory

	//Current context of the consistency check
	protected val implicitContext : ImplicitContext = new ImplicitContext

	protected var transactionContext: Boolean = false
	def getTransactionContext: Boolean = transactionContext


	//Returns the annotation which information flow should be checked
	protected def getAnnotation(typ : AnnotatedTypeMirror) : AnnotationMirror

	protected def getEmptyContextAnnotation : AnnotationMirror

	protected def getTopAnnotation : AnnotationMirror


	/*
		Increase implicit context.
	 */
	override def visitIf(node : IfTree, p : Void) : Void = {
		if (!transactionContext) return super.visitIf(node, p)
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
		if (!transactionContext) return super.visitWhileLoop(node, p)
		val conditionAnnotation : AnnotationMirror = weakestConsistencyInExpression(node.getCondition)
		implicitContext.set(conditionAnnotation)
		var r : Void = scan(node.getCondition, p)
		r = reduce(scan(node.getStatement, p), r)
		implicitContext.reset()
		r
	}

	override def visitDoWhileLoop(node : DoWhileLoopTree, p : Void) : Void = {
		if (!transactionContext) return super.visitDoWhileLoop(node, p)
		val conditionAnnotation : AnnotationMirror = weakestConsistencyInExpression(node.getCondition)
		implicitContext.set(conditionAnnotation)
		var r : Void = scan(node.getCondition, p)
		r = reduce(scan(node.getStatement, p), r)
		implicitContext.reset()
		r
	}

	override def visitForLoop(node : ForLoopTree, p : Void) : Void = {
		if (!transactionContext) return super.visitForLoop(node, p)
		val conditionAnnotation : AnnotationMirror = weakestConsistencyInExpression(node.getCondition)
		var r : Void = scan(node.getInitializer, p)
		r = reduce(scan(node.getCondition, p), r)
		implicitContext.set(conditionAnnotation)
		r = reduce(scan(node.getUpdate, p), r)
		r = reduce(scan(node.getStatement, p), r)
		implicitContext.reset()
		r
	}

	override def visitEnhancedForLoop(node : EnhancedForLoopTree, p : Void) : Void = {
		if (!transactionContext) return super.visitEnhancedForLoop(node, p)
		val conditionAnnotation : AnnotationMirror = weakestConsistencyInExpression(node.getExpression)
		var r : Void = scan(node.getVariable, p)
		r = reduce(scan(node.getExpression, p), r)
		implicitContext.set(conditionAnnotation)
		r = reduce(scan(node.getStatement, p), r)
		implicitContext.reset()
		r
	}

	override def visitSwitch(node : SwitchTree, p : Void) : Void = {
		if (!transactionContext) return super.visitSwitch(node, p)
		val conditionAnnotation : AnnotationMirror = weakestConsistencyInExpression(node.getExpression)
		var r : Void = scan(node.getExpression, p)
		implicitContext.set(conditionAnnotation)
		r = reduce(scan(node.getCases, p), r)
		implicitContext.reset()
		r
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

		// Retrieve the (inferred) annotated type
		val typ = atypeFactory.getAnnotatedType(node)
		if (typ.hasEffectiveAnnotation(classOf[Mixed]))
			AnnotationBuilder.fromClass(atypeFactory.getElementUtils, classOf[Weak])
		else getAnnotation(typ)
	}



	class ImplicitContext {

		private val implicitContexts : mutable.Stack[AnnotationMirror] = new mutable.Stack

		implicitContexts.push(getEmptyContextAnnotation)

		private[checker] def set(annotation : AnnotationMirror) : Unit = {
			val implicitContext : AnnotationMirror = atypeFactory.getQualifierHierarchy.leastUpperBound(annotation, get)
			implicitContexts.push(implicitContext)
		}

		private[checker] def reset() : Unit = {
			implicitContexts.pop()
		}


		def get : AnnotationMirror = implicitContexts.head


		private def getStrongestNonLocalAnnotationIn(typ : AnnotatedTypeMirror, annotation : AnnotationMirror) : AnnotationMirror = {
			//Easier access to lower bound
			def lowerBound(a : AnnotationMirror, b : AnnotationMirror) : AnnotationMirror = {
				atypeFactory.getQualifierHierarchy.greatestLowerBound(a, b)
			}

			typ match {
				case declaredType : AnnotatedTypeMirror.AnnotatedDeclaredType =>
					var temp : AnnotationMirror = lowerBound(getAnnotation(typ), annotation)

					declaredType.getTypeArguments.asScala.foreach { typeArg =>
						temp = lowerBound(temp, getStrongestNonLocalAnnotationIn(typeArg, temp))
					}

					temp

				case wildcardType : AnnotatedTypeMirror.AnnotatedWildcardType =>
					var temp : AnnotationMirror = lowerBound(getAnnotation(typ), annotation)
					temp = lowerBound(temp, getStrongestNonLocalAnnotationIn(wildcardType.getSuperBound, temp))
					temp = lowerBound(temp, getStrongestNonLocalAnnotationIn(wildcardType.getExtendsBound, temp))
					temp

				case _ =>
					val annotation = getAnnotation(typ)
					if (annotation != null) annotation else getTopAnnotation
			}
		}


		private def canBeAccessed(typ : AnnotatedTypeMirror, tree : Tree) : Boolean = {
			val typeAnnotation : AnnotationMirror = getStrongestNonLocalAnnotationIn(typ, getTopAnnotation)

			if (typeAnnotation == null) {
				checker.reportWarning(tree, "consistency.inferred", typ, tree)
				//Log.info(getClass(), String.format("consistency.inferred: consistency level of {%s} unknown and has been inferred to @Inconsistent.\nin: %s", type, tree));
				return true
			}

			atypeFactory.getQualifierHierarchy.isSubtype(get, typeAnnotation) ||
				atypeFactory.getQualifierHierarchy.getBottomAnnotations.contains(typeAnnotation)
		}

		def allowsUpdatesTo(typ : AnnotatedTypeMirror, tree : Tree) : Boolean =
			canBeAccessed(typ, tree)

		def allowsUpdatesFrom(typ : AnnotatedTypeMirror, tree : Tree) : Boolean =
			canBeAccessed(typ, tree)

		def allowsAsReceiver(typ : AnnotatedTypeMirror, tree : Tree) : Boolean =
			canBeAccessed(typ, tree)

		def allowsAsArgument(typ : AnnotatedTypeMirror, tree : Tree) : Boolean =
			canBeAccessed(typ, tree)

		def allowsAsMixedInvocation(typ : AnnotatedTypeMirror, tree : MethodInvocationTree): Boolean = {
			val method = TreeUtils.elementFromUse(tree)
			if (isDeclaredSideEffectFree(method))
				return true

			val methodLevel = getQualifierForMethodOp(method, typ.getEffectiveAnnotation(classOf[Mixed]))

			atypeFactory.getQualifierHierarchy.isSubtype(get, methodLevel.get) ||
				atypeFactory.getQualifierHierarchy.getBottomAnnotations.contains(methodLevel.get)
		}
	}
}
