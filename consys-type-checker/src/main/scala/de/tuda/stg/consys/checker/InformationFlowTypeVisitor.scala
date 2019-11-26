package de.tuda.stg.consys.checker

import com.sun.source.tree.{DoWhileLoopTree, EnhancedForLoopTree, ExpressionTree, ForLoopTree, IfTree, SwitchTree, Tree, WhileLoopTree}
import javax.lang.model.element.AnnotationMirror
import org.checkerframework.common.basetype.{BaseTypeChecker, BaseTypeVisitor}
import org.checkerframework.framework.`type`.{AnnotatedTypeMirror, GenericAnnotatedTypeFactory}
import org.checkerframework.framework.source.Result

import scala.collection.{JavaConverters, mutable}

/**
	* Created on 03.07.19.
	*
	* @author Mirko Köhler
	*/
abstract class InformationFlowTypeVisitor[TypeFactory <: GenericAnnotatedTypeFactory[_, _, _, _]](checker : BaseTypeChecker) extends BaseTypeVisitor[TypeFactory](checker) {
	import TypeFactoryUtils._


	//Current context of the consistency check
	protected val implicitContext : ImplicitContext = new ImplicitContext


	//Returns the annotation which information flow should be checked
	protected def getAnnotation(typ : AnnotatedTypeMirror) : AnnotationMirror

	protected def getEmptyContextAnnotation : AnnotationMirror

	protected def getTopAnnotation : AnnotationMirror


	/*
		Increase implicit context.
	 */
	override def visitIf(node : IfTree, p : Void) : Void = {
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



	class ImplicitContext {

		private val implicitContexts : mutable.ArrayStack[AnnotationMirror] = new mutable.ArrayStack

		implicitContexts.push(getEmptyContextAnnotation)

		private[checker] def set(annotation : AnnotationMirror) : Unit = {
			val implicitContext : AnnotationMirror = atypeFactory.getQualifierHierarchy.leastUpperBound(annotation, get)
			implicitContexts.push(implicitContext)
		}

		private[checker] def reset() : Unit = {
			implicitContexts.pop
		}


		def get : AnnotationMirror = implicitContexts.head


		private def getStrongestNonLocalAnnotationIn(typ : AnnotatedTypeMirror, annotation : AnnotationMirror) : AnnotationMirror = {
			//Easier access to lower bound
			def lowerBound(a : AnnotationMirror, b : AnnotationMirror) : AnnotationMirror = {
				//TODO: Fix this! There are NullPointerExceptions...
				//println(s"lower bound $a and $b. type factory? ${atypeFactory != null} hierarchy? ${if (atypeFactory != null) atypeFactory.getQualifierHierarchy != null else false}")
				//atypeFactory.getQualifierHierarchy.greatestLowerBound(a, b)
				a
			}


			typ match {
				case declaredType : AnnotatedTypeMirror.AnnotatedDeclaredType =>
					var temp : AnnotationMirror = lowerBound(getAnnotation(typ), annotation)

					JavaConverters.iterableAsScalaIterable(declaredType.getTypeArguments).foreach { typeArg =>
						temp = lowerBound(temp, getStrongestNonLocalAnnotationIn(typeArg, temp))
					}

					temp

				case wildcardType : AnnotatedTypeMirror.AnnotatedWildcardType =>
					var temp : AnnotationMirror = lowerBound(getAnnotation(typ), annotation)
					temp = lowerBound(temp, getStrongestNonLocalAnnotationIn(wildcardType.getSuperBound, temp))
					temp = lowerBound(temp, getStrongestNonLocalAnnotationIn(wildcardType.getExtendsBound, temp))
					temp

				case _ =>
					getAnnotation(typ)
			}
		}


		private def canBeAccessed(typ : AnnotatedTypeMirror, tree : Tree) : Boolean = {
			val typeAnnotation : AnnotationMirror = getStrongestNonLocalAnnotationIn(typ, getTopAnnotation)

			if (typeAnnotation == null) {
				checker.report(Result.warning("consistency.inferred", typ, tree), tree)
				//Log.info(getClass(), String.format("consistency.inferred: consistency level of {%s} unknown and has been inferred to @Inconsistent.\nin: %s", type, tree));
				return true
			}

			atypeFactory.getQualifierHierarchy.isSubtype(get, typeAnnotation)||
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
	}


}
