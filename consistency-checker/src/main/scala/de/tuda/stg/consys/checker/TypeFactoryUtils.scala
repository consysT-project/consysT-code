package de.tuda.stg.consys.checker

import com.sun.source.tree.{ExpressionTree, MemberSelectTree, MethodInvocationTree}
import javax.lang.model.element.AnnotationMirror
import org.checkerframework.framework.`type`.AnnotatedTypeFactory
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.AnnotatedDeclaredType
import org.checkerframework.javacutil.AnnotationUtils

/**
	* Created on 06.03.19.
	*
	* @author Mirko Köhler
	*/
object TypeFactoryUtils {
	/*
		Annotation definitions
	 */
	@inline def localAnnotation(implicit atypeFactory : AnnotatedTypeFactory) : AnnotationMirror =
		AnnotationUtils.getAnnotationByName(atypeFactory.getQualifierHierarchy.getBottomAnnotations, "de.tuda.stg.consys.checker.qual.Local")

	@inline def inconsistentAnnotation(implicit atypeFactory : AnnotatedTypeFactory) : AnnotationMirror =
		AnnotationUtils.getAnnotationByName(atypeFactory.getQualifierHierarchy.getTopAnnotations, "de.tuda.stg.consys.checker.qual.Inconsistent")



	def methodInvocationIsReplicate(node : MethodInvocationTree)(implicit atypeFactory : AnnotatedTypeFactory) : Boolean = node.getMethodSelect match {
		case memberSelectTree : MemberSelectTree =>

			val receiver : ExpressionTree = memberSelectTree.getExpression

			atypeFactory.getAnnotatedType(receiver) match {
				case adt : AnnotatedDeclaredType
					//Method is member of JReplicaSystem
					if adt.getUnderlyingType.asElement().getSimpleName.toString == "JReplicaSystem" =>

					//Method name is replicate
					if (memberSelectTree.getIdentifier.toString == "replicate") {

						//Method has 2 or 3 arguments
						val setArg : ExpressionTree =
							node.getArguments.size() match {
								case 3 => node.getArguments.get(1)
								case 2 => node.getArguments.get(0)
								case _ => sys.error("unknown replicate implementation")
							}

						val setArgT = atypeFactory.getAnnotatedType(setArg)

						val targs = node.getTypeArguments
						//TODO: Check type arguments here?

						println(s"args = ${node.getArguments}, targs = $targs")
					}
				case _ =>
			}

			false

		case _ =>
			false
	}

}
