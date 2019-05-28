package de.tuda.stg.consys.checker

import com.sun.source.tree.{ExpressionTree, LiteralTree, MemberSelectTree, MethodInvocationTree, NewClassTree, Tree}
import org.checkerframework.checker.signature.qual.Identifier
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.AnnotatedDeclaredType
import org.checkerframework.framework.`type`.treeannotator.TreeAnnotator
import org.checkerframework.framework.`type`.{AnnotatedTypeFactory, AnnotatedTypeMirror}

/**
	* Created on 06.03.19.
	*
	* @author Mirko Köhler
	*/
class ExtendedImplicitTreeAnnotator(tf : AnnotatedTypeFactory) extends TreeAnnotator(tf) {
	import TypeFactoryUtils._

	implicit val implicitTypeFactory : AnnotatedTypeFactory = atypeFactory

	@inline private def qualHierarchy = atypeFactory.getQualifierHierarchy



	override def visitNewClass(node : NewClassTree, annotatedTypeMirror : AnnotatedTypeMirror) : Void = {
		//Locally generated objects (new Obj...) are always @Local.
		annotatedTypeMirror.clearAnnotations()
		annotatedTypeMirror.addAnnotation(localAnnotation)

		super.visitNewClass(node, annotatedTypeMirror)
	}

	override def visitLiteral(node : LiteralTree, annotatedTypeMirror : AnnotatedTypeMirror) : Void = {
		//Literals are always @Local.
		annotatedTypeMirror.clearAnnotations()
		annotatedTypeMirror.addAnnotation(localAnnotation)
		super.visitLiteral(node, annotatedTypeMirror)
	}

	override def visitMemberSelect(node : MemberSelectTree, annotatedTypeMirror : AnnotatedTypeMirror) : Void = {

		//Class literals are always @Local.
		if (node.getIdentifier.contentEquals("class")) {
			//Change type to: @Local Class...
			annotatedTypeMirror.clearAnnotations()

			val locAnn = localAnnotation
			println(s"local annotation = $locAnn")
			annotatedTypeMirror.addAnnotation(locAnn)

			//Change type to: Class<@Local ...>
//			annotatedTypeMirror.accept(new TypeAnnotator(atypeFactory) {
//				override def visitDeclared(typ : AnnotatedTypeMirror.AnnotatedDeclaredType, p : Void) : Void = {
//					require(typ.getUnderlyingType.asElement().getSimpleName.toString == "Class")
//					val typeArg = typ.getTypeArguments.get(0)
//					typeArg.clearAnnotations()
//					typeArg.addAnnotation(localAnnotation)
//					null
//				}
//			}, null)
		}

		super.visitMemberSelect(node, annotatedTypeMirror)
	}

	override def visitMethodInvocation(node : MethodInvocationTree, p : AnnotatedTypeMirror) : Void =  node.getMethodSelect match {
		case memberSelectTree : MemberSelectTree =>

			val receiver : ExpressionTree = memberSelectTree.getExpression

			atypeFactory.getAnnotatedType(receiver) match {
				case adt : AnnotatedDeclaredType
					//Method is member of JReplicaSystem
					if adt.getUnderlyingType.asElement().getSimpleName.toString == "JReplicaSystem" =>

					//Method name is replicate
					if (memberSelectTree.getIdentifier.toString == "replicate") {


//						//Method has 2 or 3 arguments
//						val setArg : ExpressionTree =
//							node.getArguments.size() match {
//								case 3 => node.getArguments.get(1)
//								case 2 => node.getArguments.get(0)
//								case _ => sys.error("unknown replicate implementation")
//							}
//
//						val setArgT = atypeFactory.getAnnotatedType(setArg)
//
//						val targs = node.getTypeArguments
//						//TODO: Check type arguments here?
//
//						println(s"args = ${node.getArguments}, targs = $targs")



					}
				case _ =>
			}
			super.visitMethodInvocation(node, p)

		case _ =>
			super.visitMethodInvocation(node, p)
	}



}

