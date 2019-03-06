package de.tudarmstadt.consistency.checker

import com.sun.source.tree.{LiteralTree, MemberSelectTree, NewClassTree}
import javax.lang.model.`type`.DeclaredType
import javax.lang.model.element.AnnotationMirror
import org.checkerframework.framework.`type`.{AnnotatedTypeFactory, AnnotatedTypeMirror}
import org.checkerframework.framework.`type`.treeannotator.TreeAnnotator
import org.checkerframework.framework.`type`.typeannotator.TypeAnnotator
import org.checkerframework.framework.`type`.visitor.{AnnotatedTypeVisitor, SimpleAnnotatedTypeVisitor}
import org.checkerframework.javacutil.AnnotationUtils

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
			annotatedTypeMirror.addAnnotation(localAnnotation)

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



}

