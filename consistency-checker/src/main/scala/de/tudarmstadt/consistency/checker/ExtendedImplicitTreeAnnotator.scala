package de.tudarmstadt.consistency.checker

import com.sun.source.tree.{LiteralTree, MemberSelectTree, NewClassTree}
import javax.lang.model.element.AnnotationMirror
import org.checkerframework.framework.`type`.{AnnotatedTypeFactory, AnnotatedTypeMirror}
import org.checkerframework.framework.`type`.treeannotator.TreeAnnotator
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
		//Add @Local for every constructor call (new).
		annotatedTypeMirror.clearAnnotations()
		annotatedTypeMirror.addAnnotation(localAnnotation)

		super.visitNewClass(node, annotatedTypeMirror)
	}

	override def visitLiteral(node : LiteralTree, annotatedTypeMirror : AnnotatedTypeMirror) : Void = {
		annotatedTypeMirror.clearAnnotations()
		annotatedTypeMirror.addAnnotation(localAnnotation)
		super.visitLiteral(node, annotatedTypeMirror)
	}

	override def visitMemberSelect(node : MemberSelectTree, annotatedTypeMirror : AnnotatedTypeMirror) : Void = {

		//Class literals are always @Local
		if (node.getIdentifier.contentEquals("class")) {
			//TODO: Add annotation to type parameter instead
			annotatedTypeMirror.clearAnnotations()
			annotatedTypeMirror.addAnnotation(localAnnotation)
		}

		super.visitMemberSelect(node, annotatedTypeMirror)
	}



}

