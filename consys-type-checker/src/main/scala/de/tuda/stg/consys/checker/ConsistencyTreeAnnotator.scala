package de.tuda.stg.consys.checker

import com.sun.source.tree._
import com.sun.tools.javac.tree.JCTree.JCFieldAccess
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.{AnnotatedDeclaredType, AnnotatedExecutableType}
import org.checkerframework.framework.`type`.treeannotator.TreeAnnotator
import org.checkerframework.framework.`type`.typeannotator.TypeAnnotator
import org.checkerframework.framework.`type`.{AnnotatedTypeFactory, AnnotatedTypeMirror}
import org.checkerframework.javacutil.{AnnotationUtils, ElementUtils, TreeUtils, TypesUtils}

import scala.collection.convert.ImplicitConversions.`iterable AsScalaIterable`
import scala.collection.mutable

/**
	* Created on 06.03.19.
	*
	* @author Mirko Köhler
	*/
class ConsistencyTreeAnnotator(tf : AnnotatedTypeFactory) extends TreeAnnotator(tf) {
	import TypeFactoryUtils._

	implicit val implicitTypeFactory : AnnotatedTypeFactory = atypeFactory

	@inline private def qualHierarchy = atypeFactory.getQualifierHierarchy

	private var classContext = ""
	//private var classTable = mutable.Map[String, mutable.Map[String, mutable.Set[String]]]


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
			annotatedTypeMirror.accept(new TypeAnnotator(atypeFactory) {
				override def visitDeclared(typ : AnnotatedTypeMirror.AnnotatedDeclaredType, p : Void) : Void = {
					require(typ.getUnderlyingType.asElement().getSimpleName.toString == "Class")
					val typeArg = typ.getTypeArguments.get(0)
					typeArg.clearAnnotations()
					typeArg.addAnnotation(localAnnotation)
					null
				}
			}, null)
		} else if (node.isInstanceOf[JCFieldAccess]) {
//			println(classOf[ConsistencyTreeAnnotator],
//				s"fieldAccess $node with ${annotatedTypeMirror.getAnnotations} where receiver with ${tf.getAnnotatedType(node.getExpression)}")

			//Checks whether the type is from an executable (i.e. method, constructor, or initializer).
			//In these cases, the annotations can not be changed.
			if (annotatedTypeMirror.isInstanceOf[AnnotatedExecutableType]) {
//				println(classOf[ConsistencyTreeAnnotator],s"skipped")
			} else {
//				val before = s"$annotatedTypeMirror"

				node.getExpression match {
					case id: IdentifierTree if id.getName.toString == "this" => return null
					case _ =>
				}

				annotatedTypeMirror.clearAnnotations()

				val annotationsOfReceiver = tf.getAnnotatedType(node.getExpression).getAnnotations
				annotationsOfReceiver.forEach(ann => {
					annotatedTypeMirror.addAnnotation(ann)

					// Changes level of type argument of Ref<...> to weakest between receiver and field
					// skip this step if receiver is 'this'
					node.getExpression match {
						case id: IdentifierTree if id.getName.toString == "this" => ()

						case _ => annotatedTypeMirror match {
							case adt: AnnotatedDeclaredType if adt.getUnderlyingType.asElement.getSimpleName.toString == "Ref" =>
								val typeArgument = adt.getTypeArguments.get(0)
								// get weakest type between type argument and receiver
								val lowerBound = atypeFactory.getQualifierHierarchy.leastUpperBound(typeArgument.getAnnotations.iterator.next, ann)

								typeArgument.clearAnnotations()
								typeArgument.addAnnotation(lowerBound)

							case _ => ()
						}
					}
				})
//				println(s"in $node: changed $before to $annotatedTypeMirror")
			}
		}

		super.visitMemberSelect(node, annotatedTypeMirror)
	}
}
