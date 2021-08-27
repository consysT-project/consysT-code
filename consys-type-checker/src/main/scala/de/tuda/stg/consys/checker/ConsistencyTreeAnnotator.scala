package de.tuda.stg.consys.checker

import com.sun.source.tree._
import com.sun.tools.javac.tree.JCTree.JCFieldAccess
import de.tuda.stg.consys.checker.qual.Mixed
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.{AnnotatedDeclaredType, AnnotatedExecutableType}
import org.checkerframework.framework.`type`.treeannotator.TreeAnnotator
import org.checkerframework.framework.`type`.typeannotator.TypeAnnotator
import org.checkerframework.framework.`type`.{AnnotatedTypeFactory, AnnotatedTypeMirror}
import org.checkerframework.javacutil.{AnnotationUtils, ElementUtils, TreeUtils, TypesUtils}

import javax.lang.model.element.{AnnotationMirror, TypeElement, VariableElement}
import scala.collection.convert.ImplicitConversions.`iterable AsScalaIterable`
import scala.collection.convert.ImplicitConversions.`collection asJava`
import scala.collection.mutable

/**
	* Created on 06.03.19.
	*
	* @author Mirko Köhler
	*/
class ConsistencyTreeAnnotator(tf : ConsistencyAnnotatedTypeFactory) extends TreeAnnotator(tf) {
	import TypeFactoryUtils._

	implicit val implicitTypeFactory : AnnotatedTypeFactory = atypeFactory

	@inline private def qualHierarchy = atypeFactory.getQualifierHierarchy

	private var classContext = ""
	//private var classTable = mutable.Map[String, mutable.Map[String, mutable.Set[String]]]


	override def visitNewClass(node : NewClassTree, annotatedTypeMirror : AnnotatedTypeMirror) : Void = {
		//Locally generated objects (new Obj...) are always @Local.
		annotatedTypeMirror.replaceAnnotation(localAnnotation)
		annotatedTypeMirror.replaceAnnotation(mutableBottomAnnotation)
		super.visitNewClass(node, annotatedTypeMirror)
	}

	override def visitLiteral(node : LiteralTree, annotatedTypeMirror : AnnotatedTypeMirror) : Void = {
		//Literals are always @MutableBottom @Local.
		annotatedTypeMirror.replaceAnnotation(localAnnotation)
		annotatedTypeMirror.replaceAnnotation(mutableBottomAnnotation)
		super.visitLiteral(node, annotatedTypeMirror)
	}

	override def visitMemberSelect(node : MemberSelectTree, typeMirror : AnnotatedTypeMirror) : Void = {

		//Class literals are always @Local.
		if (node.getIdentifier.contentEquals("class")) {
			//Change type to: @Local Class...
			typeMirror.replaceAnnotation(localAnnotation)
			typeMirror.replaceAnnotation(mutableBottomAnnotation)

			//Change type to: Class<@Local ...>
			typeMirror.accept(new TypeAnnotator(atypeFactory) {
				override def visitDeclared(typ : AnnotatedTypeMirror.AnnotatedDeclaredType, p : Void) : Void = {
					require(typ.getUnderlyingType.asElement().getSimpleName.toString == "Class")
					val typeArg = typ.getTypeArguments.get(0)
					typeArg.replaceAnnotation(localAnnotation)
					typeArg.replaceAnnotation(mutableBottomAnnotation)
					null
				}
			}, null)
		} else if (node.isInstanceOf[JCFieldAccess]) {

			val element = TreeUtils.elementFromUse(node)
			if (element.getKind.isField) {
				val receiverType = tf.getAnnotatedType(node.getExpression)
				val receiver = TypesUtils.getTypeElement(receiverType.getUnderlyingType)

				// adapt field for receiver
				receiverType.getAnnotations.forEach(ann => {
					if (tf.getQualifierHierarchy.findAnnotationInHierarchy(List(ann), inconsistentAnnotation) != null) {
						val qualifier = receiverType.getEffectiveAnnotationInHierarchy(inconsistentAnnotation)
						visitField(node, typeMirror, receiver, qualifier)

						// Changes level of type argument of Ref<...> to weakest between receiver and field
						node.getExpression match {
							// skip this step if receiver is 'this'
							case id: IdentifierTree if id.getName.toString == "this" => () // TODO: should we really ignore this for Refs?

							case _ => typeMirror match {
								case adt: AnnotatedDeclaredType if adt.getUnderlyingType.asElement.getSimpleName.toString == "Ref" =>
									val typeArgument = adt.getTypeArguments.get(0)
									// get weakest type between type argument and receiver
									val lup = tf.getQualifierHierarchy.leastUpperBound(typeArgument.getEffectiveAnnotationInHierarchy(inconsistentAnnotation), ann)
									typeArgument.replaceAnnotation(lup)

								case _ => ()
							}
						}

					} else if (tf.getQualifierHierarchy.findAnnotationInHierarchy(List(ann), immutableAnnotation) != null) {
						val qualifier = receiverType.getEffectiveAnnotationInHierarchy(immutableAnnotation)
						val lup = tf.getQualifierHierarchy.leastUpperBound(qualifier, ann)
						typeMirror.replaceAnnotation(lup)

					} else {
						typeMirror.replaceAnnotation(ann)
					}

				})
			}

			/*
			//Checks whether the type is from an executable (i.e. method, constructor, or initializer).
			//In these cases, the annotations can not be changed.
			if (typeMirror.isInstanceOf[AnnotatedExecutableType]) {
				// println(classOf[ConsistencyTreeAnnotator],s"skipped")
			} else if (!tf.getAnnotatedType(node.getExpression).hasAnnotation(classOf[Mixed])) {
				val annotationsOfReceiver = tf.getAnnotatedType(node.getExpression).getAnnotations
				annotationsOfReceiver.forEach(ann => {
					typeMirror.replaceAnnotation(ann)

					// Changes level of type argument of Ref<...> to weakest between receiver and field
					// skip this step if receiver is 'this'
					if (tf.getQualifierHierarchy.findAnnotationInHierarchy(List(ann), inconsistentAnnotation) != null) {
						node.getExpression match {
							case id: IdentifierTree if id.getName.toString == "this" => () // TODO: should we really ignore this for Refs?

							case _ => typeMirror match {
								case adt: AnnotatedDeclaredType if adt.getUnderlyingType.asElement.getSimpleName.toString == "Ref" =>
									val typeArgument = adt.getTypeArguments.get(0)
									// get weakest type between type argument and receiver
									val lup = tf.getQualifierHierarchy.leastUpperBound(typeArgument.getEffectiveAnnotationInHierarchy(inconsistentAnnotation), ann)
									typeArgument.replaceAnnotation(lup)

								case _ => ()
							}
						}
					}
				})
//				println(s"in $node: changed $before to $annotatedTypeMirror")

			}*/
		}

		super.visitMemberSelect(node, typeMirror)
	}

	override def visitIdentifier(node: IdentifierTree, typeMirror: AnnotatedTypeMirror): Void = {
		if (TreeUtils.isExplicitThisDereference(node)) {
			// adapt 'this' to currently visited context
			val (_, qualifier) = tf.peekVisitClassContext()
			typeMirror.replaceAnnotation(qualifier)
			// 'this' is always mutable
			typeMirror.replaceAnnotation(mutableAnnotation)
			return super.visitIdentifier(node, typeMirror)
		}

		val element = TreeUtils.elementFromUse(node)
		if (element.getKind.isField) {
			val (receiver, qualifier) = tf.peekVisitClassContext() // TODO: exception if no context
			visitField(node, typeMirror, receiver, qualifier)
		}

		super.visitIdentifier(node, typeMirror)
	}

	override def visitVariable(node: VariableTree, typeMirror: AnnotatedTypeMirror): Void = {
		// TODO: can get called before Visitor.processClassTree -> class context is not ready
		val element = TreeUtils.elementFromDeclaration(node)
		// this might be called outside from a type checking context
		if (!tf.isVisitClassContextEmpty && element.getKind.isField) {
			val (receiver, qualifier) = tf.peekVisitClassContext()
			//visitField(element, typeMirror, receiver, qualifier)
		}

		super.visitVariable(node, typeMirror)
	}

	private def visitField(field: VariableElement, typeMirror: AnnotatedTypeMirror, receiver: TypeElement, qualifier: AnnotationMirror): Unit = {
		if (tf.areSameByClass(qualifier, classOf[Mixed])) {
			val inferred = tf.inferenceVisitor.getInferred(receiver, qualifier, field)
			inferred match {
				case Some(value) => typeMirror.replaceAnnotation(value)
				case None =>
					sys.error("inference failed") // TODO: exception if no context
			}
		} else {
			typeMirror.replaceAnnotation(qualifier)
		}
	}

	private def visitField(tree: ExpressionTree, typeMirror: AnnotatedTypeMirror, receiver: TypeElement, qualifier: AnnotationMirror): Unit = {
		val field = TreeUtils.elementFromUse(tree).asInstanceOf[VariableElement]
		if (tf.areSameByClass(qualifier, classOf[Mixed])) {
			val inferred = tf.inferenceVisitor.getInferred(receiver, qualifier, field)
			inferred match {
				case Some(fieldType) => tf.inferenceVisitor.refinementTable.get(tree) match {
					case Some(methodType) =>
						val lup = tf.getQualifierHierarchy.leastUpperBound(fieldType, methodType)
						typeMirror.replaceAnnotation(lup)
						// read access must be treated as immutable if the consistency type is adapted
						if (AnnotationUtils.areSame(lup, methodType) && !AnnotationUtils.areSame(fieldType, methodType))
							typeMirror.replaceAnnotation(immutableAnnotation)
					case None => typeMirror.replaceAnnotation(fieldType)
				}
				case None => sys.error("inference failed") // TODO: exception if no context
			}
		} else {
			typeMirror.replaceAnnotation(qualifier)
		}
	}

	override def visitMethod(node: MethodTree, typeMirror: AnnotatedTypeMirror): Void = {
		// TODO
		null
	}

	override def visitMethodInvocation(node: MethodInvocationTree, typeMirror: AnnotatedTypeMirror): Void = {
		node.getMethodSelect match {
			case mst: MemberSelectTree if !TreeUtils.isExplicitThisDereference(mst) =>
				val recvType = tf.getAnnotatedType(mst.getExpression).asInstanceOf[AnnotatedDeclaredType]
				val annotation = recvType.getEffectiveAnnotationInHierarchy(inconsistentAnnotation)
				val method = TreeUtils.elementFromUse(node)
				tf.returnTypeVisitor.inferenceTable.get(
					getQualifiedName(recvType.getUnderlyingType.asElement().asInstanceOf[TypeElement]),
					getQualifiedName(annotation),
					if (tf.areSameByClass(annotation, classOf[Mixed])) getMixedDefaultOp(annotation) else ""
				) match {
					case Some(value) => value.get(method) match {
						case Some(value) => typeMirror.replaceAnnotation(value)
						case None => //tf.getChecker.reportWarning(method.getElement, "invocation") // TODO
					}
					case None => // method is from bytecode, so we cannot infer anything
				}

			case _ =>
				val recvType = tf.peekVisitClassContext()._1
				val annotation = tf.peekVisitClassContext()._2
				val method = TreeUtils.elementFromUse(node)
				tf.returnTypeVisitor.inferenceTable.get(
					getQualifiedName(recvType), getQualifiedName(annotation), if (tf.areSameByClass(annotation, classOf[Mixed])) getMixedDefaultOp(annotation) else ""
				) match {
					case Some(value) => value.get(method) match {
						case Some(value) => typeMirror.replaceAnnotation(value)
						case None => //tf.getChecker.reportWarning(method.getElement, "invocation") // TODO
					}
					case None => // method is from bytecode, so we cannot infer anything
				}
		}

		super.visitMethodInvocation(node, typeMirror)
	}
}
