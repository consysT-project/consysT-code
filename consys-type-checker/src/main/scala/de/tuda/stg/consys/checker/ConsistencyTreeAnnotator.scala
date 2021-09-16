package de.tuda.stg.consys.checker

import com.sun.source.tree._
import com.sun.tools.javac.tree.JCTree.JCFieldAccess
import de.tuda.stg.consys.checker.qual.Mixed
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.{AnnotatedDeclaredType, AnnotatedExecutableType}
import org.checkerframework.framework.`type`.treeannotator.TreeAnnotator
import org.checkerframework.framework.`type`.typeannotator.TypeAnnotator
import org.checkerframework.framework.`type`.{AnnotatedTypeFactory, AnnotatedTypeMirror}
import org.checkerframework.javacutil.{AnnotationUtils, ElementUtils, TreeUtils, TypesUtils}

import javax.lang.model.element.{AnnotationMirror, Modifier, TypeElement, VariableElement}
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
									val lup =
										if (tf.areSameByClass(ann, classOf[Mixed]))
											tf.getQualifierHierarchy.leastUpperBound(
												typeArgument.getEffectiveAnnotationInHierarchy(inconsistentAnnotation),
												typeMirror.getEffectiveAnnotationInHierarchy(inconsistentAnnotation))
										else
											tf.getQualifierHierarchy.leastUpperBound(
												typeArgument.getEffectiveAnnotationInHierarchy(inconsistentAnnotation),
												ann)
									typeArgument.replaceAnnotation(lup)

								case _ => ()
							}
						}

					} else if (tf.getQualifierHierarchy.findAnnotationInHierarchy(List(ann), immutableAnnotation) != null) {
						val fieldQualifier = typeMirror.getEffectiveAnnotationInHierarchy(immutableAnnotation)
						val lup = tf.getQualifierHierarchy.leastUpperBound(fieldQualifier, ann)
						typeMirror.replaceAnnotation(lup)

					} else {
						typeMirror.replaceAnnotation(ann)
					}

				})
			}
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
		if (field.getModifiers.contains(Modifier.STATIC)) {
			typeMirror.replaceAnnotation(inconsistentAnnotation)
		} else if (tf.areSameByClass(qualifier, classOf[Mixed]) && (field.getModifiers.contains(Modifier.PRIVATE) || field.getModifiers.contains(Modifier.PROTECTED))) {
			val inferred = tf.inferenceVisitor.getInferred(receiver, qualifier, field)
			inferred match {
				case Some(fieldType) => tf.inferenceVisitor.getReadAccess(tree) match {
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
		} else if (tf.areSameByClass(qualifier, classOf[Mixed]))
			typeMirror.replaceAnnotation(getQualifierForOp(getNameForMixedDefaultOp(qualifier)).get)
		else {
			typeMirror.replaceAnnotation(qualifier)
		}
	}


	override def visitMethodInvocation(node: MethodInvocationTree, typeMirror: AnnotatedTypeMirror): Void = {
		val method = TreeUtils.elementFromUse(node)
		val methodType = tf.getAnnotatedType(method)
		val methodName = method.getSimpleName.toString.toLowerCase
		val recvQualifier = node.getMethodSelect match {
			case mst: MemberSelectTree if !TreeUtils.isExplicitThisDereference(mst) =>
				val typ = tf.getAnnotatedType(mst.getExpression).asInstanceOf[AnnotatedDeclaredType]
				typ.getEffectiveAnnotationInHierarchy(inconsistentAnnotation)
			case _ =>
				tf.peekVisitClassContext()._2
		}

		if (getExplicitConsistencyAnnotation(methodType.getReturnType).isEmpty &&
			methodName.startsWith("get")) { // TODO: include fields for method name check
			val inferred =
				if (isMixedQualifier(recvQualifier)) getQualifierForOp(getMixedOpForMethod(method, getNameForMixedDefaultOp(recvQualifier))).get
				else recvQualifier
			typeMirror.replaceAnnotation(inferred)
		}

		super.visitMethodInvocation(node, typeMirror)
	}
}
