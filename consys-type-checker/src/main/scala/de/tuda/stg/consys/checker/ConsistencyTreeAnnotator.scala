package de.tuda.stg.consys.checker

import com.sun.source.tree._
import de.tuda.stg.consys.checker.qual.{Immutable, Mixed, ThisConsistent}
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.AnnotatedDeclaredType
import org.checkerframework.framework.`type`.treeannotator.TreeAnnotator
import org.checkerframework.framework.`type`.typeannotator.TypeAnnotator
import org.checkerframework.framework.`type`.{AnnotatedTypeFactory, AnnotatedTypeMirror}
import org.checkerframework.javacutil.{AnnotationUtils, TreeUtils, TypesUtils}

import javax.lang.model.element._
import scala.jdk.CollectionConverters._

/**
	* Created on 06.03.19.
	*
	* @author Mirko Köhler
	*/
class ConsistencyTreeAnnotator(implicit tf : ConsistencyAnnotatedTypeFactory) extends TreeAnnotator(tf) {
	import TypeFactoryUtils._

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
		} else if (TreeUtils.elementFromUse(node).getKind == ElementKind.FIELD) {
			val receiverType = tf.getAnnotatedType(node.getExpression)
			val receiver = TypesUtils.getTypeElement(receiverType.getUnderlyingType)

			// adapt field for receiver
			receiverType.getAnnotations.forEach(ann => {
				if (qualHierarchy.findAnnotationInHierarchy(List(ann).asJava, inconsistentAnnotation) != null) {
					val qualifier = receiverType.getEffectiveAnnotationInHierarchy(inconsistentAnnotation)
					visitField(node, typeMirror, receiver, qualifier)

					// Changes level of type argument of Ref<...> to weakest between receiver and field
					node.getExpression match {
						// skip this step if receiver is 'this'
						case id: IdentifierTree if id.getName.toString == "this" => ()

						case _ => typeMirror match {
							case adt: AnnotatedDeclaredType if adt.getUnderlyingType.asElement.getSimpleName.toString == "Ref" =>
								val typeArgument = adt.getTypeArguments.get(0)
								// get weakest type between type argument and receiver
								val lup =
									if (tf.areSameByClass(ann, classOf[Mixed]))
										qualHierarchy.leastUpperBound(
											typeArgument.getEffectiveAnnotationInHierarchy(inconsistentAnnotation),
											typeMirror.getEffectiveAnnotationInHierarchy(inconsistentAnnotation))
									else
										qualHierarchy.leastUpperBound(
											typeArgument.getEffectiveAnnotationInHierarchy(inconsistentAnnotation),
											ann)
								typeArgument.replaceAnnotation(lup)

							case _ => ()
						}
					}
				} else if (qualHierarchy.findAnnotationInHierarchy(List(ann).asJava, immutableAnnotation) != null) {
					val fieldQualifier = typeMirror.getEffectiveAnnotationInHierarchy(immutableAnnotation)
					val lup = qualHierarchy.leastUpperBound(fieldQualifier, ann)
					typeMirror.replaceAnnotation(lup)

				} else {
					typeMirror.replaceAnnotation(ann)
				}
			})
		}

		super.visitMemberSelect(node, typeMirror)
	}

	override def visitIdentifier(node: IdentifierTree, typeMirror: AnnotatedTypeMirror): Void = {
		if (TreeUtils.isExplicitThisDereference(node)) {
			// adapt 'this' to currently visited context
			val (_, qualifier) = tf.peekVisitClassContext
			typeMirror.replaceAnnotation(qualifier)
			// 'this' is always mutable
			typeMirror.replaceAnnotation(mutableAnnotation)
			return super.visitIdentifier(node, typeMirror)
		}

		if (!tf.isVisitClassContextEmpty) {
			val element = TreeUtils.elementFromUse(node)
			element.getKind match {
				case ElementKind.FIELD =>
					val (receiver, qualifier) = tf.peekVisitClassContext
					visitField(node, typeMirror, receiver, qualifier)
				case ElementKind.PARAMETER | ElementKind.LOCAL_VARIABLE =>
					// replaces @ThisConsistent with appropriate type
					//typeMirror.replaceAnnotation(inferThisTypeFromEnclosingMethod(element))
					tf.replaceThisConsistent(typeMirror)
				case _ =>
			}
		}

		super.visitIdentifier(node, typeMirror)
	}

	override def visitVariable(node: VariableTree, typeMirror: AnnotatedTypeMirror): Void = {
		// TODO: can get called before Visitor.processClassTree -> class context is not ready
		val element = TreeUtils.elementFromDeclaration(node)
		// this might be called outside from a type checking context
		if (!tf.isVisitClassContextEmpty && element.getKind.isField) {
			val (receiver, qualifier) = tf.peekVisitClassContext
			//visitField(element, typeMirror, receiver, qualifier)
		}

		super.visitVariable(node, typeMirror)
	}

	private def visitField(field: VariableElement, typeMirror: AnnotatedTypeMirror, receiver: TypeElement, qualifier: AnnotationMirror): Unit = {
		if (tf.areSameByClass(qualifier, classOf[Mixed])) {
			val inferred = tf.mixedInferenceVisitor.getInferred(receiver, qualifier, field)
			inferred match {
				case Some(value) => typeMirror.replaceAnnotation(value)
				case None => sys.error("ConSysT type checker bug: mixed inference failed")
			}
		} else {
			typeMirror.replaceAnnotation(qualifier)
		}
	}

	private def visitField(tree: ExpressionTree, typeMirror: AnnotatedTypeMirror, receiver: TypeElement, receiverQualifier: AnnotationMirror): Unit = {
		val field = TreeUtils.elementFromUse(tree).asInstanceOf[VariableElement]
		if (field.getModifiers.contains(Modifier.STATIC)) {
			typeMirror.replaceAnnotation(inconsistentAnnotation)
		} else if (tf.areSameByClass(receiverQualifier, classOf[Mixed]) && isPrivateOrProtected(field)) {
			// use the mixed inferred consistency level
			val inferred = tf.mixedInferenceVisitor.getInferred(receiver, receiverQualifier, field)
			inferred match {
				case Some(fieldType) => tf.mixedInferenceVisitor.getReadAccess(tree) match {
					case Some(methodType) if !tf.getAnnotatedType(field).hasAnnotation(classOf[Immutable]) =>
						// adapt read result to operation level (skip for immutable fields)
						val lup = qualHierarchy.leastUpperBound(fieldType, methodType)
						typeMirror.replaceAnnotation(lup)
						// read access must be treated as immutable if the consistency type is adapted
						if (AnnotationUtils.areSame(lup, methodType) && !AnnotationUtils.areSame(fieldType, methodType))
							typeMirror.replaceAnnotation(immutableAnnotation)
					case _ =>
						typeMirror.replaceAnnotation(fieldType)
				}
				case None => sys.error("ConSysT type checker bug: mixed inference failed")
			}
		} else if (tf.areSameByClass(receiverQualifier, classOf[Mixed]))
			typeMirror.replaceAnnotation(getQualifierForOp(getNameForMixedDefaultOp(receiverQualifier)).get)
		else {
			typeMirror.replaceAnnotation(receiverQualifier)
		}
	}

	override def visitMethodInvocation(node: MethodInvocationTree, typeMirror: AnnotatedTypeMirror): Void = {
		val method = TreeUtils.elementFromUse(node)
		val recvQualifier = node.getMethodSelect match {
			case mst: MemberSelectTree if !TreeUtils.isExplicitThisDereference(mst) =>
				val typ = tf.getAnnotatedType(mst.getExpression)
				typ.getEffectiveAnnotationInHierarchy(inconsistentAnnotation)
			case _ =>
				tf.peekVisitClassContext._2
		}

		// replace @ThisConsistent return types with receiver type or op-level for mixed receivers
		if (AnnotationUtils.containsSameByClass(method.getReturnType.getAnnotationMirrors, classOf[ThisConsistent])) {
			// return type inference for mixed getters
			typeMirror.replaceAnnotation(inferThisTypeFromReceiver(recvQualifier, method))
		}

		super.visitMethodInvocation(node, typeMirror)
	}
}
