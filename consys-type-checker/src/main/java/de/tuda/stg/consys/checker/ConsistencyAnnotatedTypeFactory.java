package de.tuda.stg.consys.checker;

import com.sun.source.tree.MemberSelectTree;
import com.sun.source.tree.MethodInvocationTree;
import com.sun.source.tree.MethodTree;
import com.sun.source.tree.Tree;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.util.List;
import de.tuda.stg.consys.annotations.MethodWriteList;
import de.tuda.stg.consys.annotations.MixedField;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.type.*;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.framework.type.typeannotator.ListTypeAnnotator;
import org.checkerframework.framework.type.typeannotator.TypeAnnotator;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.TreeUtils;
import org.checkerframework.javacutil.TypeAnnotationUtils;
import scala.Tuple2;
import scala.jdk.javaapi.CollectionConverters;

import javax.lang.model.element.*;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Set;
import java.util.Stack;

public class ConsistencyAnnotatedTypeFactory extends BaseAnnotatedTypeFactory {

	public final MixedInferenceVisitor mixedInferenceVisitor;

	private final Stack<Tuple2<TypeElement, AnnotationMirror>> visitClassContext;
	private AnnotationMirror methodReceiverContext;

	public ConsistencyAnnotatedTypeFactory(BaseTypeChecker checker) {
        /*
        	Set useFlow to false if the flow analysis should be used.
         */
		super(checker, false);
		if (this.getClass().equals(ConsistencyAnnotatedTypeFactory.class)) {
			this.postInit();
		}

		this.mixedInferenceVisitor = new MixedInferenceVisitor(this);
		this.visitClassContext = new Stack<>();
	}


	@Override
	protected TreeAnnotator createTreeAnnotator() {
		TreeAnnotator others = super.createTreeAnnotator();
		return new ListTreeAnnotator(others, new ConsistencyTreeAnnotator(this));
	}

	@Override
	protected TypeAnnotator createTypeAnnotator() {
		TypeAnnotator others = super.createTypeAnnotator();
		return new ListTypeAnnotator(others, new ConsistencyTypeAnnotator(this));
	}

	@Override
	protected TypeHierarchy createTypeHierarchy() {
		DefaultTypeHierarchy hierarchy = new DefaultTypeHierarchy(
			checker, getQualifierHierarchy(), checker.getBooleanOption("ignoreRawTypeArguments", true), checker.hasOption("invariantArrays"));

		return new ConsistencyTypeHierarchy(hierarchy, this);
	}

	@Override
	protected QualifierHierarchy createQualifierHierarchy() {
		return new ConsistencyQualifierHierarchy(getSupportedTypeQualifiers(), getElementUtils(), this);
	}

	@Override
	public AnnotatedTypeMirror getAnnotatedType(Tree tree) {
		if (tree.getKind() == Tree.Kind.METHOD && ((MethodTree)tree).getName().toString().toLowerCase().startsWith("get")) {
			// disable cache when querying methods, so that we don't skip the return type adaptation
			// fields are never cached, so we don't need additional rules there
			boolean prevShouldCache = super.shouldCache;
			super.shouldCache = false;
			var result = super.getAnnotatedType(tree);
			super.shouldCache = prevShouldCache;
			return result;
		}

		return super.getAnnotatedType(tree);
	}

	@Override
	protected void addComputedTypeAnnotations(Tree tree, AnnotatedTypeMirror type, boolean iUseFlow) {
		var prevMethodReceiverContext = methodReceiverContext;
		// adapts the receiver context, so that the TypeAnnotator has the correct information when inferring
		// return types on mixed getters
		if (tree.getKind() == Tree.Kind.METHOD) {
			if (!visitClassContext.isEmpty())
				methodReceiverContext = visitClassContext.peek()._2;
		} else if (tree.getKind() == Tree.Kind.METHOD_INVOCATION) {
			var selectTree = ((MethodInvocationTree) tree).getMethodSelect();
			if (selectTree.getKind() == Tree.Kind.MEMBER_SELECT &&
					!TreeUtils.isExplicitThisDereference(((MemberSelectTree) selectTree).getExpression())) {
				methodReceiverContext = getAnnotatedType(((MemberSelectTree) selectTree).getExpression()).
						getAnnotationInHierarchy(TypeFactoryUtils.inconsistentAnnotation(this));
			} else if (!visitClassContext.isEmpty()) {
				methodReceiverContext = visitClassContext.peek()._2;
			}
		}

		super.addComputedTypeAnnotations(tree, type, iUseFlow);

		if (tree.getKind() == Tree.Kind.METHOD || tree.getKind() == Tree.Kind.METHOD_INVOCATION) {
			methodReceiverContext = prevMethodReceiverContext;
		}
	}

	@Override
	public void addComputedTypeAnnotations(Element elt, AnnotatedTypeMirror type) {
		var prevMethodReceiverContext = methodReceiverContext;
		// adapts the receiver context, so that the TypeAnnotator has the correct information when inferring
		// return types on mixed getters
		if (elt.getKind() == ElementKind.METHOD && !visitClassContext.isEmpty()) {
			methodReceiverContext = peekVisitClassContext()._2;
		}

		super.addComputedTypeAnnotations(elt, type);
		methodReceiverContext = prevMethodReceiverContext;
	}

	@Override
	public Set<AnnotationMirror> getDeclAnnotations(Element elt) {
		var result = super.getDeclAnnotations(elt);

		if (elt.getKind() == ElementKind.METHOD) {
			// add @MethodWriteList annotation containing each field the method updates (persists in .class files)
			var fieldSet = mixedInferenceVisitor.getMethodWriteList((ExecutableElement) elt);
			var annotationValue = new ArrayList<AnnotationValue>();
			if (fieldSet.isDefined()) {
				for (var field : CollectionConverters.asJava(fieldSet.get())) {
					// for some reason we have to provide the string array annotation value
					// as a List of AnnotationValues of strings
					annotationValue.add(AnnotationBuilder.
							elementNamesValues("", field.getSimpleName().toString()).get(""));
				}

				result.add(AnnotationBuilder.fromClass(getElementUtils(), MethodWriteList.class,
						AnnotationBuilder.elementNamesValues("value", annotationValue)));
			}
		} else if (elt.getKind() == ElementKind.FIELD) {
			// add runtime @MixedField annotation
			var withWeakDefault = mixedInferenceVisitor.getInferred(
					(TypeElement) elt.getEnclosingElement(),
					TypeFactoryUtils.mixedAnnotation(WeakOp.class, this), (VariableElement) elt);
			var withStrongDefault = mixedInferenceVisitor.getInferred(
					(TypeElement) elt.getEnclosingElement(),
					TypeFactoryUtils.mixedAnnotation(StrongOp.class, this), (VariableElement) elt);

			var values = new HashMap<String, AnnotationValue>();
			if (withWeakDefault.isDefined()) {
				var map = AnnotationBuilder.elementNamesValues(
						"consistencyForWeakDefault",
						withWeakDefault.get().getAnnotationType().asElement().getSimpleName().toString());
				values.putAll(map);
			}
			if (withStrongDefault.isDefined()) {
				var map = AnnotationBuilder.elementNamesValues(
						"consistencyForStrongDefault",
						withStrongDefault.get().getAnnotationType().asElement().getSimpleName().toString());
				values.putAll(map);
			}

			// only add if annotation s fully constructable
			if (values.size() > 1) {
				var sym = (Symbol.VarSymbol) elt;
				for (var a : sym.getDeclarationAttributes()) {
					// only add if not already present
					if (a.getAnnotationType().asElement().getSimpleName().toString().equals("MixedField")) {
						return result;
					}
				}

				var annotation = AnnotationBuilder.fromClass(getElementUtils(), MixedField.class, values);
				sym.appendAttributes(List.of(
						TypeAnnotationUtils.createCompoundFromAnnotationMirror(annotation, getProcessingEnv())));
			}
		}
		return result;
	}

	public boolean isInMixedClassContext() {
		return !visitClassContext.empty() && TypeFactoryUtils.isMixedQualifier(visitClassContext.peek()._2, this);
	}

	public void pushVisitClassContext(TypeElement clazz, AnnotationMirror type) {
		visitClassContext.push(new Tuple2<>(clazz, type));
	}

	public void popVisitClassContext() {
		visitClassContext.pop();
	}

	public Tuple2<TypeElement, AnnotationMirror> peekVisitClassContext() {
		return visitClassContext.peek();
	}

	public boolean isVisitClassContextEmpty() {
		return visitClassContext.isEmpty();
	}

	public AnnotationMirror getMethodReceiverContext() {
		return methodReceiverContext;
	}

	public ConsistencyVisitorImpl getVisitor() {
		return (ConsistencyVisitorImpl) checker.getVisitor();
	}
}
