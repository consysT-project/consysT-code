package de.tuda.stg.consys.checker;

import com.sun.source.tree.ClassTree;
import com.sun.source.tree.Tree;
import de.tuda.stg.consys.checker.qual.Inconsistent;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.qual.TypeUseLocation;
import org.checkerframework.framework.type.*;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.framework.type.typeannotator.ListTypeAnnotator;
import org.checkerframework.framework.type.typeannotator.TypeAnnotator;
import org.checkerframework.framework.util.QualifierKind;
import org.checkerframework.framework.util.defaults.QualifierDefaults;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.Pair;
import org.checkerframework.javacutil.TreeUtils;
import scala.Tuple2;

import javax.lang.model.element.*;
import java.util.Stack;

public class ConsistencyAnnotatedTypeFactory extends BaseAnnotatedTypeFactory {

	private final InferenceVisitor inferenceVisitor;

	private final Stack<Tuple2<TypeElement, String>> mixedClassContext;

	public ConsistencyAnnotatedTypeFactory(BaseTypeChecker checker) {
        /*
        	Set useFlow to false if the flow analysis should be used.
         */
		super(checker, false);
		if (this.getClass().equals(ConsistencyAnnotatedTypeFactory.class)) {
			this.postInit();
		}

		this.inferenceVisitor = new InferenceVisitor(this);
		this.mixedClassContext = new Stack<>();
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
	protected void addCheckedCodeDefaults(QualifierDefaults defs) {
		defs.addCheckedCodeDefault(
				AnnotationBuilder.fromClass(getElementUtils(), Inconsistent.class),
				TypeUseLocation.FIELD);

		super.addCheckedCodeDefaults(defs);
	}

	protected void addCheckedCodeDefaultsSkip(QualifierDefaults defs) {
		super.addCheckedCodeDefaults(defs);
	}

	@Override
	protected void addComputedTypeAnnotations(Tree tree, AnnotatedTypeMirror type, boolean iUseFlow) {
		super.addComputedTypeAnnotations(tree, type, iUseFlow);

		if (tree instanceof ClassTree) {
			inferenceVisitor.visitClass((ClassTree)tree, null);
		}

		if ((tree.getKind() == Tree.Kind.IDENTIFIER || tree.getKind() == Tree.Kind.VARIABLE) &&
				TreeUtils.elementFromTree(tree).getKind() == ElementKind.FIELD) {
			annotateField((VariableElement) TreeUtils.elementFromTree(tree), type);
		}
	}

	@Override
	public void addComputedTypeAnnotations(Element elt, AnnotatedTypeMirror type) {
		super.addComputedTypeAnnotations(elt, type);

		if (elt.getKind() == ElementKind.FIELD) {
			annotateField((VariableElement) elt, type);
		}
	}

	private void annotateField(VariableElement elt, AnnotatedTypeMirror type) {
		if (elt.getSimpleName().toString().equals("this")) // TODO: also do this for "super"?
			return;

		var annotation = inferenceVisitor.getInferredFieldOrFromSuperclass(elt, mixedClassContext.peek()._1, mixedClassContext.peek()._2)._1;
		if (annotation.isDefined()) {
			type.clearAnnotations();
			type.addAnnotation(annotation.get());
		}
	}

	public void setMixedClassContext(TypeElement mixedClassContext, String defaultOpLevel) {
		this.mixedClassContext.push(new Tuple2<>(mixedClassContext, defaultOpLevel));
	}

	public void resetMixedClassContext() {
		this.mixedClassContext.pop();
	}

	public String qualifierForOperation(String operation) {
		// TODO: recomputing
		return inferenceVisitor.buildQualifierMap().get(operation).get();
	}

	public void processClassWithoutCache(ClassTree node, String opLevel) {
		shouldCache = false;

		((ConsistencyVisitorImpl)checker.getVisitor()).processClassTree(node, opLevel);

		shouldCache = true;
	}
}
