package de.tuda.stg.consys.checker;

import com.sun.source.tree.ClassTree;
import com.sun.source.tree.MemberSelectTree;
import com.sun.source.tree.Tree;
import de.tuda.stg.consys.checker.qual.Inconsistent;
import de.tuda.stg.consys.checker.qual.Mixed;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.qual.TypeUseLocation;
import org.checkerframework.framework.type.*;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.framework.type.typeannotator.ListTypeAnnotator;
import org.checkerframework.framework.type.typeannotator.TypeAnnotator;
import org.checkerframework.framework.util.defaults.QualifierDefaults;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.TreeUtils;
import org.checkerframework.javacutil.TypesUtils;
import scala.Option;
import scala.Tuple2;
import scala.Tuple4;

import javax.lang.model.element.*;
import java.util.Stack;

public class ConsistencyAnnotatedTypeFactory extends BaseAnnotatedTypeFactory {

	public final InferenceVisitor inferenceVisitor;

	private final Stack<Tuple2<TypeElement, AnnotationMirror>> visitClassContext;

	public ConsistencyAnnotatedTypeFactory(BaseTypeChecker checker) {
        /*
        	Set useFlow to false if the flow analysis should be used.
         */
		super(checker, false);
		if (this.getClass().equals(ConsistencyAnnotatedTypeFactory.class)) {
			this.postInit();
		}

		this.inferenceVisitor = new InferenceVisitor(this);
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

		AnnotationMirror recvConsistency = null;

		// TODO: static field select
		switch (tree.getKind()) {
			case MEMBER_SELECT:
				// member select case is only relevant for mixed classes
				// TODO: include method invocations
				if (TreeUtils.elementFromTree(tree).getKind() != ElementKind.FIELD || TreeUtils.isClassLiteral(tree))
					return;

				var recvType = getAnnotatedType(((MemberSelectTree)tree).getExpression());
				if (TreeUtils.isExplicitThisDereference(((MemberSelectTree)tree).getExpression()) && !visitClassContext.isEmpty()) {
					// adapt 'this' to type of currently processed class
					recvType.replaceAnnotation(visitClassContext.peek()._2);
				}

				recvConsistency = recvType.getAnnotationInHierarchy(TypeFactoryUtils.inconsistentAnnotation(this));
				var classElement = TypesUtils.getTypeElement(recvType.getUnderlyingType());
				var classTree = getTreeUtils().getTree(classElement);

				if (classTree != null) {
					if (areSameByClass(recvConsistency, Mixed.class)) {
						var defaultOpLevel = TypeFactoryUtils.getMixedDefaultOp(recvConsistency, this);
						pushVisitClassContext(classElement, recvConsistency);
						inferenceVisitor.visitClass(classTree, new Tuple4<>(Option.empty(), Option.apply(defaultOpLevel), Option.empty(), Option.empty()));
						popVisitClassContext();
					}
					// visit class under consistency of receiver to check compatibility
					getVisitor().visitOrQueueClassTree(classTree, recvConsistency);
				} else {
					// TODO: issue warning when using class with consistency for which check was not already performed
					// manually run inference for unavailable mixed classes
					if (areSameByClass(recvConsistency, Mixed.class)) {
						var defaultOpLevel = TypeFactoryUtils.getMixedDefaultOp(recvConsistency, this);
						pushVisitClassContext(classElement, recvConsistency);
						inferenceVisitor.visitClass(classElement, new Tuple4<>(Option.empty(), Option.apply(defaultOpLevel), Option.empty(), Option.empty()));
						popVisitClassContext();
					}
				}
				// deliberate fall through
				if (!TreeUtils.isExplicitThisDereference(((MemberSelectTree)tree).getExpression())) {
					// if we are not in the class, i.e. receiver is not 'this', proceed to get field type
					pushVisitClassContext(classElement, recvConsistency);
				} else {
					// if we are in the class,
					recvConsistency = null;
				}
			case IDENTIFIER:
			case VARIABLE:
				if (visitClassContext.empty())
					return;
				var field = TreeUtils.elementFromTree(tree);
				if (field == null || field.getKind() != ElementKind.FIELD) {
					if (recvConsistency != null) popVisitClassContext();
					return;
				}

				// for non-mixed classes we only need the class qualifier
				if (!areSameByClass(peekVisitClassContext()._2, Mixed.class)) {
					type.replaceAnnotation(peekVisitClassContext()._2);
					if (recvConsistency != null) popVisitClassContext();
					return;
				}

				// explicitly defined or inferred annotation
				var annotation = type.getAnnotationInHierarchy(TypeFactoryUtils.inconsistentAnnotation(this));
				if (!type.hasExplicitAnnotation(annotation)) {
					annotation = getFieldAnnotation((VariableElement) field);
				}

				var opLevelForRead = inferenceVisitor.refinementTable().get(tree);

				// handle read access
				if (opLevelForRead.isDefined() && annotation != null) {
					var lup = getQualifierHierarchy().leastUpperBound(opLevelForRead.get(), annotation);
					type.replaceAnnotation(lup);
					// read access must be treated as immutable if we have to adapt the consistency type
					if (AnnotationUtils.areSame(lup, opLevelForRead.get()) &&
							!AnnotationUtils.areSame(annotation, opLevelForRead.get())) {
						type.replaceAnnotation(TypeFactoryUtils.immutableAnnotation(this));
					}
				} else if (annotation != null) {
					type.replaceAnnotation(annotation);
				}
		}

		if (recvConsistency != null) popVisitClassContext();
	}

	@Override
	public void addComputedTypeAnnotations(Element elt, AnnotatedTypeMirror type) {
		// When encountering a method invocation on a class that was not yet visited,
		// run the inference first in order to get inferred return type levels
		if (elt.getKind() == ElementKind.METHOD) {
			var classElement = elt.getEnclosingElement();
			var classTree = getTreeUtils().getTree(classElement);
			if (classTree != null && classTree.getKind() == Tree.Kind.CLASS) {
				inferenceVisitor.visitClass((ClassTree)classTree);
			} else if (classElement.getKind() == ElementKind.CLASS) {
				inferenceVisitor.visitClass((TypeElement)classElement);
			}
		}

		super.addComputedTypeAnnotations(elt, type);

		if (elt.getKind() == ElementKind.FIELD) {
			// for non-mixed classes we only need the class qualifier
			if (!areSameByClass(peekVisitClassContext()._2, Mixed.class)) {
				type.replaceAnnotation(peekVisitClassContext()._2);
				return;
			}

			if (type.hasExplicitAnnotation(type.getAnnotationInHierarchy(TypeFactoryUtils.inconsistentAnnotation(this))))
				return;

			var anno = getFieldAnnotation((VariableElement) elt);
			if (anno != null) {
				type.replaceAnnotation(anno);
			}
		}
	}

	private AnnotationMirror getFieldAnnotation(VariableElement elt) {
		if (elt.getSimpleName().toString().equals("this")) // TODO: also do this for "super"?
			return null;
		if (visitClassContext.empty())
			return null;

		var classQualifier = visitClassContext.peek()._2;
		if (areSameByClass(classQualifier, Mixed.class)) {
			var annotation =
					inferenceVisitor.getInferredFieldOrFromSuperclass(elt, visitClassContext.peek()._1,
							TypeFactoryUtils.getMixedDefaultOp(classQualifier, this))._1;
			if (annotation.isDefined()) {
				return annotation.get();
			} else {
				return null;
			}
		} else {
			return classQualifier;
		}
	}

	public boolean isInMixedClassContext() {
		return !visitClassContext.empty() && areSameByClass(visitClassContext.peek()._2, Mixed.class);
	}

	public void processClassWithoutCache(ClassTree node, AnnotationMirror qualifier) {
		boolean oldShouldCache = shouldCache;
		shouldCache = false;
		//getVisitor().processClassTreeExtern(node, qualifier, false);
		shouldCache = oldShouldCache;
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

	public ConsistencyVisitorImpl getVisitor() {
		return (ConsistencyVisitorImpl) checker.getVisitor();
	}
}
