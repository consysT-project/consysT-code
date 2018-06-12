package de.tudarmstadt.consistency.checker;
import com.sun.source.tree.*;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.common.basetype.BaseTypeVisitor;
import org.checkerframework.framework.source.Result;
import org.checkerframework.framework.type.AnnotatedTypeMirror;

import javax.lang.model.element.AnnotationMirror;
import java.util.Set;
import java.util.Stack;

public class ConsistencyVisitor extends BaseTypeVisitor<ConsistencyAnnotatedTypeFactory>{

    public ConsistencyVisitor(BaseTypeChecker checker) {
        super(checker);
    }

    private class ImplicitContext {
		private final Stack<AnnotationMirror> implicitContexts;

		public ImplicitContext() {
			implicitContexts = new Stack<AnnotationMirror>();
			//TODO: This is ugly
			implicitContexts.push(atypeFactory.getQualifierHierarchy().getBottomAnnotations().iterator().next());
		}

		public void set(AnnotationMirror annotation) {
			AnnotationMirror implicitContext = atypeFactory.getQualifierHierarchy().leastUpperBound(annotation, get());
			implicitContexts.push(implicitContext);
		}

		public AnnotationMirror get() {
			return implicitContexts.peek();
		}

		public void reset() {
			implicitContexts.pop();
		}

		public boolean allowsUpdatesTo(AnnotatedTypeMirror type, Tree tree) {

			//TODO: Improve this. We are not only checking the type but also its type parameters. This does not seem sound. How can this be improved?
			if (type instanceof AnnotatedTypeMirror.AnnotatedDeclaredType) {
				AnnotatedTypeMirror.AnnotatedDeclaredType declaredType = (AnnotatedTypeMirror.AnnotatedDeclaredType) type;

				//Check whether all type arguments are allowed to be updated in the implicit context
				for (AnnotatedTypeMirror typeArg : declaredType.getTypeArguments()) {
					if (!allowsUpdatesTo(typeArg, tree)) {
						return false;
					}
				}

			}

			AnnotationMirror typeAnnotation = getAnnotation(type);

			if (typeAnnotation == null) {
				checker.report(Result.warning("consistency.inferred", type, tree), tree);
				return true;
			}

			return atypeFactory.getQualifierHierarchy().isSubtype(get(), typeAnnotation)
				|| atypeFactory.getQualifierHierarchy().getBottomAnnotations().contains(typeAnnotation);
		}
	}


	private final ImplicitContext implicitContext = new ImplicitContext();

	/*
		Increase implicit context.
	 */
    @Override
    public Void visitIf(IfTree node, Void p) {
    	AnnotationMirror conditionAnnotation = weakestConsistencyInExpression(node.getCondition());


    	System.out.println(conditionAnnotation);

    	implicitContext.set(conditionAnnotation);

		//The condition is executed under the implicit context as well .

		Void r = scan(node.getCondition(), p);
	   	r = reduce(scan(node.getThenStatement(), p), r);
		r = reduce(scan(node.getElseStatement(), p), r);

		implicitContext.reset();

    	return r;
	}

	@Override
	public Void visitWhileLoop(WhileLoopTree node, Void p) {
    	AnnotationMirror conditionAnnotation = weakestConsistencyInExpression(node.getCondition());

    	implicitContext.set(conditionAnnotation);

		Void r = scan(node.getCondition(), p);
		r = reduce(scan(node.getStatement(), p), r);

    	implicitContext.reset();

    	return r;
	}

	@Override
	public Void visitDoWhileLoop(DoWhileLoopTree node, Void p) {
    	//TODO: The first loop of a do-while loop is not affected by implicit flow. Does this change anything? Probably not.
		AnnotationMirror conditionAnnotation = weakestConsistencyInExpression(node.getCondition());

		implicitContext.set(conditionAnnotation);

		Void r = scan(node.getCondition(), p);
		r = reduce(scan(node.getStatement(), p), r);

		implicitContext.reset();

		return r;
	}

	@Override
	public Void visitForLoop(ForLoopTree node, Void p) {
		AnnotationMirror conditionAnnotation = weakestConsistencyInExpression(node.getCondition());

		Void r = scan(node.getCondition(), p);
		//TODO: How to correctly track implicit flow for the for loop variable?
		r = reduce(scan(node.getInitializer(), p), r);

		implicitContext.set(conditionAnnotation);

		r = reduce(scan(node.getUpdate(), p), r);
		r = reduce(scan(node.getStatement(), p), r);

		implicitContext.reset();

		return r;
	}

	@Override
	public Void visitEnhancedForLoop(EnhancedForLoopTree node, Void p) {
    	//TODO: add variable to implicit context?
		AnnotationMirror conditionAnnotation = weakestConsistencyInExpression(node.getExpression());

		Void r = scan(node.getVariable(), p);
		r = reduce(scan(node.getExpression(), p), r);

		implicitContext.set(conditionAnnotation);

		r = reduce(scan(node.getStatement(), p), r);

		implicitContext.reset();

		return r;
	}

	public Void visitSwitch(SwitchTree node, Void p) {
		AnnotationMirror conditionAnnotation = weakestConsistencyInExpression(node.getExpression());

		Void r = scan(node.getExpression(), p);

		implicitContext.set(conditionAnnotation);

		r = reduce(scan(node.getCases(), p), r);

		implicitContext.reset();

		return r;
	}


	/*
		Check that implicit contexts are correct.
	 */
	@Override
	public Void visitAssignment(AssignmentTree node, Void p) {
		checkAssignment(
				atypeFactory.getAnnotatedType(node.getVariable()),
				atypeFactory.getAnnotatedType(node.getExpression()),
				node
		);

    	return super.visitAssignment(node, p);
	}


	@Override
	//compound assignment is, e.g., i += 23
	public Void visitCompoundAssignment(CompoundAssignmentTree node, Void p) {
		checkAssignment(
				atypeFactory.getAnnotatedType(node.getVariable()),
				atypeFactory.getAnnotatedType(node.getExpression()),
				node
		);

		return super.visitCompoundAssignment(node, p);
	}


	@Override
	public Void visitVariable(VariableTree node, Void p) {
    	ExpressionTree initializer = node.getInitializer();

    	if (initializer != null) {
    		checkAssignment(
    				atypeFactory.getAnnotatedType(node),
					atypeFactory.getAnnotatedType(initializer),
					node
			);
		}

		return super.visitVariable(node, p);
	}

	private void checkAssignment(AnnotatedTypeMirror lhsType, AnnotatedTypeMirror rhsType, Tree tree) {
    	if (!implicitContext.allowsUpdatesTo(lhsType, tree)) {
    		checker.report(
					Result.failure("assignment.type.implicitflow", lhsType, implicitContext.get(), tree),
					tree);
		}
	}

	public Void visitMethodInvocation(MethodInvocationTree node, Void p) {
		ExpressionTree methodSelect = node.getMethodSelect();

		if (methodSelect instanceof MemberSelectTree) {
			MemberSelectTree memberSelectTree = (MemberSelectTree) methodSelect;

			ExpressionTree expr = memberSelectTree.getExpression();

			if (expr != null) {
				checkMethodInvocationReceiver(
						atypeFactory.getAnnotatedType(expr),
						node);
			}
		}

		//implicit context is not used when checking a method implementation.
		//Thus, disallow methods that use weak contexts.
		//TODO: Methods can still have assignments to strong variables. How do we rule out those cases?
		for (ExpressionTree argExpr : node.getArguments()) {
			checkMethodInvocationArgument(
					atypeFactory.getAnnotatedType(argExpr),
					node);
		}

		return super.visitMethodInvocation(node, p);
	}

	private void checkMethodInvocationReceiver(AnnotatedTypeMirror receiverType, Tree tree) {
		if (!implicitContext.allowsUpdatesTo(receiverType, tree)) {
			checker.report(
					Result.failure("invocation.receiver.implicitflow", receiverType, implicitContext.get(), tree),
					tree);
		}
	}

	private void checkMethodInvocationArgument(AnnotatedTypeMirror argType, Tree tree) {
		if (!implicitContext.allowsUpdatesTo(argType, tree)) {
			checker.report(
					Result.failure("invocation.argument.implicitflow", argType, implicitContext.get(), tree),
					tree
			);
		}
	}



	private AnnotationMirror weakestConsistencyInExpression(ExpressionTree node) {
    	/*
			TODO: This requires an annotated JDK in order to work correctly.

			With an unannotated JDK we have the following behavior:

			Definitions:
				@Strong String s1
				@Weak String s2
				public static @PolyConsistent boolean equals(@PolyConsistent Object o1, @PolyConsistent Object o2)

			s1.equals("hello") --> inconsistent (the normal equals method is always @inconsistent because it is not annotated)
			equals(s1, "hello") --> strong
			equals(s1, s2) --> weak
    	 */

    	//Retrieve the (inferred) annotated type
    	return getAnnotation(atypeFactory.getAnnotatedType(node));
	}

	private AnnotationMirror getAnnotation(AnnotatedTypeMirror type) {
		//can only include consistency annotations
		Set<AnnotationMirror> annotations = type.getAnnotations();

		if (annotations.size() == 1) {
			return annotations.iterator().next();
		} else if (annotations.isEmpty()) {
			return null;
		}

		throw new  AssertionError("inferred an unexpected number of annotations. Expected 1 annotation, but got: " + annotations);
	}





}
