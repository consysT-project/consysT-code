package de.tuda.stg.consys.compiler;

import com.sun.source.tree.*;
import com.sun.source.util.*;
import com.sun.tools.javac.api.BasicJavacTask;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeMaker;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Names;

import javax.lang.model.element.Name;
import java.util.Iterator;
import java.util.List;
import java.util.Optional;
import java.util.function.Consumer;

/**
 * Created on 30.09.19.
 *
 * @author Mirko Köhler
 */
public class SampleJavacPlugin implements Plugin {

	@Override
	public String getName() {
		return "MyPlugin";
	}

	@Override
	public void init(JavacTask task, String... args) {
		Context context = ((BasicJavacTask) task).getContext();
		Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "Plugin started: " + getName());

		task.addTaskListener(new TaskListener() {
			@Override
			public void started(TaskEvent taskEvent) {
			}

			@Override
			public void finished(TaskEvent taskEvent) {
				//We need to listen to the ANALYZE phase because we need type information
				if (taskEvent.getKind() != TaskEvent.Kind.ANALYZE) return;

				new ModifyingTreePathScanner(context) {

					@Override
					public Void visitMemberSelect(MemberSelectTree var1, Consumer<JCTree> var2) {
						//process children first
						Void result = super.visitMemberSelect(var1, var2);

						Optional<CRefUsage> maybeRefUsage = isRefCall(getCurrentPath(), context);
						if (maybeRefUsage.isPresent()) {
							Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "Path to ref: " + getCurrentPath());

							CRefUsage refUsage = maybeRefUsage.get();
							if (refUsage instanceof CMethodInv) {
								CMethodInv methodInv = (CMethodInv) refUsage;

								TreeMaker factory = TreeMaker.instance(context);
								Names names = Names.instance(context);


								JCTree.JCExpression[] args = new JCTree.JCExpression[1 + methodInv.arguments.size()];
								args[0] = factory.Literal(new String(methodInv.methodName.toString()));
								for (int i = 1; i < args.length; i++) {
//									Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "i = " + i + ", length = " + args.length);
									args[i] = (JCTree.JCExpression) methodInv.arguments.get(i - 1);
								}

								JCTree.JCMethodInvocation newInvoke = factory.at( ((JCTree) methodInv.originalPath.getLeaf()).pos )
								.Apply(null,
									factory.Select((JCTree.JCExpression) methodInv.expr, names.fromString("invoke")),
									com.sun.tools.javac.util.List.from(args)
								);

								Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "New invoke: " + newInvoke);
							}
						}

						return result;
					}

				}
				//API Note: call scan method instead of Tree.accept to initialize the TreePathScanner
				.scan(taskEvent.getCompilationUnit(), null);

			}
		});
	}

	private static Optional<CRefUsage> isRefCall(TreePath path, Context context) {
		if (path == null) return Optional.empty();
		Tree curr = path.getLeaf();

		//Check for a call to ref(), i.e. there is a MemberSelect and a MethodInvocation
		if (!(curr instanceof MemberSelectTree
			&& ((MemberSelectTree) curr).getIdentifier().contentEquals("ref"))) {
			return Optional.empty();
		}

		ExpressionTree expr = ((MemberSelectTree) curr).getExpression();
		Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "Type of expr: " + ((JCTree.JCExpression) expr).type);

		path = path.getParentPath();
		if (path == null) return Optional.empty();
		curr = path.getLeaf();
		if (!(curr instanceof MethodInvocationTree
			&& ((MethodInvocationTree) curr).getArguments().isEmpty()
			&& ((MethodInvocationTree) curr).getTypeArguments().isEmpty())) {
			return Optional.empty();
		}



		//Test if the ref belongs to a method invocation
		path = path.getParentPath();
		if (path == null) return Optional.empty();
		curr = path.getLeaf();
		if (curr instanceof MemberSelectTree) {
			Name name = ((MemberSelectTree) curr).getIdentifier();

			TreePath methodPath = path.getParentPath();
			if (methodPath == null) return Optional.empty();
			Tree methodCurr = methodPath.getLeaf();

			if (methodCurr instanceof MethodInvocationTree) {
				List<? extends ExpressionTree> args = ((MethodInvocationTree) methodCurr).getArguments();
				Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "Found method: " + expr + "." + name + "(" + args + ")");
				return Optional.of(new CMethodInv(methodPath, expr, name, args));
			}
		}




		return Optional.empty();
	}


	private static interface CRefUsage {
		TreePath getOriginalPath();
	}

	private static class CMethodInv implements CRefUsage {
		private final TreePath originalPath;
		private final ExpressionTree expr;
		private final Name methodName;
		private final List<? extends ExpressionTree> arguments;

		private CMethodInv(TreePath originalPath, ExpressionTree expr, Name methodName, List<? extends ExpressionTree> arguments) {
			this.originalPath = originalPath;
			this.expr = expr;
			this.methodName = methodName;
			this.arguments = arguments;
		}

		@Override
		public TreePath getOriginalPath() {
			return originalPath;
		}
	}


	private static class ModifyingTreePathScanner extends TreePathScanner<Void, Consumer<JCTree>> {

		private final Context context;
		private final TreeMaker factory;

		private ModifyingTreePathScanner(Context context) {
			this.context = context;
			this.factory = TreeMaker.instance(context);
		}


		public Void visitCompilationUnit(CompilationUnitTree var1, Consumer<JCTree> var2) {
			Object var3 = this.scan((Iterable)var1.getPackageAnnotations(), var2);
			var3 = this.scanAndReduce((Tree)var1.getPackageName(), var2, var3);
			var3 = this.scanAndReduce((Iterable)var1.getImports(), var2, var3);
			var3 = this.scanAndReduce((Iterable)var1.getTypeDecls(), var2, var3);
			return var3;
		}

		public Void visitImport(ImportTree var1, Consumer<JCTree> var2) {
			return this.scan(var1.getQualifiedIdentifier(), var2);
		}

		public Void visitClass(ClassTree var1, Consumer<JCTree> var2) {
			Object var3 = this.scan((Tree)var1.getModifiers(), var2);
			var3 = this.scanAndReduce((Iterable)var1.getTypeParameters(), var2, var3);
			var3 = this.scanAndReduce(var1.getExtendsClause(), var2, var3);
			var3 = this.scanAndReduce((Iterable)var1.getImplementsClause(), var2, var3);
			var3 = this.scanAndReduce((Iterable)var1.getMembers(), var2, var3);
			return var3;
		}

		public Void visitMethod(MethodTree var1, Consumer<JCTree> var2) {
			Object var3 = this.scan((Tree)var1.getModifiers(), var2);
			var3 = this.scanAndReduce(var1.getReturnType(), var2, var3);
			var3 = this.scanAndReduce((Iterable)var1.getTypeParameters(), var2, var3);
			var3 = this.scanAndReduce((Iterable)var1.getParameters(), var2, var3);
			var3 = this.scanAndReduce((Tree)var1.getReceiverParameter(), var2, var3);
			var3 = this.scanAndReduce((Iterable)var1.getThrows(), var2, var3);
			var3 = this.scanAndReduce((Tree)var1.getBody(), var2, var3);
			var3 = this.scanAndReduce(var1.getDefaultValue(), var2, var3);
			return var3;
		}

		public Void visitVariable(VariableTree var1, Consumer<JCTree> var2) {
			Object var3 = this.scan((Tree)var1.getModifiers(), var2);
			var3 = this.scanAndReduce(var1.getType(), var2, var3);
			var3 = this.scanAndReduce((Tree)var1.getNameExpression(), var2, var3);
			var3 = this.scanAndReduce((Tree)var1.getInitializer(), var2, var3);
			return var3;
		}

		public Void visitEmptyStatement(EmptyStatementTree var1, Consumer<JCTree> var2) {
			return null;
		}

		public Void visitBlock(BlockTree var1, Consumer<JCTree> var2) {
			return this.scan((Iterable)var1.getStatements(), var2);
		}

		public Void visitDoWhileLoop(DoWhileLoopTree var1, Consumer<JCTree> var2) {
			this.scan((Tree)var1.getStatement(), (newTree) -> ((JCTree.JCDoWhileLoop) var1).body = (JCTree.JCStatement) newTree);
			this.scan((Tree)var1.getCondition(), (newTree) -> ((JCTree.JCDoWhileLoop) var1).cond = (JCTree.JCExpression) newTree);
			return null;
		}

		public Void visitWhileLoop(WhileLoopTree var1, Consumer<JCTree> var2) {
			Object var3 = this.scan((Tree)var1.getCondition(), var2);
			var3 = this.scanAndReduce((Tree)var1.getStatement(), var2, var3);
			return var3;
		}

		public Void visitForLoop(ForLoopTree var1, Consumer<JCTree> var2) {
			Object var3 = this.scan((Iterable)var1.getInitializer(), var2);
			var3 = this.scanAndReduce((Tree)var1.getCondition(), var2, var3);
			var3 = this.scanAndReduce((Iterable)var1.getUpdate(), var2, var3);
			var3 = this.scanAndReduce((Tree)var1.getStatement(), var2, var3);
			return var3;
		}

		public Void visitEnhancedForLoop(EnhancedForLoopTree var1, Consumer<JCTree> var2) {
			Object var3 = this.scan((Tree)var1.getVariable(), var2);
			var3 = this.scanAndReduce((Tree)var1.getExpression(), var2, var3);
			var3 = this.scanAndReduce((Tree)var1.getStatement(), var2, var3);
			return var3;
		}

		public Void visitLabeledStatement(LabeledStatementTree var1, Consumer<JCTree> var2) {
			return this.scan((Tree)var1.getStatement(), var2);
		}

		public Void visitSwitch(SwitchTree var1, Consumer<JCTree> var2) {
			Object var3 = this.scan((Tree)var1.getExpression(), var2);
			var3 = this.scanAndReduce((Iterable)var1.getCases(), var2, var3);
			return var3;
		}

		public Void visitCase(CaseTree var1, Consumer<JCTree> var2) {
			Object var3 = this.scan((Tree)var1.getExpression(), var2);
			var3 = this.scanAndReduce((Iterable)var1.getStatements(), var2, var3);
			return var3;
		}

		public Void visitSynchronized(SynchronizedTree var1, Consumer<JCTree> var2) {
			Object var3 = this.scan((Tree)var1.getExpression(), var2);
			var3 = this.scanAndReduce((Tree)var1.getBlock(), var2, var3);
			return var3;
		}

		public Void visitTry(TryTree var1, Consumer<JCTree> var2) {
			Object var3 = this.scan((Iterable)var1.getResources(), var2);
			var3 = this.scanAndReduce((Tree)var1.getBlock(), var2, var3);
			var3 = this.scanAndReduce((Iterable)var1.getCatches(), var2, var3);
			var3 = this.scanAndReduce((Tree)var1.getFinallyBlock(), var2, var3);
			return var3;
		}

		public Void visitCatch(CatchTree var1, Consumer<JCTree> var2) {
			Object var3 = this.scan((Tree)var1.getParameter(), var2);
			var3 = this.scanAndReduce((Tree)var1.getBlock(), var2, var3);
			return var3;
		}

		public Void visitConditionalExpression(ConditionalExpressionTree var1, Consumer<JCTree> var2) {
			Object var3 = this.scan((Tree)var1.getCondition(), var2);
			var3 = this.scanAndReduce((Tree)var1.getTrueExpression(), var2, var3);
			var3 = this.scanAndReduce((Tree)var1.getFalseExpression(), var2, var3);
			return var3;
		}

		public Void visitIf(IfTree var1, Consumer<JCTree> var2) {
			Object var3 = this.scan((Tree)var1.getCondition(), var2);
			var3 = this.scanAndReduce((Tree)var1.getThenStatement(), var2, var3);
			var3 = this.scanAndReduce((Tree)var1.getElseStatement(), var2, var3);
			return var3;
		}

		public Void visitExpressionStatement(ExpressionStatementTree var1, Consumer<JCTree> var2) {
			return this.scan((Tree)var1.getExpression(), var2);
		}

		public Void visitBreak(BreakTree var1, Consumer<JCTree> var2) {
			return null;
		}

		public Void visitContinue(ContinueTree var1, Consumer<JCTree> var2) {
			return null;
		}

		public Void visitReturn(ReturnTree var1, Consumer<JCTree> var2) {
			return this.scan((Tree)var1.getExpression(), var2);
		}

		public Void visitThrow(ThrowTree var1, Consumer<JCTree> var2) {
			return this.scan((Tree)var1.getExpression(), var2);
		}

		public Void visitAssert(AssertTree var1, Consumer<JCTree> var2) {
			Object var3 = this.scan((Tree)var1.getCondition(), var2);
			var3 = this.scanAndReduce((Tree)var1.getDetail(), var2, var3);
			return var3;
		}

		public Void visitMethodInvocation(MethodInvocationTree var1, Consumer<JCTree> var2) {
			Object var3 = this.scan((Iterable)var1.getTypeArguments(), var2);
			var3 = this.scanAndReduce((Tree)var1.getMethodSelect(), var2, var3);
			var3 = this.scanAndReduce((Iterable)var1.getArguments(), var2, var3);
			return var3;
		}

		public Void visitNewClass(NewClassTree var1, Consumer<JCTree> var2) {
			Object var3 = this.scan((Tree)var1.getEnclosingExpression(), var2);
			var3 = this.scanAndReduce((Tree)var1.getIdentifier(), var2, var3);
			var3 = this.scanAndReduce((Iterable)var1.getTypeArguments(), var2, var3);
			var3 = this.scanAndReduce((Iterable)var1.getArguments(), var2, var3);
			var3 = this.scanAndReduce((Tree)var1.getClassBody(), var2, var3);
			return var3;
		}

		public Void visitNewArray(NewArrayTree var1, Consumer<JCTree> var2) {
			Object var3 = this.scan(var1.getType(), var2);
			var3 = this.scanAndReduce((Iterable)var1.getDimensions(), var2, var3);
			var3 = this.scanAndReduce((Iterable)var1.getInitializers(), var2, var3);
			var3 = this.scanAndReduce((Iterable)var1.getAnnotations(), var2, var3);

			Iterable var5;
			for(Iterator var4 = var1.getDimAnnotations().iterator(); var4.hasNext(); var3 = this.scanAndReduce(var5, var2, var3)) {
				var5 = (Iterable)var4.next();
			}

			return var3;
		}

		public Void visitLambdaExpression(LambdaExpressionTree var1, Consumer<JCTree> var2) {
			Object var3 = this.scan((Iterable)var1.getParameters(), var2);
			var3 = this.scanAndReduce(var1.getBody(), var2, var3);
			return var3;
		}

		public Void visitParenthesized(ParenthesizedTree var1, Consumer<JCTree> var2) {
			return this.scan((Tree)var1.getExpression(), var2);
		}

		public Void visitAssignment(AssignmentTree var1, Consumer<JCTree> var2) {
			this.scan((Tree)var1.getVariable(), var2);
			var3 = this.scanAndReduce((Tree)var1.getExpression(), var2, var3);
			return var3;
		}

		public Void visitCompoundAssignment(CompoundAssignmentTree var1, Consumer<JCTree> var2) {
			Object var3 = this.scan((Tree)var1.getVariable(), var2);
			var3 = this.scanAndReduce((Tree)var1.getExpression(), var2, var3);
			return var3;
		}

		public Void visitUnary(UnaryTree var1, Consumer<JCTree> var2) {
			return this.scan((Tree)var1.getExpression(), var2);
		}

		public Void visitBinary(BinaryTree var1, Consumer<JCTree> var2) {
			Object var3 = this.scan((Tree)var1.getLeftOperand(), var2);
			var3 = this.scanAndReduce((Tree)var1.getRightOperand(), var2, var3);
			return var3;
		}

		public Void visitTypeCast(TypeCastTree var1, Consumer<JCTree> var2) {
			Object var3 = this.scan(var1.getType(), var2);
			var3 = this.scanAndReduce((Tree)var1.getExpression(), var2, var3);
			return var3;
		}

		public Void visitInstanceOf(InstanceOfTree var1, Consumer<JCTree> var2) {
			Object var3 = this.scan((Tree)var1.getExpression(), var2);
			var3 = this.scanAndReduce(var1.getType(), var2, var3);
			return var3;
		}

		public Void visitArrayAccess(ArrayAccessTree var1, Consumer<JCTree> var2) {
			Object var3 = this.scan((Tree)var1.getExpression(), var2);
			var3 = this.scanAndReduce((Tree)var1.getIndex(), var2, var3);
			return var3;
		}

		public Void visitMemberSelect(MemberSelectTree var1, Consumer<JCTree> var2) {
			return this.scan((Tree)var1.getExpression(), var2);
		}

		public Void visitMemberReference(MemberReferenceTree var1, Consumer<JCTree> var2) {
			Object var3 = this.scan((Tree)var1.getQualifierExpression(), var2);
			var3 = this.scanAndReduce((Iterable)var1.getTypeArguments(), var2, var3);
			return var3;
		}

		public Void visitIdentifier(IdentifierTree var1, Consumer<JCTree> var2) {
			return null;
		}

		public Void visitLiteral(LiteralTree var1, Consumer<JCTree> var2) {
			return null;
		}

		public Void visitPrimitiveType(PrimitiveTypeTree var1, Consumer<JCTree> var2) {
			return null;
		}

		public Void visitArrayType(ArrayTypeTree var1, Consumer<JCTree> var2) {
			return this.scan(var1.getType(), var2);
		}

		public Void visitParameterizedType(ParameterizedTypeTree var1, Consumer<JCTree> var2) {
			Object var3 = this.scan(var1.getType(), var2);
			var3 = this.scanAndReduce((Iterable)var1.getTypeArguments(), var2, var3);
			return var3;
		}

		public Void visitUnionType(UnionTypeTree var1, Consumer<JCTree> var2) {
			return this.scan((Iterable)var1.getTypeAlternatives(), var2);
		}

		public Void visitIntersectionType(IntersectionTypeTree var1, Consumer<JCTree> var2) {
			return this.scan((Iterable)var1.getBounds(), var2);
		}

		public Void visitTypeParameter(TypeParameterTree var1, Consumer<JCTree> var2) {
			Object var3 = this.scan((Iterable)var1.getAnnotations(), var2);
			var3 = this.scanAndReduce((Iterable)var1.getBounds(), var2, var3);
			return var3;
		}

		public Void visitWildcard(WildcardTree var1, Consumer<JCTree> var2) {
			return this.scan(var1.getBound(), var2);
		}

		public Void visitModifiers(ModifiersTree var1, Consumer<JCTree> var2) {
			return this.scan((Iterable)var1.getAnnotations(), var2);
		}

		public Void visitAnnotation(AnnotationTree var1, Consumer<JCTree> var2) {
			Object var3 = this.scan(var1.getAnnotationType(), var2);
			var3 = this.scanAndReduce((Iterable)var1.getArguments(), var2, var3);
			return var3;
		}

		public Void visitAnnotatedType(AnnotatedTypeTree var1, Consumer<JCTree> var2) {
			Object var3 = this.scan((Iterable)var1.getAnnotations(), var2);
			var3 = this.scanAndReduce((Tree)var1.getUnderlyingType(), var2, var3);
			return var3;
		}

		public Void visitOther(Tree var1, Consumer<JCTree> var2) {
			return null;
		}

		public Void visitErroneous(ErroneousTree var1, Consumer<JCTree> var2) {
			return null;
		}
	}

//	private static JCTree.JCIf createCheck(VariableTree parameter, Context context) {
//
//		TreeMaker factory = TreeMaker.instance(context);
//		Names symbolsTable = Names.instance(context);
//
//		factory.
//
//		return factory.at(((JCTree) parameter).pos)
//			.If(factory.Parens(createIfCondition(factory, symbolsTable, parameter)),
//				createIfBlock(factory, symbolsTable, parameter),
//				null);
//	}
//
//	private static JCTree.JCBinary createIfCondition(TreeMaker factory,
//													 Names symbolsTable, VariableTree parameter) {
//		Name parameterId = symbolsTable.fromString(parameter.getName().toString());
//		return factory.Binary(JCTree.Tag.LE,
//			factory.Ident(parameterId),
//			factory.Literal(TypeTag.INT, 0));
//	}
//
//	private static JCTree.JCBlock createIfBlock(TreeMaker factory,
//												Names symbolsTable, VariableTree parameter) {
//		String parameterName = parameter.getName().toString();
//		Name parameterId = symbolsTable.fromString(parameterName);
//
//		String errorMessagePrefix = String.format(
//			"Argument '%s' of type %s is marked by @%s but got '",
//			parameterName, parameter.getType(), Positive.class.getSimpleName());
//		String errorMessageSuffix = "' for it";
//
//		return factory.Block(0, com.sun.tools.javac.util.List.of(
//			factory.Throw(
//				factory.NewClass(null, nil(),
//					factory.Ident(symbolsTable.fromString(
//						IllegalArgumentException.class.getSimpleName())),
//					com.sun.tools.javac.util.List.of(factory.Binary(JCTree.Tag.PLUS,
//						factory.Binary(JCTree.Tag.PLUS,
//							factory.Literal(TypeTag.CLASS, errorMessagePrefix),
//							factory.Ident(parameterId)),
//						factory.Literal(TypeTag.CLASS, errorMessageSuffix))), null))));
//	}

}