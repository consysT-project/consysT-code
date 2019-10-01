package de.tuda.stg.consys.compiler;

import com.sun.source.tree.*;
import com.sun.source.util.TreeScanner;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.function.Consumer;

/**
 * Created on 01.10.19.
 *
 * @author Mirko Köhler
 */
class ModifyingTreePathScanner extends TreeScanner<Void, ModifyingTreePathScanner.Modificator> {

	@FunctionalInterface
	public static interface Modificator extends Consumer<JCTree> { }


	/* Use this method to change a single index in a com.sun.tools.javac.util.List */
	@SuppressWarnings("unchecked")
	private static <A> com.sun.tools.javac.util.List<A> setIndex(List<?> list, int index, A value) {
		Object[] asArray = list.toArray();
		asArray[index] = value;
		return com.sun.tools.javac.util.List.from((A[]) asArray);
	}

	private static <A extends JCTree> List<Modificator> getModificators(List<? extends Tree> originalList, Consumer<com.sun.tools.javac.util.List<A>> setter) {
		List<Modificator> mods = new LinkedList<>();
		int i = 0;
		for (Object t : originalList) {
			final int finalI = i;
			mods.add(newTree -> setter.accept(setIndex(originalList, finalI, (A) newTree)));
			i++;
		}
		return mods;
	}
	

	private final Context context;

	private ModifyingTreePath path;

	public ModifyingTreePathScanner(Context context) {
		this.context = context;
	}


	protected Void scan(Iterable<? extends Tree> trees, Iterable<Modificator> mods) {
		if (trees != null) {
			Iterator<? extends Tree> treeIt = trees.iterator();
			Iterator<Modificator> modIt = mods.iterator();

			while (treeIt.hasNext() && modIt.hasNext()) {
				Tree tree = treeIt.next();
				Modificator mod = modIt.next();
				scan(tree, mod);
			}
		}
		return null;
	}


	@Override
	public Void scan(Tree tree, Modificator mod) {
		if (tree == null) {
			return null;
		} else {
			ModifyingTreePath oldPath = this.path;
			this.path = new ModifyingTreePath(this.path, tree, mod);

			try {
				tree.accept(this, mod);
			} finally {
				this.path = oldPath;
			}
			return null;
		}
	}

	public ModifyingTreePath getCurrentPath() {
		return this.path;
	}


	public Void visitCompilationUnit(CompilationUnitTree var1, Modificator var2) {
		scan(var1.getPackageAnnotations(), ModifyingTreePathScanner.<JCTree.JCAnnotation>getModificators(var1.getPackageAnnotations(), l -> ((JCTree.JCCompilationUnit) var1).packageAnnotations = l));
		scan(var1.getPackageName(), newTree -> ((JCTree.JCCompilationUnit) var1).pid = (JCTree.JCExpression) newTree);
		scan(var1.getImports(), ModifyingTreePathScanner.<JCTree.JCAnnotation>getModificators(var1.getPackageAnnotations(), l -> { throw new UnsupportedOperationException("can not modify imports"); }));
		scan(var1.getTypeDecls(), ModifyingTreePathScanner.<JCTree.JCExpression>getModificators(
			var1.getTypeDecls(), newTree -> { throw new UnsupportedOperationException("can not modify types"); }));
		return null;
	}

	public Void visitImport(ImportTree var1, Modificator var2) {
		scan(var1.getQualifiedIdentifier(),  l -> { throw new UnsupportedOperationException("can not modify imports"); });
		return null;
	}

	public Void visitClass(ClassTree var1, Modificator var2) {
		scan(var1.getModifiers(), l -> ((JCTree.JCClassDecl) var1).mods = (JCTree.JCModifiers) l);
		scan(var1.getTypeParameters(), ModifyingTreePathScanner.<JCTree.JCExpression>getModificators(
			var1.getTypeParameters(), newTree -> { throw new UnsupportedOperationException("can not modify types"); }));
		scan(var1.getExtendsClause(), newTree -> { throw new UnsupportedOperationException("can not modify types"); });
		scan(var1.getImplementsClause(), ModifyingTreePathScanner.<JCTree.JCExpression>getModificators(
			var1.getImplementsClause(), newTree -> { throw new UnsupportedOperationException("can not modify types"); }));
		scan(var1.getMembers(), ModifyingTreePathScanner.<JCTree.JCExpression>getModificators(
			var1.getMembers(), newTree -> { throw new UnsupportedOperationException("can not modify members"); }));
		return null;
	}

	public Void visitMethod(MethodTree var1, Modificator var2) {
		scan(var1.getModifiers(), l -> ((JCTree.JCMethodDecl) var1).mods = (JCTree.JCModifiers) l);
		scan(var1.getReturnType(), newTree -> { throw new UnsupportedOperationException("can not modify types"); });
		scan(var1.getTypeParameters(), ModifyingTreePathScanner.<JCTree.JCExpression>getModificators(
			var1.getTypeParameters(), newTree -> { throw new UnsupportedOperationException("can not modify types"); }));
		scan(var1.getParameters(), ModifyingTreePathScanner.<JCTree.JCVariableDecl>getModificators(var1.getParameters(), l -> ((JCTree.JCMethodDecl) var1).params = l));
		scan(var1.getReceiverParameter(), l -> ((JCTree.JCMethodDecl) var1).recvparam = (JCTree.JCVariableDecl) l);
		scan(var1.getThrows(), ModifyingTreePathScanner.<JCTree.JCExpression>getModificators(var1.getThrows(), l -> ((JCTree.JCMethodDecl) var1).thrown = l));
		scan(var1.getBody(), l -> ((JCTree.JCMethodDecl) var1).body = (JCTree.JCBlock) l);
		scan(var1.getDefaultValue(), l -> ((JCTree.JCMethodDecl) var1).defaultValue = (JCTree.JCExpression) l);
		return null;
	}

	public Void visitVariable(VariableTree var1, Modificator var2) {
		scan(var1.getModifiers(), newTree -> ((JCTree.JCVariableDecl) var1).mods = (JCTree.JCModifiers) newTree);
		scan(var1.getType(), newTree -> {
			throw new UnsupportedOperationException("can not modify types");
			/*((JCTree.JCVariableDecl) var1).type = (com.sun.tools.javac.code.Type) newTree */
		});
		scan(var1.getNameExpression(), newTree -> ((JCTree.JCVariableDecl) var1).nameexpr = (JCTree.JCExpression) newTree);
		scan(var1.getInitializer(), newTree -> ((JCTree.JCVariableDecl) var1).init = (JCTree.JCExpression) newTree);
		return null;
	}

	public Void visitEmptyStatement(EmptyStatementTree var1, Modificator var2) {
		return null;
	}

	public Void visitBlock(BlockTree var1, Modificator var2) {
		scan(
			var1.getStatements(),
			ModifyingTreePathScanner.<JCTree.JCStatement>getModificators(var1.getStatements(), l -> ((JCTree.JCBlock) var1).stats = l)
		);
		return null;
	}

	public Void visitDoWhileLoop(DoWhileLoopTree var1, Modificator var2) {
		scan(var1.getStatement(), newTree -> ((JCTree.JCDoWhileLoop) var1).body = (JCTree.JCStatement) newTree);
		scan(var1.getCondition(), newTree -> ((JCTree.JCDoWhileLoop) var1).cond = (JCTree.JCExpression) newTree);
		return null;
	}

	public Void visitWhileLoop(WhileLoopTree var1, Modificator var2) {
		scan(var1.getCondition(), newTree -> ((JCTree.JCWhileLoop) var1).cond = (JCTree.JCExpression) newTree);
		scan(var1.getStatement(), newTree -> ((JCTree.JCDoWhileLoop) var1).body = (JCTree.JCStatement) newTree);
		return null;
	}

	public Void visitForLoop(ForLoopTree tree, Modificator mod) {
		scan(tree.getInitializer(), ModifyingTreePathScanner.<JCTree.JCStatement>getModificators(tree.getInitializer(), l -> ((JCTree.JCForLoop) tree).init = l));
		scan(tree.getCondition(), newTree -> ((JCTree.JCForLoop) tree).cond = (JCTree.JCExpression) newTree);
		scan(tree.getUpdate(), ModifyingTreePathScanner.<JCTree.JCExpressionStatement>getModificators(tree.getUpdate(), l -> ((JCTree.JCForLoop) tree).step = l));
		scan(tree.getStatement(), newTree -> ((JCTree.JCForLoop) tree).body = (JCTree.JCStatement) newTree);
		return null;
	}

	public Void visitEnhancedForLoop(EnhancedForLoopTree var1, Modificator var2) {
		scan(var1.getVariable(), newTree -> ((JCTree.JCEnhancedForLoop) var1).var = (JCTree.JCVariableDecl) newTree);
		scan(var1.getExpression(), newTree -> ((JCTree.JCEnhancedForLoop) var1).expr = (JCTree.JCExpression) newTree);
		scan(var1.getStatement(), newTree -> ((JCTree.JCEnhancedForLoop) var1).body = (JCTree.JCStatement) newTree);
		return null;
	}

	public Void visitLabeledStatement(LabeledStatementTree var1, Modificator var2) {
		return this.scan((Tree) var1.getStatement(), var2);
	}

	public Void visitSwitch(SwitchTree var1, Modificator var2) {
		scan(var1.getExpression(), newTree -> ((JCTree.JCSwitch) var1).selector = (JCTree.JCExpression) newTree);
		scan(var1.getCases(), ModifyingTreePathScanner.<JCTree.JCCase>getModificators(var1.getCases(), l -> ((JCTree.JCSwitch) var1).cases = l));
		return null;
	}

	public Void visitCase(CaseTree var1, Modificator var2) {
		scan(var1.getExpression(), newTree -> ((JCTree.JCCase) var1).pat = (JCTree.JCExpression) newTree);
		scan(var1.getStatements(), ModifyingTreePathScanner.<JCTree.JCStatement>getModificators(var1.getStatements(), l -> ((JCTree.JCCase) var1).stats = l));
		return null;
	}

	public Void visitSynchronized(SynchronizedTree var1, Modificator var2) {
		scan(var1.getExpression(), newTree -> ((JCTree.JCSynchronized) var1).lock = (JCTree.JCExpression) newTree);
		scan(var1.getBlock(), newTree -> ((JCTree.JCSynchronized) var1).body = (JCTree.JCBlock) newTree);
		return null;
	}

	public Void visitTry(TryTree var1, Modificator var2) {
		scan(var1.getResources(), ModifyingTreePathScanner.<JCTree>getModificators(var1.getResources(), l -> ((JCTree.JCTry) var1).resources = l));
		scan(var1.getBlock(), newTree -> ((JCTree.JCTry) var1).body = (JCTree.JCBlock) newTree);
		scan(var1.getCatches(), ModifyingTreePathScanner.<JCTree.JCCatch>getModificators(var1.getCatches(), l -> ((JCTree.JCTry) var1).catchers = l));
		scan(var1.getFinallyBlock(), newTree -> ((JCTree.JCTry) var1).finalizer = (JCTree.JCBlock) newTree);
		return null;
	}

	public Void visitCatch(CatchTree var1, Modificator var2) {
		scan(var1.getParameter(), newTree -> ((JCTree.JCCatch) var1).param = (JCTree.JCVariableDecl) newTree);
		scan(var1.getBlock(), newTree -> ((JCTree.JCCatch) var1).body = (JCTree.JCBlock) newTree);
		return null;
	}

	public Void visitConditionalExpression(ConditionalExpressionTree var1, Modificator var2) {
		scan(var1.getCondition(), newTree -> ((JCTree.JCConditional) var1).cond = (JCTree.JCExpression) newTree);
		scan(var1.getTrueExpression(), newTree -> ((JCTree.JCConditional) var1).truepart = (JCTree.JCExpression) newTree);
		scan(var1.getFalseExpression(), newTree -> ((JCTree.JCConditional) var1).falsepart = (JCTree.JCExpression) newTree);
		return null;
	}

	public Void visitIf(IfTree var1, Modificator var2) {
		scan(var1.getCondition(), newTree -> ((JCTree.JCIf) var1).cond = (JCTree.JCExpression) newTree);
		scan(var1.getThenStatement(), newTree -> ((JCTree.JCIf) var1).thenpart = (JCTree.JCBlock) newTree);
		scan(var1.getElseStatement(), newTree -> ((JCTree.JCIf) var1).elsepart = (JCTree.JCBlock) newTree);
		return null;
	}

	public Void visitExpressionStatement(ExpressionStatementTree var1, Modificator var2) {
		scan(var1.getExpression(), newTree ->
			((JCTree.JCExpressionStatement) var1).expr = (JCTree.JCExpression) newTree
		);
		return null;
	}

	public Void visitBreak(BreakTree var1, Modificator var2) {
		return null;
	}

	public Void visitContinue(ContinueTree var1, Modificator var2) {
		return null;
	}

	public Void visitReturn(ReturnTree var1, Modificator var2) {
		scan(var1.getExpression(), newTree -> ((JCTree.JCReturn) var1).expr = (JCTree.JCExpression) newTree);
		return null;
	}

	public Void visitThrow(ThrowTree var1, Modificator var2) {
		scan(var1.getExpression(), newTree -> ((JCTree.JCThrow) var1).expr = (JCTree.JCExpression) newTree);
		return null;
	}

	public Void visitAssert(AssertTree var1, Modificator var2) {
		scan(var1.getCondition(), newTree -> ((JCTree.JCAssert) var1).cond = (JCTree.JCExpression) newTree);
		scan(var1.getDetail(), newTree -> ((JCTree.JCAssert) var1).detail = (JCTree.JCExpression) newTree);
		return null;
	}

	public Void visitMethodInvocation(MethodInvocationTree var1, Modificator var2) {
		scan(var1.getTypeArguments(), ModifyingTreePathScanner.<JCTree.JCExpression>getModificators(var1.getTypeArguments(), l -> ((JCTree.JCMethodInvocation) var1).typeargs = l));
		scan(var1.getMethodSelect(), newTree -> ((JCTree.JCMethodInvocation) var1).meth = (JCTree.JCExpression) newTree);
		scan(var1.getArguments(), ModifyingTreePathScanner.<JCTree.JCExpression>getModificators(var1.getArguments(), l -> ((JCTree.JCMethodInvocation) var1).args = l));
		return null;
	}

	public Void visitNewClass(NewClassTree var1, Modificator var2) {
		scan(var1.getEnclosingExpression(), newTree -> ((JCTree.JCNewClass) var1).encl = (JCTree.JCExpression) newTree);
		scan(var1.getIdentifier(), newTree -> ((JCTree.JCNewClass) var1).clazz = (JCTree.JCExpression) newTree);
		scan(var1.getTypeArguments(), ModifyingTreePathScanner.<JCTree.JCExpression>getModificators(
			var1.getTypeArguments(), newTree -> { throw new UnsupportedOperationException("can not modify types"); }));
		scan(var1.getArguments(), ModifyingTreePathScanner.<JCTree.JCExpression>getModificators(var1.getArguments(), l -> ((JCTree.JCMethodInvocation) var1).args = l));
		scan(var1.getClassBody(), newTree -> ((JCTree.JCNewClass) var1).def = (JCTree.JCClassDecl) newTree);
		return null;
	}

	public Void visitNewArray(NewArrayTree var1, Modificator var2) {
		scan(var1.getType(), newTree -> { throw new UnsupportedOperationException("can not modify types"); });
		scan(var1.getDimensions(), ModifyingTreePathScanner.<JCTree.JCExpression>getModificators(var1.getDimensions(), l -> ((JCTree.JCNewArray) var1).dims = l));
		scan(var1.getInitializers(), ModifyingTreePathScanner.<JCTree.JCExpression>getModificators(var1.getInitializers(), l -> ((JCTree.JCNewArray) var1).elems = l));
		scan(var1.getAnnotations(), ModifyingTreePathScanner.<JCTree.JCAnnotation>getModificators(var1.getAnnotations(), l -> ((JCTree.JCNewArray) var1).annotations = l));


		//TODO: Implement multi dimension array
//		Iterable<? extends AnnotationTree> annotationTrees;
//		for(
//			Iterator<? extends List<? extends AnnotationTree>> treesIt = var1.getDimAnnotations().iterator();
//			treesIt.hasNext();
//			scan(annotationTrees, ModifyingTreePathScanner.<JCTree.JCAnnotation>getModificators(annotationTrees, l -> { throw new UnsupportedOperationException("can not modify inner array dims"); }))
//		) {
//			annotationTrees = treesIt.next();
//		}

		return null;
	}

	public Void visitLambdaExpression(LambdaExpressionTree var1, Modificator var2) {
		scan(var1.getParameters(), ModifyingTreePathScanner.<JCTree.JCVariableDecl>getModificators(var1.getParameters(), l -> ((JCTree.JCLambda) var1).params = l));
		scan(var1.getBody(), newTree -> ((JCTree.JCLambda) var1).body = (JCTree.JCExpression) newTree);
		return null;
	}

	public Void visitParenthesized(ParenthesizedTree var1, Modificator var2) {
		scan(var1.getExpression(), newTree -> ((JCTree.JCParens) var1).expr = (JCTree.JCExpression) newTree);
		return null;
	}

	public Void visitAssignment(AssignmentTree var1, Modificator var2) {
		scan(var1.getExpression(), newTree -> ((JCTree.JCAssign) var1).rhs = (JCTree.JCExpression) newTree);
		scan(var1.getVariable(), newTree -> ((JCTree.JCAssign) var1).lhs = (JCTree.JCExpression) newTree);
		return null;
	}

	public Void visitCompoundAssignment(CompoundAssignmentTree var1, Modificator var2) {
		scan(var1.getVariable(), newTree -> ((JCTree.JCAssignOp) var1).lhs = (JCTree.JCExpression) newTree);
		scan(var1.getExpression(), newTree -> ((JCTree.JCAssignOp) var1).rhs = (JCTree.JCExpression) newTree);
		return null;
	}

	public Void visitUnary(UnaryTree var1, Modificator var2) {
		scan(var1.getExpression(), newTree -> ((JCTree.JCUnary) var1).arg = (JCTree.JCExpression) newTree);
		return null;
	}

	public Void visitBinary(BinaryTree var1, Modificator var2) {
		scan(var1.getLeftOperand(), newTree -> ((JCTree.JCBinary) var1).lhs = (JCTree.JCExpression) newTree);
		scan(var1.getRightOperand(), newTree -> ((JCTree.JCBinary) var1).rhs = (JCTree.JCExpression) newTree);
		return null;
	}

	public Void visitTypeCast(TypeCastTree var1, Modificator var2) {
		scan(var1.getType(), newTree -> { throw new UnsupportedOperationException("can not modify types"); });
		scan(var1.getExpression(), newTree -> ((JCTree.JCTypeCast) var1).expr = (JCTree.JCExpression) newTree);
		return null;
	}

	public Void visitInstanceOf(InstanceOfTree var1, Modificator var2) {
		scan(var1.getExpression(), newTree -> ((JCTree.JCInstanceOf) var1).expr = (JCTree.JCExpression) newTree);
		scan(var1.getType(), newTree -> { throw new UnsupportedOperationException("can not modify types"); });
		return null;
	}

	public Void visitArrayAccess(ArrayAccessTree var1, Modificator var2) {
		scan(var1.getExpression(), newTree -> ((JCTree.JCArrayAccess) var1).indexed = (JCTree.JCExpression) newTree);
		scan(var1.getIndex(), newTree -> ((JCTree.JCArrayAccess) var1).index = (JCTree.JCExpression) newTree);
		return null;
	}

	public Void visitMemberSelect(MemberSelectTree var1, Modificator var2) {
		scan(var1.getExpression(), newTree -> ((JCTree.JCFieldAccess) var1).selected = (JCTree.JCExpression) newTree);
		return null;
	}

	public Void visitMemberReference(MemberReferenceTree var1, Modificator var2) {
		scan(var1.getQualifierExpression(), newTree -> ((JCTree.JCMemberReference) var1).expr = (JCTree.JCExpression) newTree);
		scan(var1.getTypeArguments(), ModifyingTreePathScanner.<JCTree.JCAnnotation>getModificators(var1.getTypeArguments(), l -> { throw new UnsupportedOperationException("can not modify types"); }));
		return null;
	}

	public Void visitIdentifier(IdentifierTree var1, Modificator var2) {
		return null;
	}

	public Void visitLiteral(LiteralTree var1, Modificator var2) {
		return null;
	}

	public Void visitPrimitiveType(PrimitiveTypeTree var1, Modificator var2) {
		return null;
	}

	public Void visitArrayType(ArrayTypeTree var1, Modificator var2) {
		scan(var1.getType(), newTree -> { throw new UnsupportedOperationException("can not modify types"); });
		return null;
	}

	public Void visitParameterizedType(ParameterizedTypeTree var1, Modificator var2) {
		scan(var1.getType(), newTree -> { throw new UnsupportedOperationException("can not modify types"); });
		scan(var1.getTypeArguments(), ModifyingTreePathScanner.<JCTree.JCAnnotation>getModificators(var1.getTypeArguments(), l -> { throw new UnsupportedOperationException("can not modify types"); }));
		return null;
	}

	public Void visitUnionType(UnionTypeTree var1, Modificator var2) {
		scan(var1.getTypeAlternatives(), ModifyingTreePathScanner.<JCTree.JCAnnotation>getModificators(var1.getTypeAlternatives(), l -> { throw new UnsupportedOperationException("can not modify types"); }));
		return null;
	}

	public Void visitIntersectionType(IntersectionTypeTree var1, Modificator var2) {
		scan(var1.getBounds(), ModifyingTreePathScanner.<JCTree.JCAnnotation>getModificators(var1.getBounds(), l -> { throw new UnsupportedOperationException("can not modify types"); }));
		return null;
	}

	public Void visitTypeParameter(TypeParameterTree var1, Modificator var2) {
		scan(var1.getAnnotations(), ModifyingTreePathScanner.<JCTree.JCAnnotation>getModificators(var1.getAnnotations(), l -> { throw new UnsupportedOperationException("can not modify types"); }));
		scan(var1.getBounds(), ModifyingTreePathScanner.<JCTree.JCAnnotation>getModificators(var1.getBounds(), l -> { throw new UnsupportedOperationException("can not modify types"); }));
		return null;
	}

	public Void visitWildcard(WildcardTree var1, Modificator var2) {
		scan(var1.getBound(), newTree -> { throw new UnsupportedOperationException("can not modify types"); });
		return null;
	}

	public Void visitModifiers(ModifiersTree var1, Modificator var2) {
		scan(var1.getAnnotations(), ModifyingTreePathScanner.<JCTree.JCAnnotation>getModificators(var1.getAnnotations(), l -> ((JCTree.JCModifiers) var1).annotations = l));
		return null;
	}

	public Void visitAnnotation(AnnotationTree var1, Modificator var2) {
		scan(var1.getAnnotationType(), newTree -> ((JCTree.JCAnnotation) var1).annotationType = (JCTree) newTree);
		scan(var1.getArguments(), ModifyingTreePathScanner.<JCTree.JCExpression>getModificators(var1.getArguments(), l -> ((JCTree.JCAnnotation) var1).args = l));
		return null;
	}

	public Void visitAnnotatedType(AnnotatedTypeTree var1, Modificator var2) {
		scan(var1.getAnnotations(), ModifyingTreePathScanner.<JCTree.JCAnnotation>getModificators(var1.getAnnotations(), l -> ((JCTree.JCAnnotatedType) var1).annotations = l));
		scan(var1.getUnderlyingType(), newTree -> ((JCTree.JCAnnotatedType) var1).underlyingType = (JCTree.JCExpression) newTree);
		return null;
	}

	public Void visitOther(Tree var1, Modificator var2) {
		return null;
	}

	public Void visitErroneous(ErroneousTree var1, Modificator var2) {
		return null;
	}
}
