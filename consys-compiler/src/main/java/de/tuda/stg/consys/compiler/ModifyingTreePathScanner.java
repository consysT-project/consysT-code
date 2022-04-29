package de.tuda.stg.consys.compiler;

import com.sun.source.tree.*;
import com.sun.source.util.TreeScanner;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;

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
	public interface Modificator extends Consumer<JCTree> { }


	/* Use this method to change a single index in a com.sun.tools.javac.util.List */
	@SuppressWarnings("unchecked")
	private static <A> com.sun.tools.javac.util.List<A> setIndex(List<?> list, int index, A value) {
		Object[] asArray = list.toArray();
		asArray[index] = value;
		return com.sun.tools.javac.util.List.from((A[]) asArray);
	}

	private static <A extends JCTree> List<Modificator> getModificators(List<? extends Tree> originalList, Consumer<com.sun.tools.javac.util.List<A>> setter) {
		List<Modificator> mods = new LinkedList<>();
		if (originalList == null) return mods;

		int i = 0;
		for (Object t : originalList) {
			final int finalI = i;
			mods.add(newTree -> setter.accept((com.sun.tools.javac.util.List<A>) setIndex(originalList, finalI, newTree)));
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

	@Override
	public Void visitCompilationUnit(CompilationUnitTree tree, Modificator modificator) {
		scan(tree.getPackageAnnotations(), ModifyingTreePathScanner.<JCTree.JCAnnotation>getModificators(tree.getPackageAnnotations(), l -> { throw new UnsupportedOperationException("can not modify package annotations"); }));
		scan(tree.getPackageName(), newTree -> { throw new UnsupportedOperationException("can not modify package name"); });
		scan(tree.getImports(), ModifyingTreePathScanner.<JCTree.JCAnnotation>getModificators(tree.getPackageAnnotations(), l -> { throw new UnsupportedOperationException("can not modify imports"); }));
		scan(tree.getTypeDecls(), ModifyingTreePathScanner.<JCTree.JCExpression>getModificators(
			tree.getTypeDecls(), newTree -> { throw new UnsupportedOperationException("can not modify types"); }));
		return null;
	}

	@Override
	public Void visitImport(ImportTree tree, Modificator modificator) {
		scan(tree.getQualifiedIdentifier(),  l -> { throw new UnsupportedOperationException("can not modify imports"); });
		return null;
	}

	@Override
	public Void visitClass(ClassTree tree, Modificator modificator) {
		scan(tree.getModifiers(), l -> ((JCTree.JCClassDecl) tree).mods = (JCTree.JCModifiers) l);
		scan(tree.getTypeParameters(), ModifyingTreePathScanner.<JCTree.JCExpression>getModificators(
			tree.getTypeParameters(), newTree -> { throw new UnsupportedOperationException("can not modify types"); }));
		scan(tree.getExtendsClause(), newTree -> { throw new UnsupportedOperationException("can not modify types"); });
		scan(tree.getImplementsClause(), ModifyingTreePathScanner.<JCTree.JCExpression>getModificators(
			tree.getImplementsClause(), newTree -> { throw new UnsupportedOperationException("can not modify types"); }));
		scan(tree.getMembers(), ModifyingTreePathScanner.<JCTree.JCExpression>getModificators(
			tree.getMembers(), newTree -> { throw new UnsupportedOperationException("can not modify members"); }));
		return null;
	}

	@Override
	public Void visitMethod(MethodTree tree, Modificator modificator) {
		scan(tree.getModifiers(), l -> ((JCTree.JCMethodDecl) tree).mods = (JCTree.JCModifiers) l);
		scan(tree.getReturnType(), newTree -> { throw new UnsupportedOperationException("can not modify types"); });
		scan(tree.getTypeParameters(), ModifyingTreePathScanner.<JCTree.JCExpression>getModificators(
			tree.getTypeParameters(), newTree -> { throw new UnsupportedOperationException("can not modify types"); }));
		scan(tree.getParameters(), ModifyingTreePathScanner.<JCTree.JCVariableDecl>getModificators(tree.getParameters(), l -> ((JCTree.JCMethodDecl) tree).params = l));
		scan(tree.getReceiverParameter(), l -> ((JCTree.JCMethodDecl) tree).recvparam = (JCTree.JCVariableDecl) l);
		scan(tree.getThrows(), ModifyingTreePathScanner.<JCTree.JCExpression>getModificators(tree.getThrows(), l -> ((JCTree.JCMethodDecl) tree).thrown = l));
		scan(tree.getBody(), l -> ((JCTree.JCMethodDecl) tree).body = (JCTree.JCBlock) l);
		scan(tree.getDefaultValue(), l -> ((JCTree.JCMethodDecl) tree).defaultValue = (JCTree.JCExpression) l);
		return null;
	}

	@Override
	public Void visitVariable(VariableTree tree, Modificator modificator) {
		scan(tree.getModifiers(), newTree -> ((JCTree.JCVariableDecl) tree).mods = (JCTree.JCModifiers) newTree);
		scan(tree.getType(), newTree -> {
			throw new UnsupportedOperationException("can not modify types");
			/*((JCTree.JCVariableDecl) tree).type = (com.sun.tools.javac.code.Type) newTree */
		});
		scan(tree.getNameExpression(), newTree -> ((JCTree.JCVariableDecl) tree).nameexpr = (JCTree.JCExpression) newTree);
		scan(tree.getInitializer(), newTree -> ((JCTree.JCVariableDecl) tree).init = (JCTree.JCExpression) newTree);
		return null;
	}

	@Override
	public Void visitEmptyStatement(EmptyStatementTree tree, Modificator modificator) {
		return null;
	}

	@Override
	public Void visitBlock(BlockTree tree, Modificator modificator) {
		scan(
			tree.getStatements(),
			ModifyingTreePathScanner.<JCTree.JCStatement>getModificators(tree.getStatements(), l -> ((JCTree.JCBlock) tree).stats = l)
		);
		return null;
	}

	@Override
	public Void visitDoWhileLoop(DoWhileLoopTree tree, Modificator modificator) {
		scan(tree.getStatement(), newTree -> ((JCTree.JCDoWhileLoop) tree).body = (JCTree.JCStatement) newTree);
		scan(tree.getCondition(), newTree -> ((JCTree.JCDoWhileLoop) tree).cond = (JCTree.JCExpression) newTree);
		return null;
	}

	@Override
	public Void visitWhileLoop(WhileLoopTree tree, Modificator modificator) {
		scan(tree.getCondition(), newTree -> ((JCTree.JCWhileLoop) tree).cond = (JCTree.JCExpression) newTree);
		scan(tree.getStatement(), newTree -> ((JCTree.JCDoWhileLoop) tree).body = (JCTree.JCStatement) newTree);
		return null;
	}

	@Override
	public Void visitForLoop(ForLoopTree tree, Modificator mod) {
		scan(tree.getInitializer(), ModifyingTreePathScanner.<JCTree.JCStatement>getModificators(tree.getInitializer(), l -> ((JCTree.JCForLoop) tree).init = l));
		scan(tree.getCondition(), newTree -> ((JCTree.JCForLoop) tree).cond = (JCTree.JCExpression) newTree);
		scan(tree.getUpdate(), ModifyingTreePathScanner.<JCTree.JCExpressionStatement>getModificators(tree.getUpdate(), l -> ((JCTree.JCForLoop) tree).step = l));
		scan(tree.getStatement(), newTree -> ((JCTree.JCForLoop) tree).body = (JCTree.JCStatement) newTree);
		return null;
	}

	@Override
	public Void visitEnhancedForLoop(EnhancedForLoopTree tree, Modificator modificator) {
		scan(tree.getVariable(), newTree -> ((JCTree.JCEnhancedForLoop) tree).var = (JCTree.JCVariableDecl) newTree);
		scan(tree.getExpression(), newTree -> ((JCTree.JCEnhancedForLoop) tree).expr = (JCTree.JCExpression) newTree);
		scan(tree.getStatement(), newTree -> ((JCTree.JCEnhancedForLoop) tree).body = (JCTree.JCStatement) newTree);
		return null;
	}

	@Override
	public Void visitLabeledStatement(LabeledStatementTree tree, Modificator modificator) {
		return this.scan(tree.getStatement(), modificator);
	}

	@Override
	public Void visitSwitch(SwitchTree tree, Modificator modificator) {
		scan(tree.getExpression(), newTree -> ((JCTree.JCSwitch) tree).selector = (JCTree.JCExpression) newTree);
		scan(tree.getCases(), ModifyingTreePathScanner.<JCTree.JCCase>getModificators(tree.getCases(), l -> ((JCTree.JCSwitch) tree).cases = l));
		return null;
	}

	@Override
	public Void visitCase(CaseTree tree, Modificator modificator) {
		scan(tree.getExpression(), newTree -> ((JCTree.JCCase) tree).pat = (JCTree.JCExpression) newTree);
		scan(tree.getStatements(), ModifyingTreePathScanner.<JCTree.JCStatement>getModificators(tree.getStatements(), l -> ((JCTree.JCCase) tree).stats = l));
		return null;
	}

	@Override
	public Void visitSynchronized(SynchronizedTree tree, Modificator modificator) {
		scan(tree.getExpression(), newTree -> ((JCTree.JCSynchronized) tree).lock = (JCTree.JCExpression) newTree);
		scan(tree.getBlock(), newTree -> ((JCTree.JCSynchronized) tree).body = (JCTree.JCBlock) newTree);
		return null;
	}

	@Override
	public Void visitTry(TryTree tree, Modificator modificator) {
		scan(tree.getResources(), ModifyingTreePathScanner.getModificators(tree.getResources(), l -> ((JCTree.JCTry) tree).resources = l));
		scan(tree.getBlock(), newTree -> ((JCTree.JCTry) tree).body = (JCTree.JCBlock) newTree);
		scan(tree.getCatches(), ModifyingTreePathScanner.<JCTree.JCCatch>getModificators(tree.getCatches(), l -> ((JCTree.JCTry) tree).catchers = l));
		scan(tree.getFinallyBlock(), newTree -> ((JCTree.JCTry) tree).finalizer = (JCTree.JCBlock) newTree);
		return null;
	}

	@Override
	public Void visitCatch(CatchTree tree, Modificator modificator) {
		scan(tree.getParameter(), newTree -> ((JCTree.JCCatch) tree).param = (JCTree.JCVariableDecl) newTree);
		scan(tree.getBlock(), newTree -> ((JCTree.JCCatch) tree).body = (JCTree.JCBlock) newTree);
		return null;
	}

	@Override
	public Void visitConditionalExpression(ConditionalExpressionTree tree, Modificator modificator) {
		scan(tree.getCondition(), newTree -> ((JCTree.JCConditional) tree).cond = (JCTree.JCExpression) newTree);
		scan(tree.getTrueExpression(), newTree -> ((JCTree.JCConditional) tree).truepart = (JCTree.JCExpression) newTree);
		scan(tree.getFalseExpression(), newTree -> ((JCTree.JCConditional) tree).falsepart = (JCTree.JCExpression) newTree);
		return null;
	}

	@Override
	public Void visitIf(IfTree tree, Modificator modificator) {
		scan(tree.getCondition(), newTree -> ((JCTree.JCIf) tree).cond = (JCTree.JCExpression) newTree);
		scan(tree.getThenStatement(), newTree -> ((JCTree.JCIf) tree).thenpart = (JCTree.JCBlock) newTree);
		scan(tree.getElseStatement(), newTree -> ((JCTree.JCIf) tree).elsepart = (JCTree.JCBlock) newTree);
		return null;
	}

	@Override
	public Void visitExpressionStatement(ExpressionStatementTree tree, Modificator modificator) {
		scan(tree.getExpression(), newTree ->
			((JCTree.JCExpressionStatement) tree).expr = (JCTree.JCExpression) newTree
		);
		return null;
	}

	@Override
	public Void visitBreak(BreakTree tree, Modificator modificator) {
		return null;
	}

	@Override
	public Void visitContinue(ContinueTree tree, Modificator modificator) {
		return null;
	}

	@Override
	public Void visitReturn(ReturnTree tree, Modificator modificator) {
		scan(tree.getExpression(), newTree -> ((JCTree.JCReturn) tree).expr = (JCTree.JCExpression) newTree);
		return null;
	}

	@Override
	public Void visitThrow(ThrowTree tree, Modificator modificator) {
		scan(tree.getExpression(), newTree -> ((JCTree.JCThrow) tree).expr = (JCTree.JCExpression) newTree);
		return null;
	}

	@Override
	public Void visitAssert(AssertTree tree, Modificator modificator) {
		scan(tree.getCondition(), newTree -> ((JCTree.JCAssert) tree).cond = (JCTree.JCExpression) newTree);
		scan(tree.getDetail(), newTree -> ((JCTree.JCAssert) tree).detail = (JCTree.JCExpression) newTree);
		return null;
	}

	@Override
	public Void visitMethodInvocation(MethodInvocationTree tree, Modificator modificator) {
		scan(tree.getTypeArguments(), ModifyingTreePathScanner.<JCTree.JCExpression>getModificators(tree.getTypeArguments(), l -> ((JCTree.JCMethodInvocation) tree).typeargs = l));
		// scan arguments before method-select, so that ref calls inside other ref calls get transformed
		scan(tree.getArguments(), ModifyingTreePathScanner.<JCTree.JCExpression>getModificators(tree.getArguments(), l -> ((JCTree.JCMethodInvocation) tree).args = l));
		scan(tree.getMethodSelect(), newTree -> ((JCTree.JCMethodInvocation) tree).meth = (JCTree.JCExpression) newTree);
		return null;
	}

	@Override
	public Void visitNewClass(NewClassTree tree, Modificator modificator) {
		scan(tree.getEnclosingExpression(), newTree -> ((JCTree.JCNewClass) tree).encl = (JCTree.JCExpression) newTree);
		scan(tree.getIdentifier(), newTree -> ((JCTree.JCNewClass) tree).clazz = (JCTree.JCExpression) newTree);
		scan(tree.getTypeArguments(), ModifyingTreePathScanner.<JCTree.JCExpression>getModificators(
			tree.getTypeArguments(), newTree -> { throw new UnsupportedOperationException("can not modify types"); }));
		scan(tree.getArguments(), ModifyingTreePathScanner.<JCTree.JCExpression>getModificators(tree.getArguments(), l -> ((JCTree.JCNewClass) tree).args = l));
		scan(tree.getClassBody(), newTree -> ((JCTree.JCNewClass) tree).def = (JCTree.JCClassDecl) newTree);
		return null;
	}

	@Override
	public Void visitNewArray(NewArrayTree tree, Modificator modificator) {
		scan(tree.getType(), newTree -> { throw new UnsupportedOperationException("can not modify types"); });
		scan(tree.getDimensions(), ModifyingTreePathScanner.<JCTree.JCExpression>getModificators(tree.getDimensions(), l -> ((JCTree.JCNewArray) tree).dims = l));
		scan(tree.getInitializers(), ModifyingTreePathScanner.<JCTree.JCExpression>getModificators(tree.getInitializers(), l -> ((JCTree.JCNewArray) tree).elems = l));
		scan(tree.getAnnotations(), ModifyingTreePathScanner.<JCTree.JCAnnotation>getModificators(tree.getAnnotations(), l -> ((JCTree.JCNewArray) tree).annotations = l));


		//TODO: Implement multi dimension array
//		Iterable<? extends AnnotationTree> annotationTrees;
//		for(
//			Iterator<? extends List<? extends AnnotationTree>> treesIt = tree.getDimAnnotations().iterator();
//			treesIt.hasNext();
//			scan(annotationTrees, ModifyingTreePathScanner.<JCTree.JCAnnotation>getModificators(annotationTrees, l -> { throw new UnsupportedOperationException("can not modify inner array dims"); }))
//		) {
//			annotationTrees = treesIt.next();
//		}

		return null;
	}

	@Override
	public Void visitLambdaExpression(LambdaExpressionTree tree, Modificator modificator) {
		scan(tree.getParameters(), ModifyingTreePathScanner.<JCTree.JCVariableDecl>getModificators(tree.getParameters(), l -> ((JCTree.JCLambda) tree).params = l));
		scan(tree.getBody(), newTree -> ((JCTree.JCLambda) tree).body = newTree);
		return null;
	}

	@Override
	public Void visitParenthesized(ParenthesizedTree tree, Modificator modificator) {
		scan(tree.getExpression(), newTree -> ((JCTree.JCParens) tree).expr = (JCTree.JCExpression) newTree);
		return null;
	}

	@Override
	public Void visitAssignment(AssignmentTree tree, Modificator modificator) {
		scan(tree.getExpression(), newTree -> ((JCTree.JCAssign) tree).rhs = (JCTree.JCExpression) newTree);
		scan(tree.getVariable(), newTree -> ((JCTree.JCAssign) tree).lhs = (JCTree.JCExpression) newTree);
		return null;
	}

	@Override
	public Void visitCompoundAssignment(CompoundAssignmentTree tree, Modificator modificator) {
		scan(tree.getVariable(), newTree -> ((JCTree.JCAssignOp) tree).lhs = (JCTree.JCExpression) newTree);
		scan(tree.getExpression(), newTree -> ((JCTree.JCAssignOp) tree).rhs = (JCTree.JCExpression) newTree);
		return null;
	}

	@Override
	public Void visitUnary(UnaryTree tree, Modificator modificator) {
		scan(tree.getExpression(), newTree -> ((JCTree.JCUnary) tree).arg = (JCTree.JCExpression) newTree);
		return null;
	}

	@Override
	public Void visitBinary(BinaryTree tree, Modificator modificator) {
		scan(tree.getLeftOperand(), newTree -> ((JCTree.JCBinary) tree).lhs = (JCTree.JCExpression) newTree);
		scan(tree.getRightOperand(), newTree -> ((JCTree.JCBinary) tree).rhs = (JCTree.JCExpression) newTree);
		return null;
	}

	@Override
	public Void visitTypeCast(TypeCastTree tree, Modificator modificator) {
		scan(tree.getType(), newTree -> { throw new UnsupportedOperationException("can not modify types"); });
		scan(tree.getExpression(), newTree -> ((JCTree.JCTypeCast) tree).expr = (JCTree.JCExpression) newTree);
		return null;
	}

	@Override
	public Void visitInstanceOf(InstanceOfTree tree, Modificator modificator) {
		scan(tree.getExpression(), newTree -> ((JCTree.JCInstanceOf) tree).expr = (JCTree.JCExpression) newTree);
		scan(tree.getType(), newTree -> { throw new UnsupportedOperationException("can not modify types"); });
		return null;
	}

	@Override
	public Void visitArrayAccess(ArrayAccessTree tree, Modificator modificator) {
		scan(tree.getExpression(), newTree -> ((JCTree.JCArrayAccess) tree).indexed = (JCTree.JCExpression) newTree);
		scan(tree.getIndex(), newTree -> ((JCTree.JCArrayAccess) tree).index = (JCTree.JCExpression) newTree);
		return null;
	}

	@Override
	public Void visitMemberSelect(MemberSelectTree tree, Modificator modificator) {
		scan(tree.getExpression(), newTree -> ((JCTree.JCFieldAccess) tree).selected = (JCTree.JCExpression) newTree);
		return null;
	}

	@Override
	public Void visitMemberReference(MemberReferenceTree tree, Modificator modificator) {
		scan(tree.getQualifierExpression(), newTree -> ((JCTree.JCMemberReference) tree).expr = (JCTree.JCExpression) newTree);
		scan(tree.getTypeArguments(), ModifyingTreePathScanner.<JCTree.JCAnnotation>getModificators(tree.getTypeArguments(), l -> { throw new UnsupportedOperationException("can not modify types"); }));
		return null;
	}

	@Override
	public Void visitIdentifier(IdentifierTree tree, Modificator modificator) {
		return null;
	}

	@Override
	public Void visitLiteral(LiteralTree tree, Modificator modificator) {
		return null;
	}

	@Override
	public Void visitPrimitiveType(PrimitiveTypeTree tree, Modificator modificator) {
		return null;
	}

	@Override
	public Void visitArrayType(ArrayTypeTree tree, Modificator modificator) {
		scan(tree.getType(), newTree -> { throw new UnsupportedOperationException("can not modify types"); });
		return null;
	}

	@Override
	public Void visitParameterizedType(ParameterizedTypeTree tree, Modificator modificator) {
		scan(tree.getType(), newTree -> { throw new UnsupportedOperationException("can not modify types"); });
		scan(tree.getTypeArguments(), ModifyingTreePathScanner.<JCTree.JCAnnotation>getModificators(tree.getTypeArguments(), l -> { throw new UnsupportedOperationException("can not modify types"); }));
		return null;
	}

	@Override
	public Void visitUnionType(UnionTypeTree tree, Modificator modificator) {
		scan(tree.getTypeAlternatives(), ModifyingTreePathScanner.<JCTree.JCAnnotation>getModificators(tree.getTypeAlternatives(), l -> { throw new UnsupportedOperationException("can not modify types"); }));
		return null;
	}

	@Override
	public Void visitIntersectionType(IntersectionTypeTree tree, Modificator modificator) {
		scan(tree.getBounds(), ModifyingTreePathScanner.<JCTree.JCAnnotation>getModificators(tree.getBounds(), l -> { throw new UnsupportedOperationException("can not modify types"); }));
		return null;
	}

	@Override
	public Void visitTypeParameter(TypeParameterTree tree, Modificator modificator) {
		scan(tree.getAnnotations(), ModifyingTreePathScanner.<JCTree.JCAnnotation>getModificators(tree.getAnnotations(), l -> { throw new UnsupportedOperationException("can not modify types"); }));
		scan(tree.getBounds(), ModifyingTreePathScanner.<JCTree.JCAnnotation>getModificators(tree.getBounds(), l -> { throw new UnsupportedOperationException("can not modify types"); }));
		return null;
	}

	@Override
	public Void visitWildcard(WildcardTree tree, Modificator modificator) {
		scan(tree.getBound(), newTree -> { throw new UnsupportedOperationException("can not modify types"); });
		return null;
	}

	@Override
	public Void visitModifiers(ModifiersTree tree, Modificator modificator) {
		scan(tree.getAnnotations(), ModifyingTreePathScanner.<JCTree.JCAnnotation>getModificators(tree.getAnnotations(), l -> ((JCTree.JCModifiers) tree).annotations = l));
		return null;
	}

	@Override
	public Void visitAnnotation(AnnotationTree tree, Modificator modificator) {
		scan(tree.getAnnotationType(), newTree -> ((JCTree.JCAnnotation) tree).annotationType = newTree);
		scan(tree.getArguments(), ModifyingTreePathScanner.<JCTree.JCExpression>getModificators(tree.getArguments(), l -> ((JCTree.JCAnnotation) tree).args = l));
		return null;
	}

	@Override
	public Void visitAnnotatedType(AnnotatedTypeTree tree, Modificator modificator) {
		scan(tree.getAnnotations(), ModifyingTreePathScanner.<JCTree.JCAnnotation>getModificators(tree.getAnnotations(), l -> ((JCTree.JCAnnotatedType) tree).annotations = l));
		scan(tree.getUnderlyingType(), newTree -> ((JCTree.JCAnnotatedType) tree).underlyingType = (JCTree.JCExpression) newTree);
		return null;
	}

	@Override
	public Void visitOther(Tree tree, Modificator modificator) {
		return null;
	}

	@Override
	public Void visitErroneous(ErroneousTree tree, Modificator modificator) {
		return null;
	}

	@Override
	public Void visitModule(ModuleTree tree, Modificator modificator) {
		return super.visitModule(tree, modificator);
	}

	@Override
	public Void visitExports(ExportsTree tree, Modificator modificator) {
		return super.visitExports(tree, modificator);
	}

	@Override
	public Void visitOpens(OpensTree tree, Modificator modificator) {
		return super.visitOpens(tree, modificator);
	}

	@Override
	public Void visitProvides(ProvidesTree tree, Modificator modificator) {
		return super.visitProvides(tree, modificator);
	}

	@Override
	public Void visitRequires(RequiresTree tree, Modificator modificator) {
		return super.visitRequires(tree, modificator);
	}

	@Override
	public Void visitUses(UsesTree tree, Modificator modificator) {
		return super.visitUses(tree, modificator);
	}
}
