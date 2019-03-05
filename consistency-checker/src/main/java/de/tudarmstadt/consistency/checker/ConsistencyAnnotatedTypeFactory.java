package de.tudarmstadt.consistency.checker;

import com.sun.source.tree.*;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.type.AnnotatedTypeMirror;

import javax.lang.model.element.Element;

public class ConsistencyAnnotatedTypeFactory extends BaseAnnotatedTypeFactory {
    public ConsistencyAnnotatedTypeFactory(BaseTypeChecker checker) {
        /*
        	Set useFlow to false if the flow analysis should be used.
         */
        super(checker, true);
        this.postInit();
    }

    @Override
    //Trees: check bodies of methods
    protected void addComputedTypeAnnotations(Tree tree, AnnotatedTypeMirror type, boolean iUseFlow) {

        tree.accept(new TreeVisitor<Object, Object>() {
            @Override
            public Object visitAnnotatedType(AnnotatedTypeTree annotatedTypeTree, Object o) {

            }

            @Override
            public Object visitAnnotation(AnnotationTree annotationTree, Object o) {
                return null;
            }

            @Override
            public Object visitMethodInvocation(MethodInvocationTree methodInvocationTree, Object o) {
                return null;
            }

            @Override
            public Object visitAssert(AssertTree assertTree, Object o) {
                return null;
            }

            @Override
            public Object visitAssignment(AssignmentTree assignmentTree, Object o) {
                assignmentTree.
                return null;
            }

            @Override
            public Object visitCompoundAssignment(CompoundAssignmentTree compoundAssignmentTree, Object o) {
                return null;
            }

            @Override
            public Object visitBinary(BinaryTree binaryTree, Object o) {
                return null;
            }

            @Override
            public Object visitBlock(BlockTree blockTree, Object o) {
                return null;
            }

            @Override
            public Object visitBreak(BreakTree breakTree, Object o) {
                return null;
            }

            @Override
            public Object visitCase(CaseTree caseTree, Object o) {
                return null;
            }

            @Override
            public Object visitCatch(CatchTree catchTree, Object o) {
                return null;
            }

            @Override
            public Object visitClass(ClassTree classTree, Object o) {
                return null;
            }

            @Override
            public Object visitConditionalExpression(ConditionalExpressionTree conditionalExpressionTree, Object o) {
                return null;
            }

            @Override
            public Object visitContinue(ContinueTree continueTree, Object o) {
                return null;
            }

            @Override
            public Object visitDoWhileLoop(DoWhileLoopTree doWhileLoopTree, Object o) {
                return null;
            }

            @Override
            public Object visitErroneous(ErroneousTree erroneousTree, Object o) {
                return null;
            }

            @Override
            public Object visitExpressionStatement(ExpressionStatementTree expressionStatementTree, Object o) {
                return null;
            }

            @Override
            public Object visitEnhancedForLoop(EnhancedForLoopTree enhancedForLoopTree, Object o) {
                return null;
            }

            @Override
            public Object visitForLoop(ForLoopTree forLoopTree, Object o) {
                return null;
            }

            @Override
            public Object visitIdentifier(IdentifierTree identifierTree, Object o) {
                return null;
            }

            @Override
            public Object visitIf(IfTree ifTree, Object o) {
                return null;
            }

            @Override
            public Object visitImport(ImportTree importTree, Object o) {
                return null;
            }

            @Override
            public Object visitArrayAccess(ArrayAccessTree arrayAccessTree, Object o) {
                return null;
            }

            @Override
            public Object visitLabeledStatement(LabeledStatementTree labeledStatementTree, Object o) {
                return null;
            }

            @Override
            public Object visitLiteral(LiteralTree literalTree, Object o) {
                return null;
            }

            @Override
            public Object visitMethod(MethodTree methodTree, Object o) {
                return null;
            }

            @Override
            public Object visitModifiers(ModifiersTree modifiersTree, Object o) {
                return null;
            }

            @Override
            public Object visitNewArray(NewArrayTree newArrayTree, Object o) {
                return null;
            }

            @Override
            public Object visitNewClass(NewClassTree newClassTree, Object o) {
                return null;
            }

            @Override
            public Object visitLambdaExpression(LambdaExpressionTree lambdaExpressionTree, Object o) {
                return null;
            }

            @Override
            public Object visitParenthesized(ParenthesizedTree parenthesizedTree, Object o) {
                return null;
            }

            @Override
            public Object visitReturn(ReturnTree returnTree, Object o) {
                return null;
            }

            @Override
            public Object visitMemberSelect(MemberSelectTree memberSelectTree, Object o) {
                return null;
            }

            @Override
            public Object visitMemberReference(MemberReferenceTree memberReferenceTree, Object o) {
                return null;
            }

            @Override
            public Object visitEmptyStatement(EmptyStatementTree emptyStatementTree, Object o) {
                return null;
            }

            @Override
            public Object visitSwitch(SwitchTree switchTree, Object o) {
                return null;
            }

            @Override
            public Object visitSynchronized(SynchronizedTree synchronizedTree, Object o) {
                return null;
            }

            @Override
            public Object visitThrow(ThrowTree throwTree, Object o) {
                return null;
            }

            @Override
            public Object visitCompilationUnit(CompilationUnitTree compilationUnitTree, Object o) {
                return null;
            }

            @Override
            public Object visitTry(TryTree tryTree, Object o) {
                return null;
            }

            @Override
            public Object visitParameterizedType(ParameterizedTypeTree parameterizedTypeTree, Object o) {
                return null;
            }

            @Override
            public Object visitUnionType(UnionTypeTree unionTypeTree, Object o) {
                return null;
            }

            @Override
            public Object visitIntersectionType(IntersectionTypeTree intersectionTypeTree, Object o) {
                return null;
            }

            @Override
            public Object visitArrayType(ArrayTypeTree arrayTypeTree, Object o) {
                return null;
            }

            @Override
            public Object visitTypeCast(TypeCastTree typeCastTree, Object o) {
                return null;
            }

            @Override
            public Object visitPrimitiveType(PrimitiveTypeTree primitiveTypeTree, Object o) {
                return null;
            }

            @Override
            public Object visitTypeParameter(TypeParameterTree typeParameterTree, Object o) {
                return null;
            }

            @Override
            public Object visitInstanceOf(InstanceOfTree instanceOfTree, Object o) {
                return null;
            }

            @Override
            public Object visitUnary(UnaryTree unaryTree, Object o) {
                return null;
            }

            @Override
            public Object visitVariable(VariableTree variableTree, Object o) {
                return null;
            }

            @Override
            public Object visitWhileLoop(WhileLoopTree whileLoopTree, Object o) {
                return null;
            }

            @Override
            public Object visitWildcard(WildcardTree wildcardTree, Object o) {
                return null;
            }

            @Override
            public Object visitOther(Tree tree, Object o) {
                return null;
            }
        })

        super.addComputedTypeAnnotations(tree, type, iUseFlow);
    }


    @Override
    //Elements: packages, classes, or methods
    public void addComputedTypeAnnotations(Element elt, AnnotatedTypeMirror type) {
       super.addComputedTypeAnnotations(elt, type);

    }
}
