package de.tuda.stg.consys.checker

import com.sun.source.tree.{AssignmentTree, CompoundAssignmentTree, ExpressionTree, IdentifierTree, MemberSelectTree, MethodInvocationTree, MethodTree, NewClassTree, Tree}
import com.sun.source.util.TreeScanner
import de.tuda.stg.consys.annotations.ReadOnly
import org.checkerframework.framework.`type`.AnnotatedTypeFactory
import org.checkerframework.javacutil.TreeUtils

class ReadOnlyVisitor(implicit tf: AnnotatedTypeFactory) extends TreeScanner[List[Tree], List[Tree]] {
    /**
     * Checks if a method is compatible with ReadOnly.
     * @param node The method to check
     * @return A list of AST nodes in the method body which are incompatible with ReadOnly.
     *         Nil if whole method is compatible.
     */
    def visitMethod(node: MethodTree): List[Tree] = {
        super.visitMethod(node, Nil).reverse
    }

    override def reduce(r1: List[Tree], r2: List[Tree]): List[Tree] = (r1, r2) match {
        case (_, null) if r1 != null => r1
        case (null, _) if r2 != null => r2
        case _ if r1 != null && r2 != null => r1 ++ r2
        case _ => Nil
    }

    override def visitAssignment(node: AssignmentTree, p: List[Tree]): List[Tree] = {
        val r = super.visitAssignment(node, p)
        if (isLocalVariable(node.getVariable)) r else node :: r
    }

    override def visitCompoundAssignment(node: CompoundAssignmentTree, p: List[Tree]): List[Tree] = {
        val r = super.visitCompoundAssignment(node, p)
        if (isLocalVariable(node.getVariable)) r else node :: r
    }

    override def visitMethodInvocation(node: MethodInvocationTree, p: List[Tree]): List[Tree] = {
        val r = super.visitMethodInvocation(node, p)
        if (TreeUtils.elementFromUse(node).getAnnotation(classOf[ReadOnly]) != null) r else node :: r
    }

    override def visitNewClass(node: NewClassTree, p: List[Tree]): List[Tree] = {
        val r = super.visitNewClass(node, p)
        if (TreeUtils.elementFromUse(node).getAnnotation(classOf[ReadOnly]) != null) r else node :: r
    }

    private def isLocalVariable(node: ExpressionTree): Boolean = node match {
        case m: MemberSelectTree => m.getExpression match {
            case id: IdentifierTree if id.getName.toString == "this" || id.getName.toString == "super" => false
            //case expr => isLocalVariable(expr)
            case expr => TreeUtils.isLocalVariable(node)
        }
        case _ => TreeUtils.isLocalVariable(node)
    }
}
