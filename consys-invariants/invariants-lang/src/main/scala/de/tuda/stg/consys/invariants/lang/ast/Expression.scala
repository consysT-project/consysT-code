package de.tuda.stg.consys.invariants.lang.ast

import de.tuda.stg.consys.invariants.lang.ast.ASTNode.NodeId
import de.tuda.stg.consys.invariants.lang.{ClassId, RefId, VarId}

sealed trait Expression extends ASTNode

object Expression {

	sealed trait Val extends Expression {
		override val nodeId : NodeId = ASTNode.freshNodeId()
	}
	sealed trait Op extends Expression

	case object VUnit extends Val
	case class VBool(b : Boolean) extends Val
	case class VInt(i : Int) extends Val
	case class VSet(typ : Type, xs : Set[Val]) extends Val
	case class VPair(x1 : Val, x2 : Val) extends Val
	case class VRef(clsId : ClassId, refId : RefId) extends Val
	case class VString(s : String) extends Val

	case class EVar(x: VarId)(override val nodeId: NodeId = ASTNode.freshNodeId()) extends Expression
	case class ELet(x: VarId, namedExpr: Expression, body: Expression)(override val nodeId: NodeId = ASTNode.freshNodeId()) extends Expression
	case class EPair(e1: Expression, e2: Expression)(override val nodeId: NodeId = ASTNode.freshNodeId()) extends Expression

	case class EPlus(e1: Expression, e2: Expression)(override val nodeId: NodeId = ASTNode.freshNodeId()) extends Op
	case class EFst(expr: Expression)(override val nodeId: NodeId = ASTNode.freshNodeId()) extends Op
	case class ESnd(expr: Expression)(override val nodeId: NodeId = ASTNode.freshNodeId()) extends Op



}


