package de.tuda.stg.consys.invariants.lang.ast

import de.tuda.stg.consys.invariants.lang.ast.ASTNode.NodeId
import de.tuda.stg.consys.invariants.lang.{ClassId, FieldId, MethodId, VarId}

sealed trait Statement extends ASTNode

object Statement {

	case class Return(expr: Expression)(override val nodeId: NodeId = ASTNode.freshNodeId()) extends Statement
	case class DoNew(x: VarId, cls: ClassId, fields: Seq[Expression], body: Statement)(override val nodeId: NodeId = ASTNode.freshNodeId()) extends Statement
	case class DoGetField(x: VarId, field: FieldId, body: Statement)(override val nodeId: NodeId = ASTNode.freshNodeId()) extends Statement
	case class DoSetField(x: VarId, field: FieldId, newExpr: Expression, body: Statement)(override val nodeId: NodeId = ASTNode.freshNodeId()) extends Statement
	case class DoCallMethod(x: VarId, receiver: Expression, m: MethodId, args: Seq[Expression], body: Statement)(override val nodeId: NodeId = ASTNode.freshNodeId()) extends Statement

}
