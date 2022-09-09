package de.tuda.stg.consys.invariants.lang.ast

import de.tuda.stg.consys.invariants.lang.{ClassId, FieldId, MethodId, VarId}

sealed trait Statement extends ASTNode

object Statement {

	case class Return(expr : Expression) extends Statement
	case class DoNew(x : VarId, cls : ClassId, fields : Seq[Expression], body : Statement) extends Statement
	case class DoGetField(x : VarId, field : FieldId, body : Statement) extends Statement
	case class DoSetField(x : VarId, field : FieldId, newExpr : Expression, body : Statement) extends Statement
	case class DoCallMethod(x : VarId, recv : Expression, m : MethodId, args : Seq[Expression], body : Statement) extends Statement

}
