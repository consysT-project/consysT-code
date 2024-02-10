package de.tuda.stg.consys.invariants.lang.ast

import de.tuda.stg.consys.invariants.lang.{ClassId, FieldId, MethodId, VarId}

sealed trait Statement extends ASTNode

object Statement {

	case class Return(e : Expression) extends Statement
	case class DoNew(x : VarId, c : ClassId, fields : Seq[Expression], body : Statement) extends Statement
	case class DoGetField(x : VarId, f : FieldId, body : Statement) extends Statement
	case class DoSetField(x : VarId, f : FieldId, e : Expression, body : Statement) extends Statement
	case class DoCallMethod(x : VarId, recv : Expression, m : MethodId, args : Seq[Expression], body : Statement) extends Statement

}
