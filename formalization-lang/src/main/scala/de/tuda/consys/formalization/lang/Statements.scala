package de.tuda.consys.formalization.lang

import de.tuda.consys.formalization.lang.types.{ConsistencyType, MutabilityType, Type}

sealed trait Statement

case object Skip extends Statement

case object Error extends Statement

case object Return extends Statement

case class ReturnExpr(e: Expression) extends Statement

case class Block(s: Statement) extends Statement

case class Sequence(s1: Statement, s2: Statement) extends Statement

case class If(conditionExpr: Expression, thenStmt: Statement, elseStmt: Statement) extends Statement

case class Let(varId: VarId, e: Expression) extends Statement

case class SetField(fieldId: FieldId, valueExpr: Expression) extends Statement

case class CallUpdate(recvExpr: Expression, methodId: MethodId, argumentExprs: Seq[Expression]) extends Statement

case class Transaction(body: Statement, except: Statement) extends Statement

case class GetField(varId: VarId, fieldId: FieldId) extends Statement

case class CallQuery(varId: VarId, recvExpr: Expression, methodId: MethodId, argumentExprs: Seq[Expression]) extends Statement

case class Replicate(varId: VarId, location: String,
                        classId: ClassId,
                        consistencyArguments: Seq[ConsistencyType],
                        typeArguments: Seq[Type],
                        constructor: Seq[Expression],
                        consistency: ConsistencyType,
                        mutability: MutabilityType) extends Statement
