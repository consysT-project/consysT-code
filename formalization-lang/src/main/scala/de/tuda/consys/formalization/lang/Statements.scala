package de.tuda.consys.formalization.lang

import de.tuda.consys.formalization.lang.types.{ConsistencyType, MutabilityType, Type}

sealed trait Statement

case class Sequence(s1: Statement, s2: Statement) extends Statement

case class If(conditionExpr: Expression, thenStmt: Statement, elseStmt: Statement) extends Statement

case class Let(varId: VarId, rhs: AssignRhs) extends Statement

case class Assign(varId: VarId, rhs: AssignRhs) extends Statement

case class SetField(fieldId: FieldId, valueExpr: Expression) extends Statement

case class CallUpdate(recvExpr: Expression, methodId: MethodId, argumentExprs: Seq[Expression]) extends Statement

case class Transaction(body: Statement, except: Statement) extends Statement

sealed trait AssignRhs

case class rhsExpression(e: Expression) extends AssignRhs

case class rhsGetField(fieldId: FieldId) extends AssignRhs

case class rhsCallQuery(recvExpr: Expression, methodId: MethodId, argumentExprs: Seq[Expression]) extends AssignRhs

case class rhsReplicate(location: String,
                        classId: ClassId,
                        consistencyArguments: Seq[ConsistencyType],
                        typeArguments: Seq[Type],
                        constructor: Seq[Expression],
                        consistency: ConsistencyType,
                        mutability: MutabilityType) extends AssignRhs

case class rhsLookup(location: String,
                     classId: ClassId,
                     consistencyArguments: Seq[ConsistencyType],
                     typeArguments: Seq[Type],
                     consistency: ConsistencyType,
                     mutability: MutabilityType) extends AssignRhs
