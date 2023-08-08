package de.tuda.consys.formalization.lang

import de.tuda.consys.formalization.lang.types.{ConsistencyType, MutabilityType, Type}

sealed trait Statement

case class Sequence(s1: Statement, s2: Statement) extends Statement

case class If(conditionExpr: Expression, thenStmt: Statement, elseStmt: Statement) extends Statement

case class Let(varId: VarId, namedExpr: Expression) extends Statement

case class GetField(varId: VarId, fieldId: FieldId) extends Statement

case class SetField(fieldId: FieldId, valueExpr: Expression) extends Statement

case class CallQuery(varId: VarId, recvExpr: Expression, methodId: MethodId, argumentExprs: Seq[Expression]) extends Statement

case class CallUpdate(recvExpr: Expression, methodId: MethodId, argumentExprs: Seq[Expression]) extends Statement

case class Transaction(body: Statement, except: Statement) extends Statement

case class Replicate(varId: VarId, location: String, classId: ClassId, typeArguments: Seq[Type], constructorExprs: Map[FieldId, Expression], consistency: ConsistencyType, mutability: MutabilityType) extends Statement

case class Lookup(varId: VarId, location: String) extends Statement
