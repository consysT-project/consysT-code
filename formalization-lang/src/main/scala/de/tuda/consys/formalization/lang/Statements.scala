package de.tuda.consys.formalization.lang

sealed trait IRExpr

// ---------------------------------------------------------------------------------------------------------------------
// Literal expressions
// ---------------------------------------------------------------------------------------------------------------------

sealed trait IRLiteral extends IRExpr

case class Num(n: Int) extends IRLiteral

case object True extends IRLiteral

case object False extends IRLiteral

case class Str(s: String) extends IRLiteral

case object UnitLiteral extends IRLiteral

// ---------------------------------------------------------------------------------------------------------------------
// Base expressions
// ---------------------------------------------------------------------------------------------------------------------

case class Var(id: VarId) extends IRExpr

case class Let(id: VarId, namedExpr: IRExpr, bodyExpr: IRExpr) extends IRExpr

case class If(conditionExpr: IRExpr, thenExpr: IRExpr, elseExpr: IRExpr) extends IRExpr

case class Equals(expr1: IRExpr, expr2: IRExpr) extends IRExpr

case class Add(expr1: IRExpr, expr2: IRExpr) extends IRExpr

case class New(objectId: String, classId: ClassId, typeArguments: Seq[Type], consistency: ConsistencyType, constructorExprs: Map[FieldId, IRExpr]) extends IRExpr

case class Sequence(exprs: Seq[IRExpr]) extends IRExpr

// ---------------------------------------------------------------------------------------------------------------------
// Class-related expressions
// ---------------------------------------------------------------------------------------------------------------------

case object This extends IRExpr

case class GetField(fieldId: FieldId) extends IRExpr

case class SetField(fieldId: FieldId, valueExpr: IRExpr) extends IRExpr

sealed trait IRMethodCall extends IRExpr {
    def argumentExprs: Seq[IRExpr]

    def methodId: MethodId
}

case class CallQuery(recvExpr: IRExpr, methodId: MethodId, argumentExprs: Seq[IRExpr]) extends IRMethodCall

case class CallUpdate(recvExpr: IRExpr, methodId: MethodId, argumentExprs: Seq[IRExpr]) extends IRMethodCall

// ---------------------------------------------------------------------------------------------------------------------
// Replication-related expressions
// ---------------------------------------------------------------------------------------------------------------------

case class Transaction(bodyExpr: IRExpr) extends IRExpr
