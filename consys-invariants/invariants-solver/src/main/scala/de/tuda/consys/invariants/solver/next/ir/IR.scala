package de.tuda.consys.invariants.solver.next.ir

object IR {

	type FieldId = String
	type ClassId = String
	type MethodId = String
	type VarId = String

	case class FieldDecl(name : FieldId, typ : IRType)
	case class VarDecl(name : VarId, typ : IRType)

	trait MethodDecl {
		def name : MethodId
		def declaredParameters : Seq[VarDecl]
		def body : IRExpr

		def declaredParameterTypes : Seq[IRType] = declaredParameters.map(varDecl => varDecl.typ)
	}
	case class QueryDecl(override val name : MethodId, override val declaredParameters : Seq[VarDecl], returnTyp : IRType, override val body : IRExpr) extends MethodDecl
	case class UpdateDecl(override val name : MethodId, override val declaredParameters : Seq[VarDecl], override val body : IRExpr) extends MethodDecl

	trait IRClass {
		def name : ClassId
		def toType : IRType = TClass(name)
	}
	case class ObjectClassDecl(override val name : ClassId, invariant : IRExpr, fields : Map[FieldId, FieldDecl], methods : Map[MethodId, MethodDecl]) extends IRClass
	case class NativeClassDecl(override val name : ClassId) extends IRClass

	trait IRType
	case class TClass(name : ClassId) extends IRType

	trait IRExpr

	trait IRLiteral extends IRExpr
	case class Num(n : Int) extends IRLiteral
	case object True extends IRLiteral
	case object False extends IRLiteral
	case class Str(s : String) extends IRLiteral

	case class Var(id : VarId) extends IRExpr
	case class Let(id : VarId, namedExpr : IRExpr, body : IRExpr) extends IRExpr

	case class Equals(e1 : IRExpr, e2 : IRExpr) extends IRExpr

	case object This extends IRExpr
	case class GetField(id : FieldId) extends IRExpr
	case class SetField(id : FieldId, value : IRExpr) extends IRExpr
	case class CallQuery(recv : IRExpr, mthd : MethodId, arguments : Seq[IRExpr]) extends IRExpr



	case class ProgramDecl(classTable : Map[ClassId, IRClass])
}
