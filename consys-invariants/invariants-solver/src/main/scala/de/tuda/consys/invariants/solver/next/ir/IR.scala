package de.tuda.consys.invariants.solver.next.ir


import com.microsoft.z3.{Context, Expr, Sort}

import scala.collection.mutable


object IR {

	type ClassTable = Map[ClassId, ClassDecl[_ <: MethodDecl]]

	type FieldId = String
	type ClassId = String
	type MethodId = String
	type VarId = String

	case class FieldDecl(name : FieldId, typ : Type)
	case class VarDecl(name : VarId, typ : Type)

	trait MethodDecl {
		def name : MethodId
		def declaredParameters : Seq[VarDecl]
		def declaredParameterTypes : Seq[Type] = declaredParameters.map(varDecl => varDecl.typ)
	}

	trait ObjectMethodDecl extends MethodDecl {
		def body : IRExpr
	}

	trait NativeMethodDecl extends MethodDecl {
		def impl : (Context, Expr[_], Seq[Expr[_]]) => Expr[_]
	}

	trait QueryMethodDecl extends MethodDecl {
		def returnTyp : Type
	}

	trait UpdateMethodDecl extends MethodDecl {

	}

	case class ObjectQueryMethodDecl(
		override val name : MethodId,
		override val declaredParameters : Seq[VarDecl],
		override val returnTyp : Type ,
		override val body : IRExpr
	) extends ObjectMethodDecl with QueryMethodDecl

	case class ObjectUpdateMethodDecl(
		override val name : MethodId,
		override val declaredParameters : Seq[VarDecl],
		override val body : IRExpr
	) extends ObjectMethodDecl with UpdateMethodDecl

	case class NativeQueryMethodDecl(
		override val name : MethodId,
		override val declaredParameters : Seq[VarDecl],
		override val returnTyp : Type,
		override val impl : (Context, Expr[_], Seq[Expr[_]]) => Expr[_]
	) extends NativeMethodDecl with QueryMethodDecl

	trait ClassDecl[MDecl <: MethodDecl] {
		def classId : ClassId
		def methods : Map[MethodId, MDecl]
		lazy val toType : Type = Type(classId)

		def getField(fieldId : FieldId) : Option[FieldDecl]
		def getMethod(methodId : MethodId) : Option[MDecl]
	}

	case class ObjectClassDecl(
		override val classId : ClassId,
		invariant : IRExpr,
		fields : Map[FieldId, FieldDecl],
		override val methods : Map[MethodId, ObjectMethodDecl]
	) extends ClassDecl[ObjectMethodDecl] {

		override def getField(fieldId : FieldId) : Option[FieldDecl] =
			fields.get(fieldId)
		override def getMethod(methodId : MethodId) : Option[ObjectMethodDecl] =
			methods.get(methodId)
	}

	case class NativeClassDecl(
		override val classId : ClassId,
		val sortImpl : Context => Sort,
		override val methods : Map[MethodId, NativeMethodDecl]
	) extends ClassDecl[NativeMethodDecl] {

		override def getField(fieldId : FieldId) : Option[FieldDecl] = None
		override def getMethod(methodId : MethodId) : Option[NativeMethodDecl] =
			methods.get(methodId)
	}

	case class Type(name : ClassId)

	trait IRExpr

	trait IRLiteral extends IRExpr
	case class Num(n : Int) extends IRLiteral
	case object True extends IRLiteral
	case object False extends IRLiteral
	case class Str(s : String) extends IRLiteral
	case object UnitLiteral extends IRLiteral

	case class Var(id : VarId) extends IRExpr
	case class Let(id : VarId, namedExpr : IRExpr, body : IRExpr) extends IRExpr

	case class If(conditionExpr : IRExpr, thenExpr : IRExpr, elseExpr : IRExpr) extends IRExpr

	case class Equals(e1 : IRExpr, e2 : IRExpr) extends IRExpr

	case object This extends IRExpr
	case class GetField(fieldId : FieldId) extends IRExpr
	case class SetField(fieldId : FieldId, value : IRExpr) extends IRExpr

	trait IRMethodCall extends IRExpr {
		def arguments : Seq[IRExpr]
		def methodId : MethodId
	}
	case class CallQuery(recv : IRExpr, methodId : MethodId, arguments : Seq[IRExpr]) extends IRMethodCall
	case class CallUpdateThis(methodId : MethodId, arguments : Seq[IRExpr]) extends IRMethodCall
	case class CallUpdateField(fieldId : FieldId, methodId : MethodId, arguments : Seq[IRExpr]) extends IRMethodCall








	case class ProgramDecl(classTable : ClassTable) {
		lazy val classes : Iterable[ClassDecl[_ <: MethodDecl]] = makeClassTableIterable

		private def makeClassTableIterable : Iterable[ClassDecl[_ <: MethodDecl]] = {
			val classDecls = classTable.values
			val classDependenciesBuilder = Map.newBuilder[ClassId, Set[ClassId]]

			for (classDecl <- classDecls) {
				classDecl match {
					case NativeClassDecl(name, sort, methods) =>
						classDependenciesBuilder.addOne(name, Set())
					case ObjectClassDecl(name, invariant, fields, methods) =>
						val dependencies = fields.values.map(decl => decl.typ.name).toSet
						classDependenciesBuilder.addOne(name, dependencies)
				}
			}
			val classDependencies = classDependenciesBuilder.result()


			val iterable = Iterable.newBuilder[ClassDecl[_ <: MethodDecl]]
			val resolvedDependencies = mutable.Set.empty[ClassId]
			while (resolvedDependencies.size < classDecls.size) {
				val before = resolvedDependencies.size
				for (classDecl <- classDecls) {
					if (classDependencies(classDecl.classId).subsetOf(resolvedDependencies)) {
						iterable.addOne(classDecl)
						resolvedDependencies.addOne(classDecl.classId)
					}
				}
				if (resolvedDependencies.size == before)
					throw new Exception("cyclic dependency when resolving classes")
			}

			iterable.result()
		}

	}

}
