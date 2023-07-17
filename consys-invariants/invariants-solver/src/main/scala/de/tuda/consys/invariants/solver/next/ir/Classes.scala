package de.tuda.consys.invariants.solver.next.ir


import com.microsoft.z3.{Context, Expr => Z3Expr, Sort}
import de.tuda.consys.invariants.solver.next.ir.Expressions.{BaseExpressions, BaseLang}

import scala.collection.mutable


object Classes {

	type ClassTable = Map[ClassId, ClassDecl[_ <: MethodDecl]]

	type FieldId = String
	type ClassId = String
	type MethodId = String
	type VarId = String
	type TypeVarId = String

	case class FieldDecl(name : FieldId, typ : Type)
	case class VarDecl(name : VarId, typ : Type)

	trait MethodDecl {
		def name : MethodId
		def declaredParameters : Seq[VarDecl]

		def declaredParameterTypes : Seq[Type] =
			declaredParameters.map(varDecl => varDecl.typ)
	}

	trait ObjectMethodDecl[Expr <: BaseExpressions#Expr] extends MethodDecl {
		def body : Expr
	}

	trait NativeMethodDecl extends MethodDecl {
		def impl : (Context, Z3Expr[_ <: Sort], Seq[Z3Expr[_ <: Sort]]) => Z3Expr[_ <: Sort]
	}

	trait QueryMethodDecl extends MethodDecl {
		def returnTyp : Type
	}

	trait UpdateMethodDecl extends MethodDecl {

	}

	case class ObjectQueryMethodDecl[Expr <: BaseExpressions#Expr](
		override val name : MethodId,
		override val declaredParameters : Seq[VarDecl],
		override val returnTyp : Type,
		override val body : Expr
	) extends ObjectMethodDecl[Expr] with QueryMethodDecl

	case class ObjectUpdateMethodDecl[Expr <: BaseExpressions#Expr](
		override val name : MethodId,
		override val declaredParameters : Seq[VarDecl],
		override val body : Expr
	) extends ObjectMethodDecl[Expr] with UpdateMethodDecl

	case class NativeQueryMethodDecl(
		override val name : MethodId,
		override val declaredParameters : Seq[VarDecl],
		override val returnTyp : Type,
		override val impl : (Context, Z3Expr[_ <: Sort], Seq[Z3Expr[_ <: Sort]]) => Z3Expr[_ <: Sort]
	) extends NativeMethodDecl with QueryMethodDecl

	trait ClassDecl[MDecl <: MethodDecl] {
		def classId : ClassId
		def typeParameters : Seq[TypeVar]
		def methods : Map[MethodId, MDecl]

		def getField(fieldId : FieldId) : Option[FieldDecl]
		def getMethod(methodId : MethodId) : Option[MDecl]

		lazy val asType : ClassType =
			ClassType(classId, typeParameters)

		def toType(typeArgs : Seq[Type]) : ClassType = {
			require(typeArgs.length == typeParameters.length)
			ClassType(classId, typeArgs)
		}

		def typeParametersMapTo[A](others : Seq[A]) : Map[TypeVarId, A] =
			typeParameters.map(typeVar => typeVar.typeVarId).zip(others).toMap

	}

	case class ObjectClassDecl[Expr <: BaseExpressions#Expr](
		override val classId : ClassId,
		override val typeParameters : Seq[TypeVar],
		invariant : Expr,
		fields : Map[FieldId, FieldDecl],
		override val methods : Map[MethodId, ObjectMethodDecl[Expr]]
	) extends ClassDecl[ObjectMethodDecl[Expr]] {

		override def getField(fieldId : FieldId) : Option[FieldDecl] =
			fields.get(fieldId)
		override def getMethod(methodId : MethodId) : Option[ObjectMethodDecl[Expr]] =
			methods.get(methodId)
	}

	case class NativeClassDecl(
		override val classId : ClassId,
		override val typeParameters : Seq[TypeVar],
		sortImpl : (Context, Seq[Sort]) => Sort,
		override val methods : Map[MethodId, NativeMethodDecl]
	) extends ClassDecl[NativeMethodDecl] {

		override def getField(fieldId : FieldId) : Option[FieldDecl] = None
		override def getMethod(methodId : MethodId) : Option[NativeMethodDecl] =
			methods.get(methodId)
	}

	trait Type
	case class TypeVar(typeVarId: TypeVarId) extends Type
	case class ClassType(classId : ClassId, typeArguments : Seq[Type]) extends Type








	case class ProgramDecl(classTable : ClassTable) {
		lazy val classes : Iterable[ClassDecl[_ <: MethodDecl]] = makeClassTableIterable

		private def makeClassTableIterable : Iterable[ClassDecl[_ <: MethodDecl]] = {

			def classesInType(typ : Type) : Set[ClassId] = typ match {
				case TypeVar(typeVarId) => Set()
				case ClassType(classId, typeArguments) =>
					Set(classId) ++ typeArguments.foldLeft(Set.empty[ClassId])((set, typArg) => set ++ classesInType(typArg))
			}


			val classDecls = classTable.values
			val classDependenciesBuilder = Map.newBuilder[ClassId, Set[ClassId]]

			for (classDecl <- classDecls) {
				classDecl match {
					case NativeClassDecl(name, typeParameters, sort, methods) =>
						classDependenciesBuilder.addOne(name, Set())
					case ObjectClassDecl(name, typeParameters, invariant, fields, methods) =>
						val dependencies : Set[ClassId] = fields.values.flatMap(decl => classesInType(decl.typ)).toSet
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
