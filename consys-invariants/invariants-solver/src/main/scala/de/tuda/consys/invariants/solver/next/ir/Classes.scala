package de.tuda.consys.invariants.solver.next.ir


import com.microsoft.z3.{Context, Sort, Expr => Z3Expr}
import de.tuda.consys.invariants.solver.next.ir.Expressions.{BaseExpressions, BaseLang}
import de.tuda.consys.invariants.solver.next.ir.Types.{ClassType, Type, TypeVar}

import scala.collection.mutable


object Classes {

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






	case class ProgramDecl[Expr <: BaseExpressions#Expr](classTable : ClassTable[Expr], mainExpression : Expr) {

		lazy val classes : Iterable[Either[NativeClassDecl, ObjectClassDecl[Expr]]] = makeClassTableIterable

		def classDeclarations : Iterable[ClassDecl[_ <: MethodDecl]] = classes.map({
			case Left(nativeClassDecl) => nativeClassDecl
			case Right(objectClassDecl) => objectClassDecl
		})

		// Creates an iterable the iterates classes in the order of dependencies, i.e., a class will only appear in the
		// iterable if all dependencies for that class have been resolved first.
		private def makeClassTableIterable : Iterable[Either[NativeClassDecl, ObjectClassDecl[Expr]]] = {

			def classesInType(typ : Type) : Set[ClassId] = typ match {
				case TypeVar(typeVarId) => Set()
				case ClassType(classId, typeArguments) =>
					Set(classId) ++ typeArguments.foldLeft(Set.empty[ClassId])((set, typArg) => set ++ classesInType(typArg))
			}

			val classDeclEithers = classTable.values
			val classDependenciesBuilder = Map.newBuilder[ClassId, Set[ClassId]]

			for (classDeclEither <- classDeclEithers) {
				classDeclEither match {
					case Left(nativeClassDecl) =>
						classDependenciesBuilder.addOne(nativeClassDecl.classId, Set())
					case Right(objectClassDecl) =>
						val dependencies : Set[ClassId] = objectClassDecl.fields.values.flatMap(decl => classesInType(decl.typ)).toSet
						classDependenciesBuilder.addOne(objectClassDecl.classId, dependencies)
				}
			}
			val classDependencies = classDependenciesBuilder.result()

			val iterable = Iterable.newBuilder[Either[NativeClassDecl, ObjectClassDecl[Expr]]]
			val resolvedDependencies = mutable.Set.empty[ClassId]

			while (resolvedDependencies.size < classDeclEithers.size) {
				val before = resolvedDependencies.size

				for (classDeclEither <- classDeclEithers) {
					val classId = classDeclEither match {
						case Left(nativeClassDecl) => nativeClassDecl.classId
						case Right(objectClassDecl) => objectClassDecl.classId
					}

					if (!resolvedDependencies.contains(classId) && classDependencies(classId).subsetOf(resolvedDependencies)) {
						iterable.addOne(classDeclEither)
						resolvedDependencies.addOne(classId)
					}

				}

				if (resolvedDependencies.size == before)
					throw new Exception("cyclic dependency when resolving classes")
			}

			iterable.result()
		}

	}

}
