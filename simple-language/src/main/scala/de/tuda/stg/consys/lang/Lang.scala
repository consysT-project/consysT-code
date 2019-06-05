package de.tuda.stg.consys.lang

import scala.collection.mutable

/**
	* Created on 28.05.19.
	*
	* @author Mirko Köhler
	*/
trait Lang {


	type Addr = Symbol
	type VarName = Symbol
	type ClsName = Symbol
	type FldName = Symbol
	type MthdName = Symbol

	sealed trait Expression
	sealed trait Value
	case class Id(name : VarName) extends Expression
	case class Let(name : VarName, namedExpr : Expression, bodyExpr : Expression) extends Expression
	case class Ref(typ : Type, addr : Addr) extends Expression with Value
	case class New(typ : Type, addr : Addr, args : Seq[Expression]) extends Expression
	case class FldGet(recv : Expression, fld : FldName) extends Expression
	case class FldSet(recv : Expression, fld : FldName, value : Expression) extends Expression
	case class MthdInv(recv : Expression, mthd : MthdName, arg : Expression) extends Expression

	sealed trait ConsistencyLevel
	case object Local extends ConsistencyLevel
	case object Strong extends ConsistencyLevel
	case object Weak extends ConsistencyLevel
	case object Inconsistent extends ConsistencyLevel



	case class Type(cls : ClsName, consistency: ConsistencyLevel)

	sealed trait FieldDef{ def fld : FldName}
	case class TypeFieldDef(typ : Type, fld : FldName) extends FieldDef
	case class InferredFieldDef(cls : ClsName, fld : FldName) extends FieldDef

	case class MethodDef(name : MthdName, paramType : Type, paramName : VarName, returnType : Type, body : Expression)

	case class ClassDef(name : ClsName, parent : Option[ClsName], fields : Seq[FieldDef], methods : Seq[MethodDef])


	object Auxiliary {
		def fieldsOf(ct : ClassTable, cls : ClassDef, consistency : ConsistencyLevel) : Seq[TypeFieldDef] = {
			val ClassDef(name, parent, fields, methods) = cls

			val clsFlds : Seq[TypeFieldDef] = fields.map {
				case typeFld : TypeFieldDef => typeFld
				case InferredFieldDef(infCls, infFld) => TypeFieldDef(Type(infCls, consistency), infFld)
			}

			parent match {
				case None => clsFlds
				case Some(parentName) => clsFlds ++ fieldsOf(ct, ct(parentName), consistency)
			}
		}

		def typeOfField(ct : ClassTable, cls : ClassDef, consistency : ConsistencyLevel, fldName : FldName) : Type = {
			for (fld <- cls.fields) fld match {
				case TypeFieldDef(typ, name) if name == fldName => return typ
				case InferredFieldDef(infCls, name) if name == fldName => return Type(infCls, consistency)
				case _ =>
			}

			cls.parent match {
				case None => sys.error(s"no field $fldName in $cls")
				case Some(parentName) => typeOfField(ct, ct(parentName), consistency, fldName)
			}
		}

		def findMethod(ct : ClassTable, cls : ClassDef, mthdName : MthdName) : MethodDef = {
			for (mthd <- cls.methods) mthd match {
				case mdef@MethodDef(name, _, _, _, _) if name == mthdName => return mdef
				case _ =>
			}

			cls.parent match {
				case None => sys.error(s"no method $mthdName in $cls")
				case Some(parentName) => findMethod(ct, ct(parentName), mthdName)
			}
		}


	}


	type ClassTable = Map[ClsName, ClassDef]


	case class Program(ct : ClassTable, env : TypeEnv, expressions : Seq[Expression])


	object ConsistencyLattice {
		def union(a : ConsistencyLevel, b : ConsistencyLevel) : ConsistencyLevel = (a, b) match {
			case (Inconsistent, _) => Inconsistent
			case (_, Inconsistent) => Inconsistent

			case (Weak, _) => Weak
			case (_, Weak) => Weak

			case (Strong, _) => Strong
			case (_, Strong) => Strong

			case _ => Local
		}

		def smallerEq(a : ConsistencyLevel, b :ConsistencyLevel) : Boolean =
			union(a, b) == b
	}

	object ClassLattice {
		def smallerEq(ct : ClassTable, a : ClsName, b : ClsName) : Boolean = {
			if (a == b) true
			else ct(a) match {
				case ClassDef(_, None, _, _) => false
				case ClassDef(_, Some(parentName), _, _) => smallerEq(ct, parentName, b)
			}
		}
	}

	object TypeLattice {
		def smallerEq(ct : ClassTable, a : Type, b : Type) : Boolean = {
			val Type(clsA, consA) = a
			val Type(clsB, consB) = b
			ConsistencyLattice.smallerEq(consA, consB) && ClassLattice.smallerEq(ct, clsA, clsB)
		}
	}



	type TypeEnv = Map[Addr, Type]
	type LocalTypeEnv = Map[VarName, Type]

	def classType(ct : ClassTable, env : TypeEnv, clsDef : ClassDef, consistency : ConsistencyLevel) : Unit = {
		val ClassDef(name, parent, fields, methods) = clsDef

		//Check parent
		parent match {
			case None =>
			case Some(parentName) => classType(ct, env, ct(parentName), consistency)
		}

		consistency match {
			case Local => methods.foreach(methodType(ct, env, _, name, Inconsistent))
			case _ => methods.foreach(methodType(ct, env, _, name, consistency))
		}
	}

	def methodType(ct : ClassTable, env : TypeEnv, mthd : MethodDef, cls : ClsName, consistency : ConsistencyLevel) : Unit = {
		val MethodDef(name, paramType, paramName, returnType, body) = mthd

		//TODO: Add check that overriding methods is allowed (i.e. has same type as parent method)

		val bodyType = exprType(ct, env, Map(paramName -> paramType, 'this -> Type(cls, consistency)), body)
		require(TypeLattice.smallerEq(ct, bodyType, returnType), s"body of method $name does not match expected return type $returnType, but was $bodyType.\n$mthd")
	}

	def exprType(ct : ClassTable, env : TypeEnv, lenv : LocalTypeEnv, expr : Expression) : Type = expr match {
		case Id(name) => lenv(name)

		case Let(name, namedExpr, bodyExpr) =>
			val namedType = exprType(ct, env, lenv, namedExpr)
			exprType(ct, env, lenv + (name -> namedType), bodyExpr)

		case Ref(typ, addr) =>
			require(TypeLattice.smallerEq(ct, env(addr), typ), s"[Ref] ref type $typ is not a super type of store type ${env(addr)}")
			typ

		case New(typ@Type(cls, l), addr, args) =>
			//val Type(envCls, envL) = env(addr)
			//TODO: Change in type system: Do no lookup local types in type environment
			val Type(envCls, envL) = if (l == Local) typ else env(addr)

			require(ClassLattice.smallerEq(ct, cls, envCls), s"[New] new class $cls is not a sub type of store class $envCls")
			require(envL == l, s"[New] new level $l is not equal to the store level $envL")
			classType(ct, env, ct(cls), l)

			val fields = Auxiliary.fieldsOf(ct, ct(cls), l)
			require(args.size == fields.size, s"[New] argument size ${args.size} does not match the expected field size ${fields.size}")

			args.zip(fields).foreach(t => {
				val (arg, TypeFieldDef(typ, _)) = t
				val parType = exprType(ct, env, lenv, arg)
				require(TypeLattice.smallerEq(ct, parType, typ),
					s"[New] argument type $parType does not match type of parameter $typ")
			})

			typ

		case FldGet(recv, fld) =>
			val Type(recvCls, recvL) = exprType(ct, env, lenv, recv)
			val Type(fldCls, fldL) = Auxiliary.typeOfField(ct, ct(recvCls), recvL, fld)

			Type(fldCls, ConsistencyLattice.union(fldL, recvL))

		case FldSet(recv, fld, value) =>
			val Type(recvCls, recvL) = exprType(ct, env, lenv, recv)
			val expectedType@Type(fldCls, fldL) = Auxiliary.typeOfField(ct, ct(recvCls), recvL, fld)

			val valueType = exprType(ct, env, lenv, value)
			require(TypeLattice.smallerEq(ct, valueType, expectedType),
				s"[New] type of value $valueType does not match expected type of field $expectedType")

			valueType

		case MthdInv(recv, mthdName, arg) =>
			val Type(recvCls, recvL) = exprType(ct, env, lenv, recv)
			val mdef = Auxiliary.findMethod(ct, ct(recvCls), mthdName)
			require(TypeLattice.smallerEq(ct, exprType(ct, env, lenv, arg), mdef.paramType))

			mdef.returnType
	}

	def progType(program : Program): Boolean = {
		program.expressions.foreach(expr => exprType(program.ct, program.env, Map(), expr))
		true
	}

}
