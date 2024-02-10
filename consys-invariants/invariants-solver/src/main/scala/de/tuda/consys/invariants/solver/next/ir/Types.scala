package de.tuda.consys.invariants.solver.next.ir

import de.tuda.consys.invariants.solver.next.ir.Classes.{ClassId, TypeVarId}
import de.tuda.consys.invariants.solver.next.translate.types.TypeChecker.TypeEnv
import de.tuda.consys.invariants.solver.next.translate.types.TypeException

object Types {

	val typePrinter : TypePrinter = new PrettyTypePrinter

	trait Type {
		override def toString : ClassId = typePrinter.print(this)
	}
	case class TypeVar(typeVarId: TypeVarId) extends Type
	case class ClassType(classId : ClassId, typeArguments : Seq[Type]) extends Type


	def resolveType(typ : Type, typeVars : TypeEnv) : Type = typ match {
		case TypeVar(x) => typeVars.getOrElse(x, throw TypeException(s"type variable not declared: " + x))
		case ClassType(classId, typeArgs) =>
			ClassType(classId, typeArgs.map(arg => resolveType(arg, typeVars)))
	}


	trait TypePrinter {
		def print(typ : Type) : String
	}

	class PrettyTypePrinter extends TypePrinter {
		override def print(typ : Type) : ClassId = typ match {
			case TypeVar(typeVarId) => s"$$$typeVarId"
			case ClassType(classId, typeArguments) =>
				if (typeArguments.isEmpty)
					classId
				else
					classId + typeArguments.map(typ => print(typ)).mkString("[", ",", "]")
		}
	}


}
