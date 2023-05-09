package de.tuda.consys.invariants.solver.next.translate.types

import de.tuda.consys.invariants.solver.next.ir.IR.{ClassType, Type, TypeVar}
import de.tuda.consys.invariants.solver.next.translate.types.TypeChecker.{TypeEnv, TypeException}

object Types {

  def resolveType(typ : Type, typeVars : TypeEnv) : Type = typ match {
    case TypeVar(x) => typeVars.getOrElse(x, throw TypeException(s"type variable not declared: " + x))
    case ClassType(classId, typeArgs) =>
      ClassType(classId, typeArgs.map(arg => resolveType(arg, typeVars)))
  }

}
