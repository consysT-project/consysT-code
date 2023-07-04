package de.tuda.consys.formalization.lang.types

import de.tuda.consys.formalization.lang.ClassTable.ClassTable
import de.tuda.consys.formalization.lang.{ClassId, ClassTable, Natives, TypeVarEnv, TypeVarId}
import de.tuda.consys.formalization.lang.types.Types._
import de.tuda.consys.formalization.lang.errors.TypeError

sealed trait Type extends TypeLike[Type]

case class TypeVar(typeVarId: TypeVarId) extends Type {
    def <=(t: Type)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Boolean = t match {
        case _: TypeVar => resolveType(this, typeVarEnv) <= resolveType(t, typeVarEnv)
        case _: CompoundType => resolveType(this, typeVarEnv) <= t
    }

    def >=(t: Type)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Boolean = t match {
        case _: TypeVar => resolveType(this, typeVarEnv) >= resolveType(t, typeVarEnv)
        case _: CompoundType => resolveType(this, typeVarEnv) >= t
    }

    def lub(t: Type)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Type = ???

    def glb(t: Type)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Type = ???

    override def toString: ClassId = s"$typeVarId"
}

case class ClassType(classId: ClassId, typeArguments: Seq[Type]) extends TypeLike[ClassType] {
    def <=(t: ClassType)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Boolean =
        classId == t.classId || ClassTable.isSuperclass(classId, t.classId)

    def >=(t: ClassType)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Boolean =
        classId == t.classId || ClassTable.isSuperclass(t.classId, classId)

    def lub(t: ClassType)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): ClassType = ???

    def glb(t: ClassType)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): ClassType = ???

    override def toString: ClassId = if (typeArguments.isEmpty) s"$classId" else s"$classId<${typeArguments.mkString(",")}>"
}

case class CompoundType(classType: ClassType, consistencyType: ConsistencyType, mutabilityType: MutabilityType) extends Type {
    if (mutabilityType == Bottom && consistencyType != Local)
        sys.error("invalid bottom type")

    def <=(t: Type)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Boolean = t match {
        case CompoundType(baseType1, consistencyType1, mutabilityType1) =>
            if (classType !<= baseType1)
                false
            else if (consistencyType == Local && mutabilityType == Bottom)
                true
            else if (mutabilityType1 == Immutable)
                mutabilityType <= mutabilityType1 && consistencyType <= consistencyType1
            else
                mutabilityType <= mutabilityType1 && consistencyType == consistencyType1
        case _ => false
    }

    def >=(t: Type)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Boolean = t match {
        case CompoundType(baseType1, consistencyType1, mutabilityType1) =>
            if (classType !>= baseType1)
                false
            else if (consistencyType1 == Local && mutabilityType1 == Bottom)
                true
            else if (mutabilityType == Immutable)
                mutabilityType >= mutabilityType1 && consistencyType >= consistencyType1
            else
                mutabilityType >= mutabilityType1 && consistencyType == consistencyType1
        case _ => false
    }

    def lub(t: Type)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Type = t match {
        case CompoundType(baseType, consistencyType, mutabilityType) => ???
        case _ => ???
    }

    def glb(t: Type)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Type = t match {
        case CompoundType(baseType, consistencyType, mutabilityType) => ???
        case _ => ???
    }

    override def toString: ClassId = s"$mutabilityType $consistencyType $classType"
}

object Types {
    def resolveType(typ: Type, typeVars: TypeVarEnv): CompoundType = typ match {
        case TypeVar(name) =>
            val r = typeVars.getOrElse(name, throw TypeError(s"cannot resolve type variable <$name>"))
            resolveType(r, typeVars)

        case CompoundType(ClassType(classId, typeArgs), c, m) =>
            CompoundType(ClassType(classId, typeArgs.map(typeArg => resolveType(typeArg, typeVars))), c, m)
    }
}
