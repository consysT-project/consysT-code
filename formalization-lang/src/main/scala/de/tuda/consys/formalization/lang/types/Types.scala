package de.tuda.consys.formalization.lang.types

import de.tuda.consys.formalization.lang.ClassTable.ClassTable
import de.tuda.consys.formalization.lang.{ClassId, ClassTable, Natives, TypeVarEnv, TypeVarId}
import de.tuda.consys.formalization.lang.types.Types._
import de.tuda.consys.formalization.lang.errors.TypeError

sealed trait Type extends TypeLike[Type]

case class TypeVar(typeVarId: TypeVarId) extends Type {
    def <=(t: Type)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Boolean =
        typeVarEnv.getOrElse(typeVarId, sys.error(s"cannot resolve type variable: $typeVarId")) <= t

    def >=(t: Type)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Boolean =
        this == t

    def lub(t: Type)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Type = ???

    def glb(t: Type)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Type = ???

    override def toString: ClassId = s"$typeVarId"
}

case class ClassType(classId: ClassId,
                     consistencyArguments: Seq[ConsistencyType],
                     typeArguments: Seq[Type]) extends TypeLike2[ClassType, MutabilityType] {
    def <=(t: ClassType)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv, t2: MutabilityType): Boolean = t2 match {
        case Immutable if this.classId == t.classId && this.typeArguments == t.typeArguments =>
            (this.consistencyArguments zip t.consistencyArguments).map(c => c._1 <= c._2).reduce(_&&_)
        case _ =>
            ClassTable.isSuperClassType(this, t)
    }

    def >=(t: ClassType)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv, t2: MutabilityType): Boolean = t2 match {
        case Immutable if t.classId == this.classId && t.typeArguments == this.typeArguments =>
            (t.consistencyArguments zip this.consistencyArguments).map(c => c._1 <= c._2).reduce(_ && _)
        case _ =>
            ClassTable.isSuperClassType(t, this)
    }

    def lub(t: ClassType)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv, t2: MutabilityType): ClassType = ???

    def glb(t: ClassType)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv, t2: MutabilityType): ClassType = ???

    override def toString: String =
        if (typeArguments.isEmpty) s"$classId"
        else s"$classId<${consistencyArguments.mkString(",")},${typeArguments.mkString(",")}>"
}

case class RefType(classType: ClassType, consistencyType: ConsistencyType, mutabilityType: MutabilityType) extends Type {
    def <=(t: Type)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Boolean = t match {
        case RefType(classType, consistencyType, mutabilityType) =>
            CompoundClassType(this.classType, this.consistencyType, this.mutabilityType) <=
                CompoundClassType(classType, consistencyType, mutabilityType)
        case _ => false
    }

    def >=(t: Type)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Boolean = t match {
        case RefType(classType, consistencyType, mutabilityType) =>
            CompoundClassType(this.classType, this.consistencyType, this.mutabilityType) >=
                CompoundClassType(classType, consistencyType, mutabilityType)
        case _ => false
    }

    def lub(t: Type)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Type = ???

    def glb(t: Type)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Type = ???

    override def toString: String = s"[$mutabilityType $consistencyType] Ref[$classType]"
}

case class CompoundClassType(classType: ClassType, consistencyType: ConsistencyType, mutabilityType: MutabilityType) extends Type {
    def <=(t: Type)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Boolean = t match {
        case CompoundClassType(classType, consistencyType, mutabilityType) =>
            implicit val t2 = mutabilityType
            this.consistencyType <= consistencyType &&
                this.mutabilityType <= mutabilityType &&
                this.classType <= classType

        case _ => false
    }

    def >=(t: Type)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Boolean = ???

    def lub(t: Type)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Type = ???

    def glb(t: Type)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Type = ???

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

    def substitute(typ: ClassType, typeVars: TypeVarEnv): ClassType = {
        ClassType(typ.classId, typ.consistencyArguments, typ.typeArguments.map(t => substitute(t, typeVars)))
    }

    def substitute(typ: Type, typeVars: TypeVarEnv): Type = {
        typ match {
            case TypeVar(typeVarId) => typeVars.get(typeVarId) match {
                case Some(value) => value
                case None => TypeVar(typeVarId)
            }

            case RefType(classType, consistencyType, mutabilityType) =>
                RefType(substitute(classType, typeVars), consistencyType, mutabilityType)

            case CompoundClassType(classType, consistencyType, mutabilityType) =>
                CompoundClassType(substitute(classType, typeVars), consistencyType, mutabilityType)
        }
    }
}
