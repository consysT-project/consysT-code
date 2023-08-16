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

sealed trait TerminalType extends Type {
    def consistencyType: ConsistencyType
    def mutabilityType: MutabilityType
    def withConsistency(consistencyType: ConsistencyType): TerminalType
    def withMutability(mutabilityType: MutabilityType): TerminalType
}

case class RefType(classType: ClassType,
                   override val consistencyType: ConsistencyType,
                   override val mutabilityType: MutabilityType
                  ) extends Type with TerminalType {
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

    override def withConsistency(consistencyType: ConsistencyType): TerminalType = copy(consistencyType = consistencyType)

    override def withMutability(mutabilityType: MutabilityType): TerminalType = copy(mutabilityType = mutabilityType)

    override def toString: String = s"[$mutabilityType $consistencyType] Ref[$classType]"
}

case class CompoundClassType(classType: ClassType,
                             override val consistencyType: ConsistencyType,
                             override val mutabilityType: MutabilityType
                            ) extends Type with TerminalType {
    def <=(t: Type)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Boolean = t match {
        case CompoundClassType(classType, consistencyType, mutabilityType) =>
            implicit val t2: MutabilityType = mutabilityType
            this.consistencyType <= consistencyType &&
                this.mutabilityType <= mutabilityType &&
                this.classType <= classType

        case _ => false
    }

    def >=(t: Type)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Boolean = ???

    def lub(t: Type)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Type = ???

    def glb(t: Type)(implicit classTable: ClassTable, typeVarEnv: TypeVarEnv): Type = ???

    override def withConsistency(consistencyType: ConsistencyType): TerminalType = copy(consistencyType = consistencyType)

    override def withMutability(mutabilityType: MutabilityType): TerminalType = copy(mutabilityType = mutabilityType)

    override def toString: ClassId = s"$mutabilityType $consistencyType $classType"
}

object Types {
    def bound(typ: Type)(implicit typeVars: TypeVarEnv): TerminalType = typ match {
        case TypeVar(name) =>
            typeVars.getOrElse(name, throw TypeError(s"cannot resolve type variable <$name>")) match {
                case t: TypeVar => bound(t) // allows recursive type variable bounds
                case t: TerminalType => t
            }

        case t: TerminalType => t
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
