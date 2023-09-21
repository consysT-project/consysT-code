package de.tuda.consys.formalization.lang.types2

import de.tuda.consys.formalization.lang.ClassTable.ClassTable
import de.tuda.consys.formalization.lang.errors.TypeError
import de.tuda.consys.formalization.lang.{ClassId, ConsistencyVarEnv, TypeVarEnv, TypeVarId, TypeVarMutabilityEnv}

import scala.annotation.tailrec

case class Type(l: ConsistencyType, m: MutabilityType, suffix: TypeSuffix) extends TypeLike[Type] {
    override def <=(t: Type)(implicit classTable: ClassTable,
                             typeVarEnv: TypeVarEnv,
                             consistencyVarEnv: ConsistencyVarEnv): Boolean = Subtyping.subtype(this, t)

    override def >=(t: Type)(implicit classTable: ClassTable,
                             typeVarEnv: TypeVarEnv,
                             consistencyVarEnv: ConsistencyVarEnv): Boolean = Subtyping.subtype(t, this)

    override def lub(t: Type)(implicit classTable: ClassTable,
                              typeVarEnv: TypeVarEnv,
                              consistencyVarEnv: ConsistencyVarEnv): Type = ???

    override def glb(t: Type)(implicit classTable: ClassTable,
                              typeVarEnv: TypeVarEnv,
                              consistencyVarEnv: ConsistencyVarEnv): Type = ???

    override def toString: ClassId = s"[$l $m]$suffix"
}

sealed trait TypeSuffix

case class TypeSuffixVar(id: TypeVarId) extends TypeSuffix {
    override def toString: ClassId = s"$id"
}

sealed trait NonVarTypeSuffix extends TypeSuffix

case class LocalTypeSuffix(classType: ClassType) extends NonVarTypeSuffix {
    override def toString: String = s"$classType"
}

case class RefTypeSuffix(classType: ClassType) extends NonVarTypeSuffix {
    override def toString: String = s"Ref[$classType]"
}

case class ClassType(classId: ClassId,
                     consistencyArguments: Seq[ConsistencyType],
                     typeArguments: Seq[TypeSuffix]) {
    override def toString: String =
        if (typeArguments.isEmpty) s"$classId"
        else s"$classId<${consistencyArguments.mkString(",")},${typeArguments.mkString(",")}>"
}

object Types {
    def bound(typ: Type)(implicit typeVars: TypeVarEnv, consistencyVars: ConsistencyVarEnv): Type =
        Type(bound(typ.l), typ.m, bound(typ.suffix))

    @tailrec
    def bound(typ: TypeSuffix)(implicit typeVars: TypeVarEnv): NonVarTypeSuffix = typ match {
        case TypeSuffixVar(id) =>
            typeVars.getOrElse(id, throw TypeError(s"cannot resolve type variable <$id>")) match {
                case t: TypeSuffixVar => bound(t) // allows recursive type variable bounds
                case t: NonVarTypeSuffix => t
            }

        case t: NonVarTypeSuffix => t
    }

    @tailrec
    def bound(typ: ConsistencyType)(implicit consistencyVars: ConsistencyVarEnv): ConcreteConsistencyType = typ match {
        case ConsistencyVar(name) =>
            consistencyVars.getOrElse(name, throw TypeError(s"cannot resolve consistency variable <$name>")) match {
                case t: ConsistencyVar => bound(t) // allows recursive type variable bounds
                case t: ConcreteConsistencyType => t
            }
        case t: ConcreteConsistencyType => t
    }

    def mBound(t: TypeSuffixVar)(implicit typeVarMutabilityEnv: TypeVarMutabilityEnv): MutabilityType =
        typeVarMutabilityEnv.getOrElse(t.id, throw TypeError(s"cannot resolve type variable <$t.id>"))

    def substitute(typ: Type, typeVars: TypeVarEnv, consistencyVars: ConsistencyVarEnv): Type =
        Type(substitute(typ.l, consistencyVars), typ.m, substitute(typ.suffix, typeVars, consistencyVars))

    def substitute(typ: TypeSuffix, typeVars: TypeVarEnv, consistencyVars: ConsistencyVarEnv): TypeSuffix = typ match {
        case TypeSuffixVar(id) => typeVars.get(id) match {
            case Some(value) => value
            case None => TypeSuffixVar(id)
        }
        case RefTypeSuffix(classType) => RefTypeSuffix(substitute(classType, typeVars, consistencyVars))
        case LocalTypeSuffix(classType) => LocalTypeSuffix(substitute(classType, typeVars, consistencyVars))
    }

    def substitute(typ: ClassType, typeVars: TypeVarEnv, consistencyVars: ConsistencyVarEnv): ClassType =
        ClassType(typ.classId,
            typ.consistencyArguments.map(t => substitute(t, consistencyVars)),
            typ.typeArguments.map(t => substitute(t, typeVars, consistencyVars)))

    def substitute(typ: ConsistencyType, consistencyVars: ConsistencyVarEnv): ConsistencyType = typ match {
        case consistencyType: ConcreteConsistencyType => consistencyType
        case ConsistencyVar(name) => consistencyVars.get(name) match {
            case Some(value) => value
            case None => ConsistencyVar(name)
        }
    }
}