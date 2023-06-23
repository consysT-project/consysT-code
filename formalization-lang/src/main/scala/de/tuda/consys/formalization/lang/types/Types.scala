package de.tuda.consys.formalization.lang.types

import de.tuda.consys.formalization.lang.{ClassId, TypeVarId}

sealed trait Type {
    def <=(t: Type): Boolean

    def !<=(t: Type): Boolean = !this.<=(t)

    def >=(t: Type): Boolean

    def !>=(t: Type): Boolean = !this.>=(t)

    def lub(t: Type): Type

    def glb(t: Type): Type

    def effectiveType(): CompoundType
}

case class ClassType(classId: ClassId, typeArguments: Seq[Type]) {
    override def toString: ClassId = if (typeArguments.isEmpty) s"$classId" else s"$classId<${typeArguments.mkString(",")}>"
}

case class CompoundType(classType: ClassType, consistencyType: ConsistencyType, mutabilityType: MutabilityType) extends Type {
    if (mutabilityType == Bottom && consistencyType != Local)
        sys.error("invalid bottom type")

    def <=(t: Type): Boolean = t match {
        case CompoundType(baseType1, consistencyType1, mutabilityType1) =>
            if (classType != baseType1)
                false // TODO: inheritance
            else if (consistencyType == Local && mutabilityType == Bottom) // TODO
                true
            else if (mutabilityType1 == Immutable)
                mutabilityType <= mutabilityType1 && consistencyType <= consistencyType1
            else
                mutabilityType <= mutabilityType1 && consistencyType == consistencyType1
        case _ => false
    }

    def >=(t: Type): Boolean = t match {
        case CompoundType(baseType, consistencyType, mutabilityType) => this == t || !(this <= t)
        case _ => false
    }

    def lub(t: Type): Type = t match {
        case CompoundType(baseType, consistencyType, mutabilityType) => ???
        case _ => ???
    }

    def glb(t: Type): Type = t match {
        case CompoundType(baseType, consistencyType, mutabilityType) => ???
        case _ => ???
    }

    def effectiveType(): CompoundType = this

    override def toString: ClassId = s"$mutabilityType $consistencyType $classType"
}

case class TypeVar(typeVarId: TypeVarId, upperBound: Type) extends Type {
    def <=(t: Type): Boolean = ???

    def >=(t: Type): Boolean = ???

    def lub(t: Type): Type = ???

    def glb(t: Type): Type = ???

    def effectiveType(): CompoundType = upperBound match {
        case t@CompoundType(_, _, _) => t
        case t@TypeVar(_, _) => t.effectiveType()
        case _ => ???
    }

    override def toString: ClassId = s"$typeVarId <: $upperBound"
}
