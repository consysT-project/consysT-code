package de.tuda.consys.formalization.lang.types

import de.tuda.consys.formalization.lang.ClassTable.ClassTable
import de.tuda.consys.formalization.lang.{ClassTable, ConsistencyVarEnv, TypeVarEnv, topClassId, types}

import scala.annotation.tailrec

object Subtyping {
    def subtype(t1: Type, t2: Type)
               (implicit ct: ClassTable,
                typeVarEnv: TypeVarEnv,
                consistencyVarEnv: ConsistencyVarEnv): Boolean = {
        t2.m match {
            case Mutable => t1.l == t2.l && t1.m == Mutable && subtype(Mutable, t1.suffix, t2.suffix)
            case Immutable => t1.l <= t2.l && t1.m <= t2.m && subtype(Immutable, t1.suffix, t2.suffix)
        }
    }

    @tailrec
    def subtype(m: MutabilityType, t1: TypeSuffix, t2: TypeSuffix)
               (implicit ct: ClassTable, typeVarEnv: TypeVarEnv, consistencyVarEnv: ConsistencyVarEnv): Boolean =
        (t1, t2) match {
            case (RefTypeSuffix(classType1), RefTypeSuffix(classType2)) => subtype(m, classType1, classType2)
            case (LocalTypeSuffix(classType1), LocalTypeSuffix(classType2)) => subtype(m, classType1, classType2)
            case (TypeSuffixVar(_), t2) =>
                val bound = Types.bound(t1)
                t1 == t2 || // TS-Refl
                    bound == t2 || // TS-Var
                    subtype(m, bound, t2) // TS-Trans
            case _ => false
        }

    def subtype(m: MutabilityType, t1: ClassType, t2: ClassType)
               (implicit ct: ClassTable, typeVarEnv: TypeVarEnv, consistencyVarEnv: ConsistencyVarEnv): Boolean = {
        val top = t2.classId == topClassId
        val reflexive = t1 == t2
        val superclass = ClassTable.getSuperType(t1) == t2
        val covariant =
            m == Immutable &&
            t1.classId == t2.classId &&
            t1.typeArguments == t2.typeArguments &&
            (t1.consistencyArguments zip t2.consistencyArguments).forall(p => p._1 <= p._2)

        top || reflexive || superclass || covariant
    }

    @tailrec
    def subtype(t1: ConsistencyType, t2: ConsistencyType)(implicit consistencyVarEnv: ConsistencyVarEnv): Boolean = {
        (t1, t2) match {
            case (t1: ConcreteConsistencyType, t2: ConcreteConsistencyType) =>
                ConsistencyTypeLattice(t1).hasUpperBound(t2)
            case (ConsistencyVar(_), t2) =>
                val bound = Types.bound(t1)
                t1 == t2 || // L-Refl
                    bound == t2 || // L-Var
                    subtype(bound, t2) // L-Trans
            case _ => false
        }
    }

    def subtype(t1: MutabilityType, t2: MutabilityType): Boolean = MutabilityTypeLattice(t1).hasUpperBound(t2)

    def lub(t1: (ConsistencyType, MutabilityType),
            t2: (ConsistencyType, MutabilityType))(implicit ct: ClassTable,
                                                   varEnv: TypeVarEnv,
                                                   cEnv: ConsistencyVarEnv): (ConsistencyType, MutabilityType) = {
        val (c1, m1) = t1
        val (c2, m2) = t2
        // lub between two distinct types can only ever be Immutable
        (m1, m2) match {
            case (Mutable, Mutable) if c1 == c2 => (c1, Mutable)
            case _ => (c1 lub c2, Immutable)
        }
    }
}
