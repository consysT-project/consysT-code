package de.tuda.consys.formalization.lang.types

import de.tuda.consys.formalization.lang.ClassTable.ClassTable
import de.tuda.consys.formalization.lang.{ClassTable, ConsistencyVarEnv, TypeVarEnv, TypeVarMutabilityEnv, topClassId, types}

import scala.annotation.tailrec

object Subtyping {
    def subtype(t1: Type, t2: Type)
               (implicit ct: ClassTable,
                typeVarEnv: TypeVarEnv,
                typeVarMutabilityEnv: TypeVarMutabilityEnv,
                consistencyVarEnv: ConsistencyVarEnv): Boolean = {
        subtype(t1.l, t2.l) && subtype(t1.m, t2.m) && subtype(t2.m, t1.suffix, t2.suffix)
    }

    def subtype(m: MutabilityType, t1: TypeSuffix, t2: TypeSuffix)
               (implicit ct: ClassTable,
                typeVarEnv: TypeVarEnv,
                typeVarMutabilityEnv: TypeVarMutabilityEnv,
                consistencyVarEnv: ConsistencyVarEnv): Boolean =
        (t1, t2) match {
            case (RefTypeSuffix(classType1), RefTypeSuffix(classType2)) => subtype(m, classType1, classType2)
            case (LocalTypeSuffix(classType1), LocalTypeSuffix(classType2)) if m == Immutable => subtype(m, classType1, classType2)
            case (v@TypeSuffixVar(_), t2) =>
                val bound = Types.bound(t1)
                val mBound = Types.mBound(v)
                val vs = t1 == t2 || // TS-Refl
                    (bound == t2 && mBound <= m) || // TS-Var & TS-Trans
                    subtype(m, bound, t2) // TS-Trans
                if (m == Mutable)
                    vs || subtype(Mutable, bound, t2)
                else
                    vs || subtype(Mutable, bound, t2) || subtype(Immutable, bound, t2)
            case (s1, s2) => s1 == s2 // TS-Refl
            case _ => false
        }

    def subtype(m: MutabilityType, t1: ClassType, t2: ClassType)
               (implicit ct: ClassTable,
                typeVarEnv: TypeVarEnv,
                typeVarMutabilityEnv: TypeVarMutabilityEnv,
                consistencyVarEnv: ConsistencyVarEnv): Boolean = {
        if (t2.classId == topClassId) // S-Top
            return true

        if (t1.classId == topClassId && t1 != t2)
            return false

        if (t1 == t2) // S-Refl
            return true

        val covariant = // S-Covariant
            m == Immutable &&
                t1.classId == t2.classId &&
                (t1.typeArguments zip t2.typeArguments).forall(p => subtype(Immutable, p._1, p._2)) &&
                (t1.consistencyArguments zip t2.consistencyArguments).forall(p => p._1 <= p._2)
        if (covariant)
            return true

        val supertype = ClassTable.getSuperType(t1)
        if (m == Mutable) // S-Trans & S-Super
            subtype(Mutable, supertype, t2)
        else
            subtype(Mutable, supertype, t2) || subtype(Immutable, supertype, t2)
    }

    def subtype(t1: ConsistencyType, t2: ConsistencyType)(implicit consistencyVarEnv: ConsistencyVarEnv): Boolean = {
        (t1, t2) match {
            case (Local, _) => true
            case (_, Inconsistent) => true
            case (t1: ConcreteConsistencyType, t2: ConcreteConsistencyType) =>
                ConsistencyTypeLattice(t1).hasUpperBound(t2) // includes trans and refl rules
            case (ConsistencyVar(_), t2) =>
                val bound = Types.bound(t1)
                val union = t2 match {
                    case ConsistencyUnion(u1, u2) => subtype(t1, u1) || subtype(t1, u2)
                    case _ => false
                }
                t1 == t2 || // L-Refl
                    bound == t2 || // L-Var
                    subtype(bound, t2) || // L-Trans
                    union
            case (ConsistencyUnion(u1, u2), _) =>
                t1 == t2 || (subtype(u1, t2) && subtype(u2, t2))
            case (_, ConsistencyUnion(u1, u2)) =>
                t1 == t2 || (subtype(t1, u1) || subtype(t1, u2))
            case _ => false
        }
    }

    def subtype(t1: MutabilityType, t2: MutabilityType): Boolean = MutabilityTypeLattice(t1).hasUpperBound(t2)
}
