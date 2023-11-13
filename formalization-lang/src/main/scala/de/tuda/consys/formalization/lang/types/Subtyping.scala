package de.tuda.consys.formalization.lang.types

import de.tuda.consys.formalization.lang.ClassTable.ClassTable
import de.tuda.consys.formalization.lang.{ClassTable, ConsistencyVarEnv, TypeVarEnv, topClassId, types}

import scala.annotation.tailrec

object Subtyping {
    def subtype(t1: Type, t2: Type)
               (implicit ct: ClassTable,
                typeVarEnv: TypeVarEnv,
                consistencyVarEnv: ConsistencyVarEnv): Boolean = {
        subtype(t1.l, t2.l) && subtype(t1.m, t2.m) && subtype(t2.m, t1.suffix, t2.suffix)
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
                    subtype(m, bound, t2) // TS-Trans TODO: transitive mut
            case (s1, s2) => s1 == s2 // TODO
            case _ => false
        }

    @tailrec
    def subtype(m: MutabilityType, t1: ClassType, t2: ClassType)
               (implicit ct: ClassTable, typeVarEnv: TypeVarEnv, consistencyVarEnv: ConsistencyVarEnv): Boolean = {
        if (t2.classId == topClassId) // S-Top
            return true

        if (t1 == t2) // S-Refl
            return true

        val supertype = ClassTable.getSuperType(t1)
        if (supertype == t2) // S-Super
            return true

        val covariant =
            m == Immutable &&
            t1.classId == t2.classId &&
            t1.typeArguments == t2.typeArguments &&
            (t1.consistencyArguments zip t2.consistencyArguments).forall(p => p._1 <= p._2)
        if (covariant)
            return true

        subtype(m, t2, ClassTable.getSuperType(t1)) // S-Trans TODO: transitive mut
    }

    // TODO: algorithmic rule not correct, theres more cases with unions
    def subtype(t1: ConsistencyType, t2: ConsistencyType)(implicit consistencyVarEnv: ConsistencyVarEnv): Boolean = {
        (t1, t2) match {
            case (Local, _) => true
            case (_, Inconsistent) => true
            case (t1: ConcreteConsistencyType, t2: ConcreteConsistencyType) =>
                ConsistencyTypeLattice(t1).hasUpperBound(t2)
            case (v, v2@ConsistencyUnion(t1, t2)) =>
                v == v2 || (subtype(v, t1) || subtype(v, t2))
            case (v2@ConsistencyUnion(t1, t2), v) =>
                v == v2 || (subtype(t1, v) && subtype(t2, v))
            case (ConsistencyVar(_), t2) =>
                val bound = Types.bound(t1)
                t1 == t2 || // L-Refl
                    bound == t2 || // L-Var
                    subtype(bound, t2) // L-Trans
            case _ => false
        }
    }

    def subtype(t1: MutabilityType, t2: MutabilityType): Boolean = MutabilityTypeLattice(t1).hasUpperBound(t2)
}
