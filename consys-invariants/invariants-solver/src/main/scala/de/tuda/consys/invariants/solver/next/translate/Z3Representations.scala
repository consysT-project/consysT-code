package de.tuda.consys.invariants.solver.next.translate

import com.microsoft.z3.{BoolSort, FuncDecl, Sort, TupleSort}
import de.tuda.consys.invariants.solver.next.ir.Classes.{ClassId, FieldId, MethodId, Type, TypeVarId}

import scala.collection.mutable


object Z3Representations {

	class CachedMap[A, B](f : A => B, entries : Map[A, B] = Map.empty[A, B]) extends (A => B) {
		private val cache : mutable.Map[A, B] = mutable.Map.empty
		cache.addAll(entries)

		override def apply(v1 : A) : B =
			cache.getOrElseUpdate(v1, f(v1))
	}
}
