package de.tuda.stg.consys.invariants.lang.solver

import com.microsoft.z3.{ArithSort, DatatypeSort, Sort, TupleSort, Context => Z3Context, Expr => Z3Expr}
import de.tuda.stg.consys.invariants.lang.ast.Type
import de.tuda.stg.consys.invariants.lang.ast.Type._


trait TypeTranslator { this : BaseTranslator =>

  def translateType(typ : Type) : Sort = typ match {
    case TBool => context.getBoolSort
    case TInt => context.getIntSort
    case TUnit => context.mkSeqSort(context.getIntSort)
    case TRef(c) => ???
    case TPair(t1, t2) => ???
    case TSet(t) => context.mkSetSort(translateType(t))
    case TString => context.getStringSort
  }

}
