package de.tuda.stg.consys.invariants.lang.solver

import com.microsoft.z3.{ArithSort, DatatypeSort, Sort, TupleSort, Context => Z3Context, Expr => Z3Expr}
import de.tuda.stg.consys.invariants.lang.{ClassId, ClassTable}


trait BaseTranslator {
  def context : Z3Context

  private case class TranslationError(msg : String) extends Exception(msg)

  private[solver] def error(msg : String) : Nothing =
    throw TranslationError(msg)
}

object BaseTranslator {

  def loadLibs() : Unit = {
    System.load("/usr/lib/jni/libz3.so")
    System.load("/usr/lib/jni/libz3java.so")
  }
}