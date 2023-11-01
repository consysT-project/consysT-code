package de.tuda.consys.invariants.solver.next.ir

import de.tuda.consys.invariants.solver.next.ir.Classes.{ClassDecl, ClassId, MethodDecl, NativeClassDecl, ObjectClassDecl}
import de.tuda.consys.invariants.solver.next.ir.Expressions.BaseExpressions

class ClassTable[Expr <: BaseExpressions#Expr](private val classes : Map[ClassId, Either[NativeClassDecl, ObjectClassDecl[Expr]]]) {
  def values : Iterable[Either[NativeClassDecl, ObjectClassDecl[Expr]]] = classes.values

  def getOrElse(classId : ClassId, any : => ClassDecl[_ <: MethodDecl]) : ClassDecl[_ <: MethodDecl] =
    classes.get(classId) match {
      case Some(Left(nativeClassDecl)) => nativeClassDecl
      case Some(Right(objectClassDecl)) => objectClassDecl
      case None => any
    }
}

object ClassTable {
  def apply[Expr <: BaseExpressions#Expr](elems: (ClassId, Either[NativeClassDecl, ObjectClassDecl[Expr]])*) : ClassTable[Expr] =
    new ClassTable[Expr](Map(elems : _*))

}
