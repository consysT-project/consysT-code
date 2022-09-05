package de.tuda.stg.consys.invariants.lang

import de.tuda.stg.consys.invariants.lang.Expr._
import de.tuda.stg.consys.invariants.lang.Stmt.{DoCallMethod, DoGetField, DoNew, DoSetField, Return}
import de.tuda.stg.consys.invariants.lang.Type._

object TypeSystem {

  def isSubtypeOf(t1 : Type, t2 : Type) : Boolean =
    t1 == t2

  implicit class TypeOps(t1 : Type) {
    def <=(t2 : Type) : Boolean = isSubtypeOf(t1, t2)
  }

  private case class TypeError(msg : String) extends Exception(msg)

  private def error(msg : String) : Nothing =
    throw TypeError(msg)

  def checkExpr(env : TypeEnv, expr : Expr) : Type = expr match {
    case UnitVal => TUnit
    case BoolVal(_) => TBool
    case IntVal(_) => TInt
    case SetVal(t, _) => TSet(t)
    case PairVal(x1, x2) =>
      val t1 = checkExpr(env, x1)
      val t2 = checkExpr(env, x2)
      TPair(t1, t2)
    case RefVal(c, _) => TRef(c)

    case Var(x) =>
      env.getOrElse(x, error("variable not bound: " + x))

    case LetExpr(x, e, body) =>
      val t = checkExpr(env, e)
      checkExpr(env + (x -> t), body)

    case PairExpr(e1, e2) =>
      val t1 = checkExpr(env, e1)
      val t2 = checkExpr(env, e2)
      TPair(t1, t2)

    case PlusOp(e1, e2) =>
      val t1 = checkExpr(env, e1)
      if (t1 != TInt) error(s"expected TInt in +, but got: $e1 (of type $t1)")

      val t2 = checkExpr(env, e2)
      if (t2 != TInt) error(s"expected TInt in +, but got: $e2 (of type $t2)")

      TInt

    case FstOp(e) =>
      checkExpr(env, e) match {
        case TPair(t1, t2) => t1
        case t => error(s"expected TPair, but got: $e (of type $t)")
      }

    case SndOp(e) =>
      checkExpr(env, e) match {
        case TPair(t1, t2) => t1
        case t => error(s"expected TPair, but got: $e (of type $t)")
      }
  }

  def checkStmt(ct : ClsTable, env : TypeEnv, stmt : Stmt) : Unit = stmt match {
    case Return(e) => checkExpr(env, e)

    case DoNew(x, c, fields, body) =>
      // Check that the class exists
      val clsDef = ct.getOrElse(c, error(s"unknown class: $c"))

      // Check the arguements
      val fieldTypes = fields.map(f => (f._1, checkExpr(env, f._2)))
      val clsFieldTypes = clsDef.fields.map(f => (f._1, f._2.t))

      // Check that the field names match
      if (clsFieldTypes.keys != fieldTypes.keys) error(s"incompatible fields, expected: $clsFieldTypes, but got: $fieldTypes")
      // Check that the argument types match
      clsFieldTypes.foreach(f1Entry => {
        val f2 = fieldTypes(f1Entry._1)
        if (!(f2 <= f1Entry._2)) error(s"wrong type for field ${f1Entry._1}, expected: ${f1Entry._2}, but was: $f2")
      })

      checkStmt(ct, env + (x -> TRef(c)), body)

    case DoGetField(x, f, body) =>
      env.getOrElse(thsId, error(s"access to field only possible in class context, field was: $f")) match {
        case TRef(c) =>
          val clsDef = ct.getOrElse(c, error(s"unknown class: $c"))
          val fieldDef = clsDef.fields.getOrElse(f, error(s"unknown field in class $c: $f"))

          checkStmt(ct, env + (x -> fieldDef.t), body)

        case t => error(s"expected TRef for $$this, but got: $t")
      }

    case DoSetField(x, f, e, body) =>
      env.getOrElse(thsId, error(s"access to field only possible in class context, field was: $f")) match {
        case TRef(c) =>
          val clsDef = ct.getOrElse(c, error(s"unknown class: $c"))
          val fieldDef = clsDef.fields.getOrElse(f, error(s"unknown field in class $c: $f"))

          val eType = checkExpr(env, e)
          if (eType <= fieldDef.t) error(s"type mismatch assigning to $f, expected: ${fieldDef.t}, but was: $eType")

          checkStmt(ct, env + (x -> fieldDef.t), body)

        case t => error(s"expected TRef for $$this, but got: $t")
      }

    case DoCallMethod(x, recv, m, args, body) =>
      checkExpr(env, recv) match {
        case recvType@TRef(c) =>
          val clsDef = ct.getOrElse(c, error(s"unknown class: $c"))
          val methodDef = clsDef.methods.getOrElse(m, error(s"unknown method in class $c: $m"))

          val argTypes = args.map(e => checkExpr(env, e))
          val methodArgTypes = methodDef.pars.map(v => v.t)

          if (argTypes.size != methodArgTypes.size) error(s"wrong number of arguments for method $m, expected: $methodArgTypes, but got: $argTypes")
          argTypes.zip(methodArgTypes).foreach(tt => if (!(tt._1 <= tt._2)) error(s"wrong argument type for method $m, expected: ${tt._2}, but was: ${tt._1}"))

          checkStmt(ct, env + (x -> methodDef.t) + (thsId -> recvType), body)


        case t => error(s"expected TRef for $recv, but got: $t")
      }
   }

  def checkProg( prog : Prog) : Unit = {
    prog.txs.foreach(tx => {
      checkStmt(prog.ct, Map(), tx.stmt)
    })
  }

}
