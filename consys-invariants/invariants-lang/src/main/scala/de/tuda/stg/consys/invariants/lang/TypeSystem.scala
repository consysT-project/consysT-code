package de.tuda.stg.consys.invariants.lang


import com.datastax.oss.driver.api.core.loadbalancing.NodeDistance
import de.tuda.stg.consys.invariants.lang.ast.ASTNode.NodeId
import de.tuda.stg.consys.invariants.lang.ast.Expression._
import de.tuda.stg.consys.invariants.lang.ast.Statement._
import de.tuda.stg.consys.invariants.lang.ast.Type._
import de.tuda.stg.consys.invariants.lang.ast.{ASTNode, Expression, Statement, Type}

object TypeSystem {

  type TypeEnv = Map[VarId, Type]
  type TypeMap = Map[NodeId, Type]

  def isSubtypeOf(t1 : Type, t2 : Type) : Boolean = (t1, t2) match {
    case (_, TAny) => true
    case (TSet(a), TSet(b)) => isSubtypeOf(a, b)
    case (TPair(a1, a2), TPair(b1, b2)) => isSubtypeOf(a1, b1) && isSubtypeOf(a2, b2)
    case (a1, a2) if a1 == a2 => true
    case _ => false
  }

  implicit class TypeOps(t1 : Type) {
    def <=(t2 : Type) : Boolean = isSubtypeOf(t1, t2)
  }

  private case class TypeError(msg : String) extends Exception(msg)

  private def error(msg : String) : Nothing =
    throw TypeError(msg)


  case class TypeResult(typ : Type, typeMap : TypeMap) {
    def join(other : TypeResult, newExpr : Expression, f : (Type, Type) => Type) : TypeResult = {
      val newType = f(typ, other.typ)
      TypeResult(newType, (typeMap ++ other.typeMap) + (newExpr.nodeId -> newType))
    }
  }


  private def unit(expr : Expression, typ : Type) : TypeResult = TypeResult(typ, Map(expr.nodeId -> typ))



  def checkVal(value : Val) : TypeResult = value match {
    case VUnit => unit(value, TUnit)
    case VBool(_) => unit(value, TBool)
    case VInt(_) => unit(value, TInt)

    case VSet(typ, xs) =>
      val map = xs.foldLeft(Map.empty[NodeId, Type])((typeMap, x) => {
        val xResult = checkVal(x)
        if (!(xResult.typ <= typ)) error(s"wrong element type in set of type $typ: ${xResult.typ}")

        typeMap ++ xResult.typeMap
      })
      TypeResult(TSet(typ), map)

    case VPair(x1, x2) =>
      val r1 = checkVal(x1)
      val r2 = checkVal(x2)
      r1.join(r2, value, (t1, t2) => TPair(t1, t2))


    case VRef(cls, refId) => unit(value, TRef(cls))

    case VString(_) => unit(value, TString)
  }

  def checkExpr(ct : ClassTable, env : TypeEnv, expr : Expression) : TypeResult = expr match {
    case v : Val => checkVal(v)

    case EVar(x) =>
      unit(expr, env.getOrElse(x, error("variable not bound: " + x)))

    case EField(f) =>
      env.getOrElse(thsId, error(s"access to field only possible in class context, field was: $f")) match {
        case TRef(c) =>
          val clsDef = ct.getOrElse(c, error(s"unknown class: $c"))
          val fldDef = clsDef.getField(f).getOrElse(error(s"unknown field in class $c: $f"))
          unit(expr, fldDef.typ)

        case t => error(s"expected TRef for $$this, but got: $t")
      }


    case ELet(x, namedExpr, body) =>
      val tr = checkExpr(ct, env, namedExpr)
      tr.join(checkExpr(ct, env + (x -> tr.typ), body), expr, (t1, t2) => t2)

    case EPair(e1, e2) =>
      val r1 = checkExpr(ct, env, e1)
      val r2 = checkExpr(ct, env, e2)
      r1.join(r2, expr, (t1, t2) => TPair(t1, t2))

    case EPlus(e1, e2) =>
      val r1 = checkExpr(ct, env, e1)
      if (r1.typ != TInt) error(s"expected TInt in +, but got: $e1 (of type ${r1.typ})")

      val r2 = checkExpr(ct, env, e2)
      if (r2.typ != TInt) error(s"expected TInt in +, but got: $e2 (of type ${r2.typ})")

      r1.join(r2, expr, (_, _) => TInt)

    case EFst(e) =>
      checkExpr(ct, env, e) match {
        case TypeResult(TPair(t1, t2), map) => TypeResult(t1, map + (expr.nodeId -> t1))
        case t => error(s"expected TPair, but got: $expr (of type ${t.typ})")
      }

    case ESnd(e) =>
      checkExpr(ct, env, e) match {
        case TypeResult(TPair(t1, t2), map) => TypeResult(t2, map + (expr.nodeId -> t2))
        case t => error(s"expected TPair, but got: $expr (of type ${t.typ})")
      }
  }

  def checkStmt(ct : ClassTable, env : TypeEnv, stmt : Statement) : TypeMap = stmt match {
    case Return(expr) =>
      checkExpr(ct, env, expr).typeMap

    case DoNew(x, cls, fields, body) =>
      // Check that the class exists
      val clsDef = ct.getOrElse(cls, error(s"unknown class: $cls"))

      // Check the arguements
      val fieldTypeResults = fields.map(e => checkExpr(ct, env, e))
      val clsFieldTypes = clsDef.fields.map(fDef => fDef.typ)

      // Check that the field names match
      if (clsFieldTypes.length != fieldTypeResults.length) error(s"wrong number of fields, expected: ${clsFieldTypes.length}, but got: ${fieldTypeResults.length}")
      // Check that the argument types match
      clsFieldTypes.zip(fieldTypeResults).foreach(tt => if (!(tt._2.typ <= tt._1))
        error(s"wrong type for field, expected: ${tt._1}, but was: ${tt._2}")
      )

      val typeMap = checkStmt(ct, env + (x -> TRef(cls)), body)
      typeMap ++ fieldTypeResults.flatMap(r => r.typeMap)


    case DoExpr(x, expr, body) =>
      val tr1 = checkExpr(ct, env, expr)
      val map2 = checkStmt(ct, env + (x -> tr1.typ), body)

      tr1.typeMap ++ map2

    case DoSetField(x, f, e, body) =>
      env.getOrElse(thsId, error(s"access to field only possible in class context, field was: $f")) match {
        case TRef(c) =>
          val clsDef = ct.getOrElse(c, error(s"unknown class: $c"))
          val fieldDef = clsDef.getField(f).getOrElse(error(s"unknown field in class $c: $f"))

          val fieldTypeResult = checkExpr(ct, env, e)
          if (!(fieldTypeResult.typ <= fieldDef.typ)) error(s"type mismatch assigning to $f, expected: ${fieldDef.typ}, but was: $fieldTypeResult")

          val typeMap = checkStmt(ct, env + (x -> fieldTypeResult.typ), body)
          typeMap ++ fieldTypeResult.typeMap

        case t => error(s"expected TRef for $$this, but got: $t")
      }

    case DoCallMethod(x, recv, m, args, body) =>
      checkExpr(ct, env, recv) match {
        case TypeResult(TRef(c), map) =>
          val clsDef = ct.getOrElse(c, error(s"unknown class: $c"))
          val methodDef = clsDef.getMethod(m).getOrElse(error(s"unknown method in class $c: $m"))

          val argTypeResults = args.map(e => checkExpr(ct, env, e))
          val methodArgTypes = methodDef.parameters.map(v => v.typ)

          if (argTypeResults.size != methodArgTypes.size) error(s"wrong number of arguments for method $m, expected: $methodArgTypes, but got: $argTypeResults")
          argTypeResults.zip(methodArgTypes).foreach(tt => if (!(tt._1.typ <= tt._2)) error(s"wrong argument type for method $m, expected: ${tt._2}, but was: ${tt._1}"))

          val typeMap = checkStmt(ct, env + (x -> methodDef.typ), body)
          typeMap ++ map ++ argTypeResults.flatMap(r => r.typeMap)

        case t => error(s"expected TRef for $recv, but got: $t")
      }
   }

  def checkClass(ct : ClassTable, cls : ClassDef) : TypeMap = {
    cls.fields.foldLeft(Set.empty[FieldId])((ids, fDef) => {
      if (ids.contains(fDef.name)) error(s"field already defined in ${cls.name}: ${fDef.name}")
      ids + fDef.name
    })

    cls.methods.foldLeft(Set.empty[MethodId])((ids, mDef) => {
      if (ids.contains(mDef.name)) error(s"method already defined in ${cls.name}: ${mDef.name}")
      ids + mDef.name
    })

    cls.methods.foldLeft(Map.empty[NodeId, Type])((typeMap, mDef) => {
      typeMap ++ checkStmt(ct, Map(thsId -> TRef(cls.name)), mDef.body)
    })
  }

  def checkClassTable(ct : ClassTable) : TypeMap = {
    ct.classes.foldLeft(Set.empty[ClassId])((ids, cDef) => {
      if (ids.contains(cDef.name)) error(s"class already defined: ${cDef.name}")
      ids + cDef.name
    })

    ct.classes.foldLeft(Map.empty[NodeId, Type])((typeMap, cls) =>
      typeMap ++ checkClass(ct, cls))
  }

  def checkProg(prog : Program) : TypeMap = {
    val classMap = checkClassTable(prog.ct)
    val txMap = prog.txs.foldLeft(Map.empty[NodeId, Type])((typeMap, tx) =>
      typeMap ++ checkStmt(prog.ct, Map(), tx.stmt))

    txMap ++ classMap
  }

}
