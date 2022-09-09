package de.tuda.stg.consys.invariants.lang


import de.tuda.stg.consys.invariants.lang.ast.Expression._
import de.tuda.stg.consys.invariants.lang.ast.Statement._
import de.tuda.stg.consys.invariants.lang.ast.Type._
import de.tuda.stg.consys.invariants.lang.ast.{ASTNode, Expression, Statement, Type}

object TypeSystem {

  type TypeEnv = Map[VarId, Type]
  type TypeMap = Map[Expression, Type]

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
    def flatMap(f : Type => TypeResult) : TypeResult = {

      val res = f(typ)
      val r = TypeResult(res.typ, res.typeMap ++ typeMap)
      println("flatMap = " + r)
      r
    }

    def >>=(f : Type => TypeResult) : TypeResult =
      flatMap(f)

    def map(f : Type => Type) : TypeResult = {

      val r = TypeResult(f(typ), typeMap)
      println("map = " + r)
      r
    }
  }

  def unit(value : Val, t : Type) : TypeResult = TypeResult(t, Map(value -> t))


  def checkValM(value : Val) : TypeResult = value match {
    case VInt(_) => unit(value, TInt)

    case VPair(x1, x2) =>
      for {
        t1 <- checkValM(x1)
        t2 <- checkValM(x2)
      } yield TPair(t1, t2)

//      checkValM(x1) >>= {
//        t1 => checkValM(x2) >>= {
//          t2 => unit(value, TPair(t1, t2))
//        }
//      }
  }


  def checkVal(value : Val) : Type = value match {
    case VUnit => TUnit
    case VBool(_) => TBool
    case VInt(_) => TInt

    case VSet(typ, xs) =>
      xs.foreach(x => {
        val t = checkVal(x)
        if (!(t <= typ)) error(s"wrong element type in set of type $typ: $t")
      })
      TSet(typ)

    case VPair(x1, x2) =>
      val t1 = checkVal(x1)
      val t2 = checkVal(x2)
      TPair(t1, t2)

    case VRef(cls, refId) => TRef(cls)
  }

  def checkExpr(env : TypeEnv, expr : Expression) : Type = expr match {
    case v : Val => checkVal(v)

    case EVar(x) => env.getOrElse(x, error("variable not bound: " + x))

    case ELet(x, namedExpr, body) =>
      val t = checkExpr(env, namedExpr)
      checkExpr(env + (x -> t), body)

    case EPair(e1, e2) =>
      val t1 = checkExpr(env, e1)
      val t2 = checkExpr(env, e2)
      TPair(t1, t2)

    case EPlus(e1, e2) =>
      val t1 = checkExpr(env, e1)
      if (t1 != TInt) error(s"expected TInt in +, but got: $e1 (of type $t1)")

      val t2 = checkExpr(env, e2)
      if (t2 != TInt) error(s"expected TInt in +, but got: $e2 (of type $t2)")

      TInt

    case EFst(expr) =>
      checkExpr(env, expr) match {
        case TPair(t1, t2) => t1
        case t => error(s"expected TPair, but got: $expr (of type $t)")
      }

    case e : ESnd =>
      checkExpr(env, expr) match {
        case TPair(t1, t2) => t2
        case t => error(s"expected TPair, but got: $expr (of type $t)")
      }
  }

  def checkStmt(ct : ClassTable, env : TypeEnv, stmt : Statement) : Unit = stmt match {
    case Return(expr) =>
      checkExpr(env, expr)

    case DoNew(x, cls, fields, body) =>
      // Check that the class exists
      val clsDef = ct.getOrElse(cls, error(s"unknown class: $cls"))

      // Check the arguements
      val fieldTypes = fields.map(e => checkExpr(env, e))
      val clsFieldTypes = clsDef.fields.map(fDef => fDef.typ)

      // Check that the field names match
      if (clsFieldTypes.length != fieldTypes.length) error(s"wrong number of fields, expected: $clsFieldTypes, but got: $fieldTypes")
      // Check that the argument types match
      clsFieldTypes.zip(fieldTypes).foreach(tt => if (!(tt._2 <= tt._1))
        error(s"wrong type for field, expected: ${tt._1}, but was: ${tt._2}")
      )

      checkStmt(ct, env + (x -> TRef(cls)), body)


    case DoGetField(x, field, body) =>
      env.getOrElse(thsId, error(s"access to field $field only possible in class context")) match {
        case TRef(c) =>
          val clsDef = ct.getOrElse(c, error(s"unknown class: $c"))
          val fieldDef = clsDef.fields.find(fDef => fDef.name == field).getOrElse(error(s"unknown field in class $c: $field"))

          checkStmt(ct, env + (x -> fieldDef.typ), body)

        case t => error(s"expected TRef for $$this, but got: $t")
      }

    case DoSetField(x, f, e, body) =>
      env.getOrElse(thsId, error(s"access to field only possible in class context, field was: $f")) match {
        case TRef(c) =>
          val clsDef = ct.getOrElse(c, error(s"unknown class: $c"))
          val fieldDef = clsDef.fields.find(fDef => fDef.name == f).getOrElse(error(s"unknown field in class $c: $f"))

          val eType = checkExpr(env, e)
          if (!(eType <= fieldDef.typ)) error(s"type mismatch assigning to $f, expected: ${fieldDef.typ}, but was: $eType")

          checkStmt(ct, env + (x -> eType), body)

        case t => error(s"expected TRef for $$this, but got: $t")
      }

    case DoCallMethod(x, recv, m, args, body) =>
      checkExpr(env, recv) match {
        case recvType@TRef(c) =>
          val clsDef = ct.getOrElse(c, error(s"unknown class: $c"))
          val methodDef = clsDef.methods.find(mDef => mDef.name == m).getOrElse(error(s"unknown method in class $c: $m"))

          val argTypes = args.map(e => checkExpr(env, e))
          val methodArgTypes = methodDef.parameters.map(v => v.typ)

          if (argTypes.size != methodArgTypes.size) error(s"wrong number of arguments for method $m, expected: $methodArgTypes, but got: $argTypes")
          argTypes.zip(methodArgTypes).foreach(tt => if (!(tt._1 <= tt._2)) error(s"wrong argument type for method $m, expected: ${tt._2}, but was: ${tt._1}"))

          checkStmt(ct, env + (x -> methodDef.typ), body)


        case t => error(s"expected TRef for $recv, but got: $t")
      }
   }

  def checkClass(ct : ClassTable, cls : ClassDef) : Unit = {
    cls.fields.foldLeft(Set.empty[FieldId])((ids, fDef) => {
      if (ids.contains(fDef.name)) error(s"field already defined in ${cls.name}: ${fDef.name}")
      ids + fDef.name
    })

    cls.methods.foldLeft(Set.empty[MethodId])((ids, mDef) => {
      if (ids.contains(mDef.name)) error(s"method already defined in ${cls.name}: ${mDef.name}")
      ids + mDef.name
    })

    cls.methods.foreach(mDef => {
      checkStmt(ct, Map(thsId -> TRef(cls.name)), mDef.body)
    })
  }

  def checkClassTable(ct : ClassTable) : Unit = {
    ct.classes.foldLeft(Set.empty[ClassId])((ids, cDef) => {
      if (ids.contains(cDef.name)) error(s"class already defined: ${cDef.name}")
      ids + cDef.name
    })

    ct.classes.foreach(cls => checkClass(ct, cls))
  }

  def checkProg(prog : Program) : Unit = {
    checkClassTable(prog.ct)
    prog.txs.foreach(tx => checkStmt(prog.ct, Map(), tx.stmt))
  }

}
