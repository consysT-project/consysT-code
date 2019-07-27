package de.tuda.stg.consys.process

/**
	* Created on 24.07.19.
	*
	* @author Mirko Köhler
	*/
trait SimpleProcessReduction { lang : ExtendedProcessLanguage =>

	case class Obj(cls : Cls, lab : Lab, fields : Map[Fld, Value])

	override type Cls = FunCls
	case class FunCls(fields : Set[Fld], methods : Map[Method, (Obj, Value) => (Obj, Value)])


	type Store = Map[Loc, Obj]

	def newloc : Loc
	def isAsync(lab : Lab) : Boolean

	def isReduced(fields : Map[Fld, Expression]) : Boolean =
		fields.valuesIterator.forall(isValue)


	def subst(body : Expression, x : Var, substExpr : Expression) : Expression = body match {
		case Location(_, _) => body

		case V(y) if y == x => substExpr
		case V(_) => body

		case Operation(e, m, arg) => Operation(subst(e, x, substExpr), m, subst(arg, x, substExpr))

		case Let(y, e, letBody) if x == y => Let(y, subst(e, x, substExpr), letBody)
		case Let(y, e, letBody) => Let(y, subst(e, x, substExpr), subst(letBody, x, substExpr))

		case New(cls, lab, fields) => New(cls, lab, fields.mapValues(e => subst(e, x, substExpr)))

		case Num(_) => body

		case Add(e1, e2) => Add(subst(e1, x, substExpr), subst(e2, x, substExpr))
	}


	def reduce(e : Expression, store : Store) : (Expression, Store) = e match {
		case V(x) => sys.error(s"undefined variable $x")


		case Let(x, v : Value, body) =>
			(subst(body, x, v), store)

		case Let(x, e1, body) =>
			val (newE, newStore) = reduce(e1, store)
			(Let(x, newE, body), newStore)


		case Operation(Location(o, l), m, arg : Value) if isAsync(l) =>
			//Asynchronous reduction
			val obj@Obj(cls, lab, fields) = store(o)

			require(lab == l)

			val method = cls.methods(m)
			val (newObj, returnValue) = method(obj, arg)

			require(newObj.cls == obj.cls)
			require(newObj.lab == obj.lab)

			(returnValue, store + (o -> newObj))

		case Operation(v : Value, m, arg) =>
			val (newArg, newStore) = reduce(arg, store)
			(Operation(v, m, newArg), newStore)

		case Operation(e1, m, arg) =>
			val (newE1, newStore) = reduce(e1, store)
			(Operation(newE1, m, arg), newStore)


		case New(cls, lab, fields) if isAsync(lab) && isReduced(fields) =>
			val o = newloc
			(Location(o, lab), store + (o -> Obj(cls, lab, fields.asInstanceOf[Map[Fld, Value]])))

		case New(cls, lab, fields) =>
			val Some((fld, fldExpr)) = fields.find(kv => !isValue(kv._2))
			val (newFldExpr, newStore) = reduce(fldExpr, store)
			(New(cls, lab, fields + (fld -> newFldExpr)), newStore)


		case Add(Num(n1), Num(n2)) =>
			(Num(n1 + n2), store)

		case Add(v1 : Value, e2) =>
			val (newE2, newStore) = reduce(e2, store)
			(Add(v1, newE2), newStore)

		case Add(e1, e2) =>
			val (newE1, newStore) = reduce(e1, store)
			(Add(newE1, e2), newStore)
	}


	def reduceAll(e : Expression, store : Store) : (Expression, Store) = e match {
		case v : Value => (e, store)
		case _ =>
			val (newE, newStore) = reduce(e, store)
			reduceAll(newE, newStore)
	}

}
