package de.tuda.stg.consys.invariants.lang

import de.tuda.stg.consys.invariants.lang.Cls.{MethodDef, VarDef}
import de.tuda.stg.consys.invariants.lang.Expr.{RefVal, Val, interp}

sealed trait Stmt

object Stmt {

	case class Return(e : Expr) extends Stmt
	case class DoNew(x : VarId, c : ClassId, fields : Map[FieldId, Expr], body : Stmt) extends Stmt
	case class DoGetField(x : VarId, f : FieldId, body : Stmt) extends Stmt
	case class DoSetField(x : VarId, f : FieldId, e : Expr, body : Stmt) extends Stmt
	case class DoCallMethod(x : VarId, recv : Expr, m : MethodId, args : Seq[Expr], body : Stmt) extends Stmt

	def interp(ct : ClsTable, env : VarEnv, store : Store, stmt : Stmt) : (Val, Store) = {
		stmt match {
			case Return(e) => (Expr.interp(env, e), store)

			case DoNew(x, c, fields, body) =>
				val cls = ct(c)
				require(cls.fields.keys == fields.keys)
				require(!store.contains(x))

				val store1 = store + (x -> Obj(c, fields.map(t => (t._1, Expr.interp(env, t._2)))))
				val env1 = env + (x -> RefVal(x))

				val res = interp(ct, env1, store1, body)
				res

			case DoGetField(x, f, body) =>
				val RefVal(ref) = env(thsId)
				val obj = store(ref)

				val env1 = env + (x -> obj.fields(f))
				interp(ct, env1, store, body)

			case DoSetField(x, f, e, body) =>
				val RefVal(ref) = env(thsId)
				val obj = store(ref)

				val newVal = Expr.interp(env, e)
				val newObj = obj.copy(fields = obj.fields + (f -> newVal))

				val env1 = env + (x -> newVal)
				val store1 = store + (ref -> newObj)
				interp(ct, env1, store1, body)

			case DoCallMethod(x, recv, m, args, body) =>
				val ths@RefVal(ref) = Expr.interp(env, recv)
				val obj = store(ref)

				val argVals = args.map(e => Expr.interp(env, e))

				val mDef = ct(obj.c).methods(m)
				val mEnv : VarEnv = mDef.pars.map(vDef => vDef.x).zip(argVals).toMap + (thsId -> ths)

				val mRes = interp(ct, mEnv, store, mDef.stmt)

				val newEnv = env + (x -> mRes._1)
				interp(ct, newEnv, mRes._2, body)
		}
	}


}
