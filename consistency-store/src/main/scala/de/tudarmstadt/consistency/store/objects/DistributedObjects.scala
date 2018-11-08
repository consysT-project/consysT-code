package de.tudarmstadt.consistency.store.objects

import de.mkoe.interpreter.lang.{ArithmeticLanguage, LambdaLanguage, Language}

import scala.collection.mutable

/**
	* Created on 07.11.18.
	*
	* @author Mirko Köhler
	*/
object DistributedObjects {

	trait DistributedObjectLanguage {
		type ClassName
		type FieldName
		type MethodName
		type VarName

		type Address

		type Consistency


		trait ClassId
		case class Class(name : ClassName) extends ClassId
		case object Root extends ClassId

		trait Type
		case object TInt extends Type
		case class TFun(arg : Type, ret : Type) extends Type
		case class TClass(className : ClassId) extends Type


		sealed trait Expression
		sealed trait Value extends Expression
		case class Num(n : Int) extends Expression with Value
		case class Fun(x : VarName, body : Computation) extends Expression with Value
		case class Ref(refType : Type, refConsistency : Consistency, addr : Address) extends Expression with Value
		case class Obj(className : ClassId, fields : Map[FieldName, Value]) extends Expression with Value //Developers should use new

		case class Var(x : VarName) extends Expression
		case class New(className : ClassId, fieldArguments : Map[FieldName, Expression]) extends Expression
		case class FieldRead(recv : Expression, f : FieldName) extends Expression
		case class FieldWrite(recv : Expression, f : FieldName, e : Expression) extends Expression


		trait Operation
		case class Eval(expr : Expression) extends Operation
		case class Enref(consistency : Consistency, expr : Expression) extends Operation
		case class Deref(expr : Expression) extends Operation


		trait Computation
		case class Return(e : Expression) extends Computation
		case class Do(x : VarName, c0 : Operation, c1 : Computation) extends Computation
		case class App(e1 : Expression, e2 : Expression) extends Computation


		case class AnnotatedType(t : Type, c : Consistency)

		case class ClassDef(name : ClassName, parent : ClassId, fieldDeclarations : Map[FieldName, AnnotatedType] /*, methodDeclarations */)

		type ClassTable = Map[ClassName, ClassDef]

		case class Program(ct : ClassTable, processes : Seq[Computation])

	}


	trait Interpreter {
		lang : DistributedObjectLanguage =>

		type Environment = Map[VarName, Value]

		case class Conf(store : Replica, env : Environment, c : Computation)


		type ReplicaId <: Ordered[ReplicaId]
		type Timestamp <: Ordered[Timestamp]

		case class StoreEntry(timestamp : Timestamp, consistency : Consistency, data : Value)

		class Replica(val id : ReplicaId, val store : Map[Address, StoreEntry] = Map.empty) {

			def getTimestamp : Timestamp

			def +(addr : Address, consistency: Consistency, data : Value) : Replica =
				new Replica(id, store + (addr -> StoreEntry(getTimestamp, consistency, data)))

		}




		def interp()


		//Returns None if the configuration cannot make a step
		def interp(conf : Conf, world : Seq[Conf])(implicit ct : ClassTable) : Option[Conf] = {

			val Conf(store, env, comp) = conf

			comp match {
				case Return(v : Value) =>
					None
				case Return(e) =>
					Some(Conf(store, env, Return(interp(e, env))))

				case Do(x, Eval(v : Value), c2) =>
					None
				case Do(x, Eval(e), c2) =>
					val eVal = interp(e, env)
					Some(Conf(store, env + (x -> eVal), c2))

				case Do(x, Deref(Ref(refType, refConsistency, addr)), c2)
					if isConsistent(refConsistency, addr, world.map(_.store)) =>
					Some(Conf(store, env + (x -> store(addr)), c2))
				case Do(x, Deref(v : Value), c2) =>
					None
				case Do(x, Deref(e), c2) =>
					val v = interp(e, env)
					Some(Conf(store, env, Do(x, Deref(v), c2)))

				case Do(x, Enref(consistency, v : Value), c2) =>
					val addr = freshAddr()
					Some(Conf(store + (addr, consistency, v), env + (x -> Ref(typeOf(v), consistency, addr)), c2))
				case Do(x, Enref(consistency, e), c2) =>
					val v = interp(e, env)
					Some(Conf(store, env, Do(x, Enref(consistency, v), c2)))

				case App(Fun(x, body), v : Value) =>
					Some(Conf(store, env + (x -> v), body))
				case App(v1 : Value, v2 : Value) =>
					None
				case App(v1 : Value, e2) =>
					val v2 = interp(e2, env)
					Some(Conf(store, env, App(v1, v2)))
				case App(e1, e2) =>
					val v1 = interp(v1, env)
					Some(Conf(store, env, App(v1, e2)))

			}
		}


		def interp(e : Expression, env : Environment)(implicit ct : ClassTable) : Value = e match {
//			case v : Value => v

			case Var(x) => env(x)

			case New(clsid, fields) =>
				assert(fieldsMatchClass(fields, clsid))
				Obj(clsid, fields.mapValues(e => interp(e, env)))

			case FieldRead(Obj(clsid, fields), f) =>
				fields(f)
			case FieldRead(e1, f) =>
				val v1 = interp(e1, env)
				interp(FieldRead(v1, f), env)

			case FieldWrite(Obj(clsid, fields), f, v2 : Value) =>
				Obj(clsid, fields + (f -> v2))
			case FieldWrite(v1 : Value, f, e2) =>
				val v2 = interp(e2, env)
				interp(FieldWrite(v1, f, v2), env)
			case FieldWrite(e1, f, e2) =>
				val v1 = interp(e1, env)
				interp(FieldWrite(v1, f, e2), env)
		}


		def typeOf(e : Expression) : Type = ???

		def freshAddr() : Address

		def chooseConf(confs : Seq[Conf]) : (Int, Conf)

		def isConsistent(consistency: Consistency, addr : Address, stores : Seq[Replica]) : Boolean

		private def fieldsMatchClass(fields : Map[FieldName, Expression], classId : ClassId)(implicit ct : ClassTable) : Boolean = classId match {
			case Root => fields.isEmpty
			case Class(className) =>
				val classDef = ct(className)
				classDef.fieldDeclarations.keySet == fields.keySet &&
					fields.forall(f => typeOf(f._2) == classDef.fieldDeclarations(f._1))
		}

	}


	object LanguageImpl extends DistributedObjectLanguage {
		override type ClassName = Symbol
		override type FieldName = Symbol
		override type MethodName = Symbol
		override type VarName = Symbol

		override type Address = Int

		override type Consistency = Symbol
	}

}

