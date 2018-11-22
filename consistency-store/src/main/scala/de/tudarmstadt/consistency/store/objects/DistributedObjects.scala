package de.tudarmstadt.consistency.store.objects

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
		case object NoClass extends ClassId

		trait Type
		case object TInt extends Type
		case object TUnit extends Type
		case class TFun(arg : Annotated, pc: Consistency, returnType : Annotated) extends Type {
//			override def toString : String = s"$arg --$pc--> $returnType"
		} //pc = strongest consistency level of effects that happen in the function body
		case class TClass(className : ClassId) extends Type
		case class TRef(typ : Annotated) extends Type {
//			override def toString : String = s"Ref$typ"
		}
		case class TOpt(typ : Type) extends Type


		sealed trait Expression
		sealed trait Value extends Expression
		case object UnitVal extends Expression with Value
		case class Num(n : Int) extends Expression with Value
		case class Fun(x : VarName, pc : Consistency, argType : Annotated, body : Computation) extends Expression with Value
		case class Ref(refType : Annotated, addr : Address) extends Expression with Value
		case class Obj(className : ClassId, fields : Map[FieldName, Value]) extends Expression with Value //Developers should use new
		case class Defined(v : Value) extends Expression with Value
		case object Undefined extends Expression with Value

		case class Var(x : VarName) extends Expression
		case class New(className : ClassId, fieldArguments : Map[FieldName, Expression]) extends Expression
		case class FieldRead(recv : Expression, f : FieldName) extends Expression
		case class FieldWrite(recv : Expression, f : FieldName, e : Expression) extends Expression
		case class NewDefined(e : Expression) extends Expression

		trait Computation //Computation result is a return(v)
		case class Return(e : Expression) extends Computation
		case class Do(x : VarName, c0 : Computation, c1 : Computation) extends Computation
		case class App(e1 : Expression, e2 : Expression) extends Computation
		case class Enref(consistency : Consistency, expr : Expression) extends Computation
		case class Deref(expr : Expression) extends Computation
		case class UpdateRef(refExpr : Expression, e : Expression) extends Computation
		case class Match(e0 : Expression, valId : VarName, someBranch : Computation, noneBranch : Computation) extends Computation



		case class Annotated(typ : Type, consistency : Consistency) {
//			override def toString : String = s"($typ ^ $consistency)"
		}


		case class ClassDef(name : ClassName, parent : ClassId, fieldDeclarations : Map[FieldName, Type] /*, methodDeclarations */)

		type ClassTable = Map[ClassName, ClassDef]

		case class Program(ct : ClassTable, processes : Seq[Computation])

		def isValue(e : Expression) : Boolean =
			e.isInstanceOf[Value]

		val rootClassName : ClassName

		def lookupClassTable(classId: ClassId)(implicit ct : ClassTable) : ClassDef = classId match {
			case Root => ClassDef(rootClassName, NoClass, Map.empty)
			case Class(className) => ct(className)
			case NoClass => sys.error(s"cannot resolve None class")
		}

	}


	trait Replicas {
		lang : DistributedObjectLanguage =>

		type ReplicaId

		case class StoreEntry[Timestamp](timestamp : Timestamp, consistency : Consistency, value : Value)

		trait Replica[Timestamp] {

			type Self <: Replica[Timestamp]

			val id : ReplicaId
			val data : Map[Address, StoreEntry[Timestamp]]

			def get(addr : Address) : Option[Value] =
				data.get(addr).map(entry => entry.value)

			def apply(addr : Address) : Value =
				data(addr).value

			def timestamp() : Timestamp

			def +(addr : Address, consistency: Consistency, data : Value) : Self =
				this + (addr, StoreEntry(timestamp(), consistency, data))

			def +(addr : Address, entry : StoreEntry[Timestamp]) : Self


			def hasNewerValueFor(other : Replica[Timestamp], address : Address)(implicit ord : Ordering[Timestamp]) : Boolean =	(data.get(address), other.data.get(address)) match {
				case (None, None) => false
				case (Some(a), None) => true
				case (None, Some(b)) => false
				case (Some(a), Some(b)) => ord.gt(a.timestamp, b.timestamp)
			}

			def hasNewerValueFor(address : Address, entry : StoreEntry[Timestamp])(implicit ord : Ordering[Timestamp]) : Boolean =	data.get(address) match {
				case None => false
				case Some(StoreEntry(timestamp, _, _)) => ord.gt(timestamp, entry.timestamp)
			}

			override def toString : String =
				s"Replica#$id : $data"
		}


		class CurrentTimeMillisReplica(val id : ReplicaId, val data : Map[Address, StoreEntry[(Long, ReplicaId)]]) extends Replica[(Long, ReplicaId)] {
			override type Self = CurrentTimeMillisReplica

			override def timestamp() : (Long, ReplicaId) = (System.currentTimeMillis(), id)

			override def +(addr : Address, entry : StoreEntry[(Long, ReplicaId)]) : Self = {
				val newStore = data + (addr -> entry)
				return new CurrentTimeMillisReplica(id, newStore)
			}

		}
	}





	trait Interpreter {
		self : DistributedObjectLanguage with Replicas =>

		type Environment = Map[VarName, Value]
		type TypeEnvironment = Map[VarName, Annotated]

		type ReplicaId
		type Timestamp

		val ordering : Ordering[Timestamp]

		val consistencyLattice : ConsistencyLattice[Consistency]
		import consistencyLattice._
		def local = bot
		def  inconsistent = top


		case class Conf(store : Replica[Timestamp], env : Environment, c : Computation)



		def propagateStep(world : Seq[Conf]) : Option[Seq[Conf]] = {

			def mapFirst[A](seq : Seq[A])(f : A => Option[A]) : Option[Seq[A]] = seq match {
				case Nil => None
				case a :: tail => f(a) match {
					case None => mapFirst(tail)(f) match {
						case None => None
						case Some(newTail) => Some(a +: newTail)
					}
					case Some(newA) => Some(newA +: tail)
				}
			}

			mapFirst(world) { w1 =>
				val store1 = w1.store.data

				val foundNewerRow = world.flatMap(w2 => w2.store.data).find { row2 =>
					val (addr2, entry2) = row2
					store1.get(addr2) match {
						case None => true
						case Some(entry1) => ordering.gt(entry2.timestamp, entry1.timestamp)
					}
				}

				foundNewerRow match {
					case None =>
						println(s"replica ${w1.store.id}: already up-to-date")
						None
					case Some(newerEntry) =>
						val (addr1, entry1) = newerEntry
						println(s"replica ${w1.store.id}: received update $addr1 -> $entry1")
						Some(Conf(w1.store + (addr1, entry1), w1.env, w1.c))
				}
			}
		}


		def localStep(world : Seq[Conf])(implicit ct : ClassTable) : Option[Seq[Conf]] = world match {
			case Nil => None
			case conf :: tail => interp(conf, world) match {
				case None => localStep(tail) match {
					case None => None
					case Some(_world) => Some(conf +: _world)
				}
				case Some(_conf) =>
					Some(_conf +: tail)
			}
		}

		//Returns None if the configuration cannot make a step
		def interp(conf : Conf, world : Seq[Conf])(implicit ct : ClassTable) : Option[Conf] = {

			val Conf(store, env, comp) = conf

			comp match {
				case Return(v : Value) =>
					None
				case Return(e) => interp(e, env) match {
					case None => None
					case Some(_e) => Some(Conf(store, env, Return(_e)))
				}


				case Deref(Ref(refType, addr))
					if isConsistent(refType.consistency, addr, world.map(_.store)) =>
					Some(Conf(store, env, Return(store(addr))))
				case Deref(v : Value) =>
					None
				case Deref(e) =>
					interp(e, env).map(_e => Conf(store, env, Deref(_e)))

				case UpdateRef(Ref(refType, addr), v : Value)
					if isConsistent(refType.consistency, addr, world.map(_.store)) =>
					Some(Conf(store + (addr, refType.consistency, v), env, Return(v)))
				case UpdateRef(v1 : Value, v2 : Value) =>
					None
				case UpdateRef(v1 : Value, e2) =>
					interp(e2, env).map(v2 => Conf(store, env, UpdateRef(v1, v2)))
				case UpdateRef(e1, e2) =>
					interp(e1, env).map(v1 => Conf(store, env, UpdateRef(v1, e2)))


//				case Enref(consistency, v : Value) =>
//					val addr = freshAddr()
//					Some(Conf(store + (addr, consistency, v), env, Return(Ref(typeOf(v), consistency, addr))))
				case Enref(consistency, e) =>
					interp(e, env).map(_e => Conf(store, env, Enref(consistency, _e)))

				case Do(x, Return(v : Value), c2) =>
					Some(Conf(store, env + (x -> v), c2))
				case Do(x, c1, c2) => interp(Conf(store, env, c1), world) match {
					case None => None
					case Some(Conf(newStore, newEnv, newC1)) => Some(Conf(newStore, newEnv, Do(x, newC1, c2)))
				}

				case App(Fun(x, pc, t, body), v : Value) =>
					Some(Conf(store, env + (x -> v), body))
				case App(v1 : Value, v2 : Value) =>
					None
				case App(v1 : Value, e2) =>
					interp(e2, env).map(v2 => Conf(store, env, App(v1, v2)))
				case App(e1, e2) =>
					interp(e1, env).map(v1 => Conf(store, env, App(v1, e2)))

				case Match(Defined(v), x, c1, c2) =>
					Some(Conf(store, env + (x -> v), c1))
				case Match(Undefined, x, c1, c2) =>
					Some(Conf(store, env, c2))
				case Match(e0, x, c1, c2) =>
					interp(e0, env).map(v0 => Conf(store, env, Match(v0, x, c1, c2)))

			}
		}


		def interp(e : Expression, env : Environment)(implicit ct : ClassTable) : Option[Expression] = e match {
			case Var(x) => Some (env(x))

			case New(clsid, fields) if fields.forall(f => isValue(f._2)) =>
				assert(fieldsMatchClass(fields, clsid))
				Some (Obj(clsid, fields.mapValues(v => v.asInstanceOf[Value])))
			case New(clsid, fields) =>
				//TODO: It could happen to get stuck here, i.e. if there are no fields that can make progress, but not all are values
				Some(New(clsid, fields.mapValues(e0 => interp(e0, env) match {
					case None => e0
					case Some(_e0) => _e0
				})))

			case FieldRead(Obj(clsid, fields), f) =>
				Some(fields(f))
			case FieldRead(e1, f) => interp(e1, env) match {
				case None => None
				case Some(_e1) => Some(FieldRead(_e1, f))
			}


			case FieldWrite(Obj(clsid, fields), f, v2 : Value) =>
				Some(Obj(clsid, fields + (f -> v2)))
			case FieldWrite(v1 : Value, f, e2) => interp(e2, env) match {
				case None => None
				case Some(_e2) => Some(FieldWrite(v1, f, _e2))
			}
			case FieldWrite(e1, f, e2) => interp(e1, env) match {
				case None => None
				case Some(_e1) => Some(FieldWrite(_e1, f, e2))
			}


			case NewDefined(v : Value) =>
				Some(Defined(v))
			case NewDefined(e1) => interp(e1, env) match {
				case None => None
				case Some(_e1) => Some(NewDefined(_e1))
			}
		}


		def typeOf(e : Expression, tenv : TypeEnvironment)(implicit ct : ClassTable) : Annotated = e match {
			case UnitVal => Annotated(TUnit, local)

			case Num(_) =>
				Annotated(TInt, local)

			case Fun(x, pc, t, body) =>
				val (t1, pc1) = typeOf(body, pc, tenv + (x -> t))
				val res = Annotated(TFun(t, pc1, t1), local)
				println(s"type of $e == $res")
				res


			case Ref(refType, _) =>
				Annotated(TRef(refType), local)
			case Obj(className, _) =>
				Annotated(TClass(className), local)

			case Defined(v) => ???
			case Undefined => ???

			case Var(x) => tenv(x)

			case New(className, fieldArguments) =>
				val fieldTypes = fieldArguments.mapValues(expr => typeOf(expr, tenv))
				val fieldsMatchClass = fieldTypes.forall(entry => {
					val (fieldName, ft) = entry
					val fdef = lookupClassTable(className).fieldDeclarations(fieldName)
					fdef == ft.typ
				})

				if (!fieldsMatchClass)
					sys.error(s"type of fields does not match classdef, class $className, but got arguments $fieldTypes")

				val cnst = fieldTypes.values.foldLeft(bot) { (acc, fieldType) =>
					acc cup fieldType.consistency
				}

				Annotated(TClass(className), cnst)


			case FieldRead(recv, f) => typeOf(recv, tenv) match {
				case Annotated(TClass(className), l) =>
					val fType = lookupClassTable(className).fieldDeclarations(f)
					Annotated(fType, l)

				case x => sys.error(s"wrong type. expected class, got $x")
			}
			case FieldWrite(recv, f, e) => typeOf(recv, tenv) match {
				case Annotated(TClass(className), l) =>
					val eType = typeOf(e, tenv)
					val fType = lookupClassTable(className).fieldDeclarations(f)

					if (eType.typ != fType)
						sys.error(s"assigning wrong type, expected $fType, but got ${eType.typ}")

					Annotated(fType, l cup eType.consistency)

				case x => sys.error(s"wrong type. expected class, got $x")
			}
			case NewDefined(e) => ???
		}

		//returns the return type of the computation, as well as the required pc for all effects
		def typeOf(c : Computation, pc : Consistency, tenv : TypeEnvironment)(implicit ct : ClassTable) : (Annotated, Consistency) = c match {
			case Return(e) =>
				val t = typeOf(e, tenv)
				(t, inconsistent)

			case Do(x, c1, c2) =>
				val (t1, pc1) = typeOf(c1, pc, tenv)
				val (t2, pc2) = typeOf(c2, pc, tenv + (x -> t1))

				if (!(pc < (pc1 cap pc2)))
					sys.error(s"pc too weak")

				(t2, pc1 cap pc2)

			case App(e1 ,e2) => (typeOf(e1, tenv), typeOf(e2, tenv)) match {
				case (Annotated(tA1@TFun(tA, pc1, tB), l0), tA2) =>
					if (tA != tA2) sys.error(s"type does not match, expected $tA, but got $tA2")
 					if (!(pc < pc1)) sys.error(s"function pc too weak, expected at least $pc but got $pc1")
					if (!(l0 < pc1))
						sys.error(s"value too weak")
					(tB, pc1)

				case wrong =>
					sys.error(s"expected function type but got $wrong")
			}

			case Deref(expr) => typeOf(expr, tenv) match {
				case Annotated(TRef(Annotated(t0, l0)), l1) =>
					if (!(pc < l0)) sys.error(s"pc too weak")
					(Annotated(t0, l0 cup l1), l0)

				case x => sys.error(s"expected reference type but got $x")
			}

			case Enref(l0, expr) => typeOf(expr, tenv) match {
				case Annotated(t, l) =>
					if (l != local) sys.error(s"can only enref local value")
					if (!(pc < l0)) sys.error(s"pc too weak")
					(Annotated(TRef(Annotated(t, l0)), local), l0)
			}

			case UpdateRef(refExpr, e) => (typeOf(refExpr, tenv), typeOf(e, tenv)) match {
				case (Annotated(TRef(Annotated(t, l)), l1), Annotated(t2, l2)) if t == t2 =>
					if (!(l2 < l))
						sys.error(s"cant assign weaker level")
					if (!(l1 < l))
						sys.error(s"cant update reference with weaker value consistency")
					if (!(pc < l))
						sys.error(s"pc too weak")

					(Annotated(TUnit, local), l)

				case x => sys.error(s"expected reference type but got $x")
			}




		}

		def freeVariables(expression : Expression) : Set[VarName] = expression match {
			case Num(_) => Set.empty
			case Fun(x, _, _, body) => freeVariables(body) - x
			case Ref(_, _) => Set.empty
			case Obj(_, _) => Set.empty
			case Defined(_) => Set.empty
			case Undefined => Set.empty

			case Var(x) => Set(x)
			case New(_, fields) =>
				fields.values.flatMap(expr => freeVariables(expr)).toSet
			case FieldRead(recv, f) => freeVariables(recv)
			case FieldWrite(recv, f, e) => freeVariables(recv) ++ freeVariables(e)
			case NewDefined(e) => freeVariables(e)
		}

		def freeVariables(computation : Computation) : Set[VarName] = computation match {
			case Return(e) => freeVariables(e)
			case Do(x, c0, c1) => freeVariables(c0) ++ (freeVariables(c1) - x)
			case App(e1, e2) => freeVariables(e1) ++ freeVariables(e2)
			case Enref(_, e) => freeVariables(e)
			case Deref(e) => freeVariables(e)
			case UpdateRef(refExpr, e) => freeVariables(refExpr) ++ freeVariables(e)
			case Match(e0, x, some, none) => freeVariables(e0) ++ (freeVariables(some) - x) ++ freeVariables(none)
		}

		def freshAddr() : Address

		def isConsistent(consistency: Consistency, addr : Address, stores : Seq[Replica[Timestamp]]) : Boolean

		private def fieldsMatchClass(fields : Map[FieldName, Expression], classId : ClassId)(implicit ct : ClassTable) : Boolean = classId match {
			case Root => fields.isEmpty
//			case Class(className) =>
//				val classDef = ct(className)
//				classDef.fieldDeclarations.keySet == fields.keySet &&
//					fields.forall(f => typeOf(f._2) == classDef.fieldDeclarations(f._1))
		}

	}


	trait SimpleLanguageBindings extends DistributedObjectLanguage {
		override type ClassName = Symbol
		override type FieldName = Symbol
		override type MethodName = Symbol
		override type VarName = Symbol

		override type Address = Int

		override val rootClassName : Symbol = 'Root
	}

	object InterpreterImpl extends SimpleLanguageBindings with Interpreter with Replicas with DistributedObjectLanguage {


		private var count = 0
		override def freshAddr() : Address = {
			count = count + 1
			count
		}

		override type ReplicaId = Int

		override type Timestamp = (Long, ReplicaId)

		override def isConsistent(consistency : Consistency, addr : Int, stores : Seq[Replica[Timestamp]]) : Boolean = ???

		override val ordering : Ordering[Timestamp] = implicitly

		override val consistencyLattice : ConsistencyLattice[Consistency] = PropagationConsistencyDef.PropagationConsistencyLattice
		override type Consistency = PropagationConsistencyDef.ConsistencyLevel
	}


}

