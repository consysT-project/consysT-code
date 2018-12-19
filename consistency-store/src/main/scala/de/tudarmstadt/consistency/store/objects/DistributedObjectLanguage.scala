package de.tudarmstadt.consistency.store.objects

/**
	* Created on 26.11.18.
	*
	* @author Mirko Köhler
	*/
trait DistributedObjectLanguage {
	self : Bindings =>

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
	case class Fun(x : Var, pc : Consistency, argType : Annotated, body : Computation) extends Expression with Value
	case class Ref(refType : Annotated, addr : Address) extends Expression with Value
	case class Obj(className : ClassId, fields : Map[FieldName, Value]) extends Expression with Value //Developers should use new
	case class Defined(v : Value) extends Expression with Value
	case object Undefined extends Expression with Value

	case class Id(x : Var) extends Expression
	case class New(className : ClassId, fieldArguments : Map[FieldName, Expression]) extends Expression
	case class FieldRead(recv : Expression, f : FieldName) extends Expression
	case class FieldWrite(recv : Expression, f : FieldName, e : Expression) extends Expression
	case class NewDefined(e : Expression) extends Expression

	trait Computation //Computation result is a return(v)
	case class Return(e : Expression) extends Computation
	case class Do(x : Var, c0 : Computation, c1 : Computation) extends Computation
	case class App(e1 : Expression, e2 : Expression) extends Computation
	case class Enref(consistency : Consistency, expr : Expression) extends Computation
	case class Deref(expr : Expression) extends Computation
	case class UpdateRef(refExpr : Expression, e : Expression) extends Computation
	case class Match(e0 : Expression, valId : Var, someBranch : Computation, noneBranch : Computation) extends Computation



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