package de.tuda.stg.consys.experimental.lang

import de.tuda.stg.consys.experimental.lang.ObjectStore.{CassandraStore, MapStore}

import scala.language.implicitConversions

/**
 * Created on 28.11.19.
 *
 * @author Mirko Köhler
 */
object Main extends App {


	object CassandraLangBinding extends Syntax with LocalSemantics
		with OOSyntax with OOSemantics
		with IntSyntax with IntSemantics
	{
		type VarId = Symbol
		type FieldId = String
		type MethodId = String
		type Location = Int

		override type ObjectStore = CassandraStore[Location, Obj]

		override protected def createReduction : Reduction =
			new Reduction with IntReduction with OOReduction {
				override protected val objStore : CassandraStore[Location, Obj] =
					new CassandraStore[Location, Obj](reset = true)
			}

		override protected def thisVar : Symbol = 'this
	}

	final val binding = CassandraLangBinding


	import binding._
	object Builder {


		//Conversions for expressions
		implicit def varIdToVar(v : VarId) : Var = Var(v)
		implicit def locIdToLoc(v : Location) : Loc = Loc(v)

		//Elements used in assignments
		trait SyntaxElem
		case class EXPR(expr : Expression) extends SyntaxElem
		case class NEW(loc : Location, fields : Map[FieldId, Expression], methods : Map[MethodId, MethodDef]) extends SyntaxElem
		case class GET(objExpr : Expression, field : FieldId) extends SyntaxElem
		case class SET(objExpr : Expression, field : FieldId, expr : Expression) extends SyntaxElem
		case class INVOKE(objExpr : Expression, method : MethodId, param : Expression) extends SyntaxElem

		//Builds assignments: 'x := NEW(...)
		implicit def varToVarOps(v : VarId) : VarOps = VarOps(v)
		case class VarOps(variable : VarId) {
			def :=(op : SyntaxElem) : AssignmentBuilder = AssignmentBuilder(variable, op)
		}
		case class AssignmentBuilder(variable : VarId, elem : SyntaxElem)

		//Do syntax
		case class DO(ass : AssignmentBuilder) extends BlockStatement {
			def IN(childBuilder : StatementBuilder) : StatementBuilder = ass match {
				case AssignmentBuilder(v, EXPR(expr)) => BindStmtBuilder(v, expr, childBuilder)
				case AssignmentBuilder(v, NEW(loc, fields, methods)) =>	NewStmtBuilder(v, loc, fields, methods, childBuilder)
				case AssignmentBuilder(v, GET(objExpr, field)) =>	GetStmtBuilder(v, objExpr, field, childBuilder)
				case AssignmentBuilder(v, SET(objExpr, field, expr)) =>	SetStmtBuilder(v, objExpr, field, expr, childBuilder)
				case AssignmentBuilder(v, INVOKE(objExpr, method, param)) =>	InvokeStmtBuilder(v, objExpr, method, param, childBuilder)
			}
		}

		//Return syntax
		case class RETURN(expr : Expression) extends StatementBuilder with BlockStatement {
			override def build() : Statement = Return(expr)
		}

		//Code block syntax
		trait BlockStatement
		case class BLOCK(stmts : BlockStatement*) extends StatementBuilder {
			override def build() : Statement = stmts.toList match {
				case (ret : RETURN) :: Nil => ret.build()
				case (doStmt : DO) :: rest =>	doStmt.IN(BLOCK(rest : _*)).build()
			}
		}

		//Builds statements
		implicit def builderToStmt(builder : StatementBuilder) : Statement =
			builder.build()

		trait StatementBuilder {
			def build() : Statement
		}
		case class BindStmtBuilder(v : VarId, expr : Expression, body : StatementBuilder) extends StatementBuilder {
			override def build() : Statement = Bind(expr, Continuation(v, body.build()))
		}
		case class NewStmtBuilder(v : VarId, loc : Location, fields : Map[FieldId, Expression], methods : Map[MethodId, MethodDef], body : StatementBuilder) extends StatementBuilder {
			override def build() : Statement = New(loc, fields, methods, Continuation(v, body.build()))
		}
		case class GetStmtBuilder(v : VarId, objExpr : Expression, field : FieldId, body : StatementBuilder) extends StatementBuilder {
			override def build() : Statement = FieldGet(objExpr, field, Continuation(v, body.build()))
		}
		case class SetStmtBuilder(v : VarId, objExpr : Expression, field : FieldId, expr : Expression, body : StatementBuilder) extends StatementBuilder {
			override def build() : Statement = FieldSet(objExpr, field, expr, Continuation(v, body.build()))
		}
		case class InvokeStmtBuilder(v : VarId, objExpr : Expression, method : MethodId, param : Expression, body : StatementBuilder) extends StatementBuilder {
			override def build() : Statement = Invoke(objExpr, method, param, Continuation(v, body.build()))
		}
	}

	import Builder._
//	val builder1 = DO ('x := NEW(0, Map(), Map())) IN (
//		DO ('y := NEW(1, Map("f" -> 'x), Map())) IN (
//			RETURN ('y)
//		)
//	)

	val incF : MethodDef = MethodDef('n,
		BLOCK (
			DO ('oldf := GET('this, "f")),
			DO ('newf := EXPR(Add('oldf, 'n))),
			DO ('_  := SET('this, "f", 'newf)),
			RETURN ('newf)
		)
	)


	val builder = BLOCK (
		DO ('x := EXPR(Num(5))),
		DO ('y := NEW(1, Map("f" -> 'x), Map("incN" -> incF))),
		DO ('res := INVOKE('y, "incN", Num(42))),
		RETURN ('res)
	)

	println(builder)
	val stmt = builder.build()
	println(stmt)
	println("###")
	val res = reduce(stmt)
	println("###")
	println(res)
}
