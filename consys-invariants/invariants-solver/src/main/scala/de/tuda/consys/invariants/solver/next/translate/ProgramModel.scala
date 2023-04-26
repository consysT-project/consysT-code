package de.tuda.consys.invariants.solver.next.translate

import com.microsoft.z3.{BoolSort, Context, Expr, FuncDecl, Sort, TupleSort, Symbol => Z3Symbol}
import de.tuda.consys.invariants.solver.next.ir.{IR, Natives}
import de.tuda.consys.invariants.solver.next.ir.IR.{FieldId, IRExpr, IRType, MethodDecl, Num, ObjectClassDecl, ProgramDecl, TClass}
import de.tuda.consys.invariants.solver.next.translate.TypeRep.{NativeTypeRep, ObjectTypeRep}
import de.tuda.consys.invariants.solver.next.translate.ExpressionParser.ObjectClassExpressionParser
import de.tuda.stg.consys.invariants.solver.subset.model.FieldModel
import de.tuda.stg.consys.invariants.solver.subset.model.types.TypeModel
import de.tuda.stg.consys.invariants.solver.subset.utils.{JDTUtils, Z3Utils}

import scala.collection.mutable

class ProgramModel(val env : Z3Env, val program : ProgramDecl) {


	def create() : Unit = {
		//1. Declare all types and create the type map
		val typeMap = createTypeMap()

		//2. Create method declarations


		//3. Create invariant definitions
		for ((clsId, cls) <- program.classTable) {
			cls match {
				case ocls : ObjectClassDecl => parseInvariant(ocls, typeMap)
				case _ =>
			}
		}

		println("Done.")
	}

	type TypeMap = Map[IRType, TypeRep]

	private def createTypeMap() : TypeMap = {
		import env.ctx

		val result = mutable.Map.empty[IRType, TypeRep]

		for ((clsId, cls) <- program.classTable) {
			cls match {
				case Natives.INT_CLASS =>
					result.put(TClass(cls.name), NativeTypeRep(ctx.getIntSort))

				case ObjectClassDecl(name, invariant, fields, methods) =>
					/* 1. Initialize the sort of the class. */
					val numOfFields = fields.size
					val fieldSeq = fields.toSeq

					// Create the z3 sort for states of this class.
					val fieldNames = new Array[Z3Symbol](numOfFields)
					val fieldSorts = new Array[Sort](numOfFields)

					for (((fieldId, fieldDecl), i) <- fieldSeq.zipWithIndex) {
						fieldNames(i) = ctx.mkSymbol(fieldId)
						fieldSorts(i) = result.getOrElse(fieldDecl.typ, throw new ModelException("field type not available: " + fieldDecl)).sort
					}

					val sortName = "Class$" + clsId
					val classSort = ctx.mkTupleSort(ctx.mkSymbol(sortName), fieldNames, fieldSorts)

					// Create the field accessors for the class
					val accessorBuilder = Map.newBuilder[FieldId, FuncDecl[_]]
					val accessorArr = classSort.getFieldDecls
					for (((fieldId, _), i) <- fieldSeq.zipWithIndex) {
						accessorBuilder.addOne((fieldId, accessorArr(i)))
					}

					val clsModel = ObjectTypeRep(classSort, accessorBuilder.result())
					result.put(TClass(name), clsModel)
			}
		}

		result.toMap
	}

	private def parseMethod(cls : ObjectClassDecl, mthd : MethodDecl, typeMap : TypeMap) : FuncDecl[BoolSort] = {
		import env.ctx

		val typeRep = typeMap.get(cls.toType) match {
			case Some(x : ObjectTypeRep) => x
			case _ => throw new ModelException("class not in type map or no object class: " + cls)
		}

		val parameterSorts = mthd.parameters.map(decl => typeMap.getOrElse(decl.typ, throw new UnknownTypeModelException(decl.typ)).sort)
		val returnSort = typeMap.getOrElse(mthd.returnTyp, throw new UnknownTypeModelException(mthd.returnTyp)).sort

		val mthdDecl = ctx.mkFuncDecl("mthd$" + cls.name + "$" + mthd.name, parameterSorts.toArray[Sort], returnSort)

		???

	}

	private def parseInvariant(cls : ObjectClassDecl, typeMap : TypeMap) : FuncDecl[BoolSort] = {
		import env.ctx
		val typeRep = typeMap.get(cls.toType) match {
			case Some(x : ObjectTypeRep) => x
			case _ => throw new ModelException("class not in type map or no object class: " + cls)
		}

		val invDecl = ctx.mkFuncDecl("inv$" + cls.name, typeRep.sort, ctx.getBoolSort)

		val invArg = ctx.mkFreshConst("s0", typeRep.sort)
		val invExpr = new ObjectClassExpressionParser(ctx, Map(), invArg, typeRep).parse(cls.invariant)

		env.solver.add(
			ctx.mkForall(Array(invArg),
				ctx.mkEq(ctx.mkApp(invDecl, invArg), invExpr.asInstanceOf[Expr[BoolSort]]),
				1,
				null,
				null,
				null,
				null
			)
		)

		invDecl
	}


	/*def parseMethod(method : MethodDecl) : Any = {
		env.ctx.mkDatatypeSort()

	}


	def parse(expr : IRExpr) : Z3Expr[_] = expr match {
		case Num(n) => env.ctx.mkInt(n)
		case Var(id) => env.ctx.
	}*/

}
