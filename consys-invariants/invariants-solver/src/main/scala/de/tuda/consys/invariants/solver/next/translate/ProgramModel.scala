package de.tuda.consys.invariants.solver.next.translate

import com.microsoft.z3.{BoolSort, Context, Expr, FuncDecl, Sort, TupleSort, Symbol => Z3Symbol}
import de.tuda.consys.invariants.solver.next.ir.{IR, Natives}
import de.tuda.consys.invariants.solver.next.ir.IR.{FieldId, IRExpr, IRType, MethodDecl, MethodId, NativeClassDecl, Num, ObjectClassDecl, ProgramDecl, QueryDecl, TClass, UpdateDecl, VarId}
import de.tuda.consys.invariants.solver.next.translate.TypeRep.{MethodTypeRep, NativeTypeRep, ObjectTypeRep, QueryMethodTypeRep, UpdateMethodTypeRep}
import de.tuda.consys.invariants.solver.next.translate.ExpressionCompiler.{UpdateBodyExpressionCompiler, ObjectClassExpressionCompiler}
import de.tuda.stg.consys.invariants.solver.subset.model.FieldModel
import de.tuda.stg.consys.invariants.solver.subset.model.types.TypeModel
import de.tuda.stg.consys.invariants.solver.subset.utils.{JDTUtils, Z3Utils}

import scala.collection.mutable

class ProgramModel(val env : Z3Env, val program : ProgramDecl) {

	def create() : Unit = {
		//1. Declare all types and create the type map
		val typeMap = createTypeMap()

		//2. Create invariant definition
		for ((clsId, cls) <- program.classTable) {
			cls match {
				case ocls : ObjectClassDecl => parseInvariant(ocls, typeMap)
				case _ =>
			}
		}

		//3. Create method definitions
		for ((clsId, cls) <- program.classTable) {
			cls match {
				case ocls : ObjectClassDecl =>
					for ((mthdId, mthd) <- ocls.methods) {
						parseMethod(ocls, mthd, typeMap)
					}
				case _ =>
			}
		}



		println("Done.")
	}


	private def createTypeMap() : TypeMap = {
		import env.ctx

		trait ClassRep {
			def sort : Sort
		}
		case class ObjectClassRep(override val sort : TupleSort,	accessors : Map[FieldId, FuncDecl[_]]) extends ClassRep
		case class NativeClassRep(override val sort : Sort) extends ClassRep

		// 1st iteration: Build the map with all datatypes for the classes
		val classMap = mutable.Map.empty[IRType, ClassRep]
		for ((clsId, cls) <- program.classTable) {
			cls match {
				case Natives.INT_CLASS =>
					classMap.put(TClass(cls.name), NativeClassRep(ctx.getIntSort))

				case Natives.BOOL_CLASS =>
					classMap.put(TClass(cls.name), NativeClassRep(ctx.getBoolSort))

				case Natives.STRING_CLASS =>
					classMap.put(TClass(cls.name), NativeClassRep(ctx.getStringSort))

				case ObjectClassDecl(name, invariant, fields, methods) =>
					/* 1. Initialize the sort of the class. */
					val numOfFields = fields.size
					val fieldSeq = fields.toSeq

					// Create the z3 sort for states of this class.
					val fieldNames = new Array[Z3Symbol](numOfFields)
					val fieldSorts = new Array[Sort](numOfFields)

					for (((fieldId, fieldDecl), i) <- fieldSeq.zipWithIndex) {
						fieldNames(i) = ctx.mkSymbol(fieldId)
						fieldSorts(i) = classMap.getOrElse(fieldDecl.typ, throw new ModelException("field type not available: " + fieldDecl)).sort
					}

					val sortName = "Class$" + clsId
					val classSort = ctx.mkTupleSort(ctx.mkSymbol(sortName), fieldNames, fieldSorts)

					// Create the field accessors for the class
					val accessorBuilder = Map.newBuilder[FieldId, FuncDecl[_]]
					val accessorArr = classSort.getFieldDecls
					for (((fieldId, _), i) <- fieldSeq.zipWithIndex) {
						accessorBuilder.addOne((fieldId, accessorArr(i)))
					}

					val clsModel = ObjectClassRep(classSort, accessorBuilder.result())
					classMap.put(TClass(name), clsModel)
			}
		}

		// 2nd iteration: Build the method declarations for each class
		val methodMapBuilder = Map.newBuilder[IRType, Map[(MethodId, Seq[IRType]), MethodTypeRep]]
		for ((clsId, cls) <- program.classTable) {
			cls match {
				case NativeClassDecl(name) =>

				case ObjectClassDecl(name, invariant, fields, methods) =>
					val classMethodBuilder = Map.newBuilder[(MethodId, Seq[IRType]), MethodTypeRep]
					for ((mthdId, mthd) <- methods) {

						//Add the receiver object to the Z3 function parameters
						val declaredParameterTypes = mthd.declaredParameters.map(decl => decl.typ)
						val actualParameterTypes = Seq(cls.toType) ++ declaredParameterTypes
						val actualParameterSorts = actualParameterTypes.map(typ => classMap.getOrElse(typ, throw new UnknownTypeModelException(typ)).sort)

						mthd match {
							case query@QueryDecl(name, parameters, returnTyp, body) =>
								val returnSort = classMap.getOrElse(query.returnTyp, throw new UnknownTypeModelException(query.returnTyp)).sort
								val mthdDecl = ctx.mkFuncDecl( cls.name + "$query$" + mthd.name, actualParameterSorts.toArray[Sort], returnSort)
								classMethodBuilder.addOne((mthdId, declaredParameterTypes), QueryMethodTypeRep(mthdDecl))
							case UpdateDecl(name, parameters, body) =>
								val returnSort = classMap.getOrElse(cls.toType, throw new UnknownTypeModelException(cls.toType)).sort
								val mthdDecl = ctx.mkFuncDecl(cls.name + "$update$" + mthd.name, actualParameterSorts.toArray[Sort], returnSort)
								classMethodBuilder.addOne((mthdId, declaredParameterTypes), UpdateMethodTypeRep(mthdDecl))
						}
					}
					methodMapBuilder.addOne(TClass(name), classMethodBuilder.result())
			}
		}

		val methodMap = methodMapBuilder.result()


		// 3rd: Combine class and method map to create the type map
		val typeMapBuilder = Map.newBuilder[IRType, TypeRep]
		for ((typ, classRep) <- classMap) {
			classRep match {
				case NativeClassRep(sort) =>
					typeMapBuilder.addOne(typ, NativeTypeRep(sort))
				case ObjectClassRep(sort, accessors) =>
					typeMapBuilder.addOne(typ, ObjectTypeRep(sort, accessors, methodMap.getOrElse(typ, Map())))
			}
		}

		typeMapBuilder.result()

	}

	private def parseMethod(cls : ObjectClassDecl, mthd : MethodDecl, typeMap : TypeMap) : Unit = {
		import env.ctx

		val typeRep = typeMap.get(cls.toType) match {
			case Some(x : ObjectTypeRep) => x
			case _ => throw new ModelException("class not in type map or no object class: " + cls)
		}

		val methodRep = typeRep.methods.getOrElse((mthd.name, mthd.declaredParameterTypes),
			throw new ModelException("method not found: " + mthd))

		val receiverExpr = ctx.mkFreshConst("s0", typeRep.sort)

		val declaredArguments : Seq[Expr[_]] = mthd.declaredParameters.map(varDecl => {
			val typeRep = typeMap.getOrElse(varDecl.typ, throw new ModelException("Unknown type: " + varDecl.typ))
			ctx.mkFreshConst(varDecl.name, typeRep.sort)
		})

		val declaredArgumentsMap = mthd.declaredParameters.zip(declaredArguments).map(t => (t._1.name, t._2)).toMap

		mthd match {
			case QueryDecl(name, parameters, returnTyp, body) =>
				val (bodyVal, bodyState) = new ObjectClassExpressionCompiler(ctx, typeMap).compile[TupleSort](mthd.body, declaredArgumentsMap, receiverExpr)

				val methodDef = ctx.mkForall(
					(Seq(receiverExpr) ++ declaredArguments).toArray,
					ctx.mkEq(ctx.mkApp(methodRep.funcDecl, (Seq(receiverExpr) ++ declaredArguments).toArray : _*), bodyVal),
					1,
					null,
					null,
					null,
					null
				)

				env.solver.add(methodDef)

			case UpdateDecl(name, parameters, body) =>
				val (bodyVal, bodyState) = new UpdateBodyExpressionCompiler(ctx, typeMap).compile[TupleSort](mthd.body, declaredArgumentsMap, receiverExpr)

				val methodDef = ctx.mkForall(
					(Seq(receiverExpr) ++ declaredArguments).toArray,
					ctx.mkEq(ctx.mkApp(methodRep.funcDecl, (Seq(receiverExpr) ++ declaredArguments).toArray : _*), bodyState),
					1,
					null,
					null,
					null,
					null
				)

				env.solver.add(methodDef)
		}
	}

	private def parseInvariant(cls : ObjectClassDecl, typeMap : TypeMap) : FuncDecl[BoolSort] = {
		import env.ctx
		val typeRep = typeMap.get(cls.toType) match {
			case Some(x : ObjectTypeRep) => x
			case _ => throw new ModelException("class not in type map or no object class: " + cls)
		}

		val invDecl = ctx.mkFuncDecl(cls.name + "$inv" , typeRep.sort, ctx.getBoolSort)

		val invArg = ctx.mkFreshConst("s0", typeRep.sort)
		val (invExpr, invState) = new ObjectClassExpressionCompiler(ctx, typeMap).compile(cls.invariant, Map(), invArg)

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
