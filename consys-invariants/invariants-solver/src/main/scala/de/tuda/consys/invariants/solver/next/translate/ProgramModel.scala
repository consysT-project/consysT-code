package de.tuda.consys.invariants.solver.next.translate

import com.microsoft.z3.{BoolSort, Context, Expr, FuncDecl, Sort, TupleSort, Symbol => Z3Symbol}
import de.tuda.consys.invariants.solver.next.ir.{IR, Natives}
import de.tuda.consys.invariants.solver.next.ir.IR.{ClassId, ClassTable, FieldId, IRExpr, MethodDecl, MethodId, NativeClassDecl, Num, ObjectClassDecl, ProgramDecl, QueryDecl, Type, UpdateDecl, VarId}
import de.tuda.consys.invariants.solver.next.translate.TypeChecker.{Immutable, Mutable, TypeException, checkCls}
import de.tuda.consys.invariants.solver.next.translate.ExpressionCompiler.{ClassExpressionCompiler, MutableClassExpressionCompiler}
import de.tuda.consys.invariants.solver.next.translate.Z3Representations.{ClassRep, FieldRep, InvariantRep, MethodRep, NativeClassRep, ObjectClassRep, QueryMethodRep, UpdateMethodRep}
import de.tuda.stg.consys.invariants.solver.subset.model.FieldModel
import de.tuda.stg.consys.invariants.solver.subset.model.types.TypeModel
import de.tuda.stg.consys.invariants.solver.subset.utils.{JDTUtils, Z3Utils}

import scala.collection.mutable

class ProgramModel(val env : Z3Env, val program : ProgramDecl) {

	def create() : Unit = {
		implicit val ctx : Context = env.ctx
		implicit val classTable : ClassTable = program.classTable

		//0. Type check the expressions
		for (classDecl <- program.classes) {
			checkCls(classDecl)(program.classTable)
		}

		//1. Declare all types and create the type map
		implicit val repTable : RepTable = createRepTable()

		//2. Create invariant definition
		val invariantMapBuilder = Map.newBuilder[ClassId, InvariantRep]
		for (classDecl <- program.classes) {
			classDecl match {
				case ocls : ObjectClassDecl =>
					val invariantRep = parseInvariant(ocls)
					invariantMapBuilder.addOne(classDecl.classId -> invariantRep)
				case _ =>
			}
		}
		val invariantMap = invariantMapBuilder.result()

		//3. Create method definitions
		for (classDecl <- program.classes) {
			classDecl match {
				case ocls : ObjectClassDecl =>
					for ((methodId, methodDecl) <- ocls.methods) {
						parseMethod(ocls, methodDecl)
					}
				case _ =>
			}
		}


		//4. Check properties
		import env.ctx
		for ((classId, typeRep) <- repTable) {
			typeRep match {
				case objTypeRep@ObjectClassRep(sort, accessors, methods) =>
					for ((methodId, mthdRep) <- methods) {
						mthdRep match {
							case UpdateMethodRep(funcDecl) =>
								val inv = invariantMap(classId).funcDecl
								val arguments : Array[Expr[_]] = funcDecl.getDomain.map(sort => ctx.mkFreshConst("arg", sort))
								val s0 = arguments(0)

								val property = ctx.mkForall(
									arguments,
									ctx.mkImplies(
										ctx.mkApp(inv, s0),
										ctx.mkApp(inv, ctx.mkApp(funcDecl, arguments : _*))
									),
									1, null, null, null, null
								)

								val checkResult = env.solver.check(ctx.mkNot(property))
								println(s"$classId.$methodId = $checkResult")

							case QueryMethodRep(funcDecl) =>
						}
					}
				case NativeClassRep(sort) =>
			}
		}

		println("Done.")
	}


	private def createRepTable() : RepTable = {
		import env.ctx

		trait TempClassRep {
			def sort : Sort
		}
		case class TempObjectClassRep(override val sort : TupleSort,	accessors : Map[FieldId, FieldRep]) extends TempClassRep
		case class TempNativeClassRep(override val sort : Sort) extends TempClassRep

		// 1st iteration: Build the map with all datatypes for the classes
		val tempRepMap = mutable.Map.empty[ClassId, TempClassRep]
		for (classDecl <- program.classes) {
			classDecl match {
				case Natives.INT_CLASS =>
					tempRepMap.put(classDecl.classId, TempNativeClassRep(ctx.getIntSort))

				case Natives.BOOL_CLASS =>
					tempRepMap.put(classDecl.classId, TempNativeClassRep(ctx.getBoolSort))

				case Natives.STRING_CLASS =>
					tempRepMap.put(classDecl.classId, TempNativeClassRep(ctx.getStringSort))

				case Natives.UNIT_CLASS =>
					val unitSort = ctx.mkTupleSort(ctx.mkSymbol("Unit"), Array(), Array())
					tempRepMap.put(classDecl.classId, TempNativeClassRep(unitSort))

				case ObjectClassDecl(name, invariant, fields, methods) =>
					/* 1. Initialize the sort of the class. */
					val numOfFields = fields.size
					val fieldSeq = fields.toSeq

					// Create the z3 sort for states of this class.
					val fieldNames = new Array[Z3Symbol](numOfFields)
					val fieldSorts = new Array[Sort](numOfFields)

					for (((fieldId, fieldDecl), i) <- fieldSeq.zipWithIndex) {
						fieldNames(i) = ctx.mkSymbol(fieldId)
						fieldSorts(i) = tempRepMap.getOrElse(fieldDecl.typ.name, throw new ModelException("field type not available: " + fieldDecl)).sort
					}

					val sortName = "Class$" + classDecl.classId
					val classSort = ctx.mkTupleSort(ctx.mkSymbol(sortName), fieldNames, fieldSorts)


					// Create the field accessors for the class
					val accessorBuilder = Map.newBuilder[FieldId, FieldRep]
					val accessorArr = classSort.getFieldDecls
					for (((fieldId, _), i) <- fieldSeq.zipWithIndex) {
						accessorBuilder.addOne(fieldId, FieldRep(accessorArr(i)))
					}

					val clsModel = TempObjectClassRep(classSort, accessorBuilder.result())
					tempRepMap.put(name, clsModel)
			}
		}

		// 2nd iteration: Build the method declarations for each class
		val methodMapBuilder = Map.newBuilder[ClassId, Map[MethodId, MethodRep]]
		for (classDecl <- program.classes) {
			classDecl match {
				case NativeClassDecl(name) =>

				case ObjectClassDecl(name, invariant, fields, methods) =>
					val classMethodBuilder = Map.newBuilder[MethodId, MethodRep]
					for ((methodId, mthd) <- methods) {

						//Add the receiver object to the Z3 function parameters
						val declaredParameterTypes = mthd.declaredParameters.map(decl => decl.typ)
						val actualParameterTypes = Seq(classDecl.toType) ++ declaredParameterTypes
						val actualParameterSorts = actualParameterTypes.map(typ => tempRepMap.getOrElse(typ.name, throw new UnknownTypeModelException(typ)).sort)

						mthd match {
							case query@QueryDecl(name, parameters, returnTyp, body) =>
								val returnSort = tempRepMap.getOrElse(query.returnTyp.name, throw new UnknownTypeModelException(query.returnTyp)).sort
								val mthdDecl = ctx.mkFuncDecl( classDecl.classId + "$query$" + mthd.name, actualParameterSorts.toArray[Sort], returnSort)
								classMethodBuilder.addOne(methodId, QueryMethodRep(mthdDecl))
							case UpdateDecl(name, parameters, body) =>
								val returnSort = tempRepMap.getOrElse(classDecl.toType.name, throw new UnknownTypeModelException(classDecl.toType)).sort
								val mthdDecl = ctx.mkFuncDecl(classDecl.classId + "$update$" + mthd.name, actualParameterSorts.toArray[Sort], returnSort)
								classMethodBuilder.addOne(methodId, UpdateMethodRep(mthdDecl))
						}
					}
					methodMapBuilder.addOne(name, classMethodBuilder.result())
			}
		}

		val methodMap = methodMapBuilder.result()


		// 3rd: Combine class and method map to create the type map
		val typeMapBuilder = Map.newBuilder[ClassId, ClassRep]
		for ((classId, classRep) <- tempRepMap) {
			classRep match {
				case TempNativeClassRep(sort) =>
					typeMapBuilder.addOne(classId, NativeClassRep(sort))
				case TempObjectClassRep(sort, accessors) =>
					typeMapBuilder.addOne(classId, ObjectClassRep(sort, accessors, methodMap.getOrElse(classId, Map())))
			}
		}

		typeMapBuilder.result()

	}

	private def parseMethod(classDecl : ObjectClassDecl, methodDecl : MethodDecl)(implicit repTable : RepTable, classTable : ClassTable) : Unit = {
		implicit val ctx : Context = env.ctx

		val typeRep = repTable.get(classDecl.classId) match {
			case Some(x : ObjectClassRep) => x
			case _ => throw new ModelException("class not in type map or no object class: " + classDecl)
		}

		val methodRep = typeRep.methods.getOrElse(methodDecl.name,
			throw new ModelException("method not found: " + methodDecl))

		val receiverExpr = ctx.mkFreshConst("s0", typeRep.sort)

		val declaredArguments : Seq[Expr[_]] = methodDecl.declaredParameters.map(varDecl => {
			val typeRep = repTable.getOrElse(varDecl.typ.name, throw new ModelException("Unknown type: " + varDecl.typ))
			ctx.mkFreshConst(varDecl.name, typeRep.sort)
		})

		val declaredArgumentsMap = methodDecl.declaredParameters.zip(declaredArguments).map(t => (t._1.name, t._2)).toMap

		methodDecl match {
			case QueryDecl(name, parameters, returnTyp, body) =>
				val (bodyVal, bodyState) =
					new ClassExpressionCompiler(classDecl.classId)
						.compile[TupleSort](methodDecl.body, declaredArgumentsMap, receiverExpr)

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
				val (bodyVal, bodyState) =
					new MutableClassExpressionCompiler(classDecl.classId)
						.compile[TupleSort](methodDecl.body, declaredArgumentsMap, receiverExpr)

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

	private def parseInvariant(classDecl : ObjectClassDecl)(implicit repTable : RepTable, classTable : ClassTable) : InvariantRep = {
		implicit val ctx : Context = env.ctx

		val typeRep = repTable.get(classDecl.classId) match {
			case Some(x : ObjectClassRep) => x
			case _ => throw new ModelException("class not in type map or no object class: " + classDecl)
		}

		val invDecl = ctx.mkFuncDecl(classDecl.classId + "$inv" , typeRep.sort, ctx.getBoolSort)

		val invArg = ctx.mkFreshConst("s0", typeRep.sort)
		val (invExpr, invState) = new ClassExpressionCompiler(classDecl.classId).compile(classDecl.invariant, Map(), invArg)

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

		InvariantRep(invDecl)
	}


	/*def parseMethod(method : MethodDecl) : Any = {
		env.ctx.mkDatatypeSort()

	}


	def parse(expr : IRExpr) : Z3Expr[_] = expr match {
		case Num(n) => env.ctx.mkInt(n)
		case Var(id) => env.ctx.
	}*/

}
