package de.tuda.consys.invariants.solver.next.translate

import com.microsoft.z3.{Context, Expr, Sort, Symbol => Z3Symbol}
import de.tuda.consys.invariants.solver.next.ir.IR.{TypeVarId, _}
import de.tuda.consys.invariants.solver.next.translate.Z3Representations.{CachedMap, FieldRep, InstantiatedClassRep, InstantiatedObjectClassRep, InvariantRep, MethodRep, ParametrizedClassRep, ParametrizedObjectClassRep, QueryMethodRep, RepTable, UpdateMethodRep}
import de.tuda.consys.invariants.solver.next.translate.types.TypeChecker.checkClass

import scala.collection.immutable.Map
import scala.collection.mutable

class ProgramModel(val env : Z3Env, val program : ProgramDecl) {

	def create() : Unit = {
		implicit val ctx : Context = env.ctx
		implicit val classTable : ClassTable = program.classTable

		//0. Type check the expressions
		for (classDecl <- program.classes) {
			checkClass(classDecl)(program.classTable)
		}

		//1. Declare all types and create the type map
		implicit val repTable : RepTable = createRepTable()

//		//2. Create invariant definition
//		val invariantMapBuilder = Map.newBuilder[ClassId, InvariantRep]
//		for (classDecl <- program.classes) {
//			classDecl match {
//				case ocls : ObjectClassDecl =>
//					val invariantRep = addInvariantDef(ocls)
//					invariantMapBuilder.addOne(classDecl.classId -> invariantRep)
//				case _ =>
//			}
//		}
//		val invariantMap = invariantMapBuilder.result()
//
//		//3. Create method definitions
//		for (classDecl <- program.classes) {
//				for ((methodId, methodDecl) <- classDecl.methods) {
//					addMethodDef(classDecl, methodDecl)
//				}
//		}
//
//
//		//4. Check properties
//		for ((classId, typeRep) <- repTable) {
//			typeRep match {
//				case objTypeRep@ObjectClassRep(sort, accessors, methods) =>
//					for ((methodId, mthdRep) <- methods) {
//						mthdRep match {
//							case UpdateMethodRep(funcDecl) =>
//								val inv = invariantMap(classId).funcDecl
//								val arguments : Array[Expr[_]] = funcDecl.getDomain.map(sort => ctx.mkFreshConst("arg", sort))
//								val s0 = arguments(0)
//
//								val property = ctx.mkForall(
//									arguments,
//									ctx.mkImplies(
//										ctx.mkApp(inv, s0),
//										ctx.mkApp(inv, ctx.mkApp(funcDecl, arguments : _*))
//									),
//									1, null, null, null, null
//								)
//
//								val checkResult = env.solver.check(ctx.mkNot(property))
//								println(s"$classId.$methodId = $checkResult")
//
//							case QueryMethodRep(funcDecl) =>
//						}
//					}
//				case NativeClassRep(sort, methods) =>
//			}
//		}

//		val constructor = ctx.mkConstructor[Sort]("mkPair", "isPair",
//			Array[String]("first", "second"), Array[Sort](null, null), Array[Int](1, 2))
//		val dataTypeSort = ctx.mkDatatypeSort("Pair", Array(constructor))


//		env.solver.add(ctx.mkForall(
//			Array[Expr[_]](ctx.mkFreshConst("s", dataTypeSort)), ctx.mkTrue(), 0, null, null, null, null
//		))

		println("Done.")
	}

	private def sortId(classId : ClassId, typeArguments : Seq[Sort]) : String =
		classId + "[" +  typeArguments.map(sort => sort.toString).mkString(",") + "]"

	private def className(classId : ClassId, typeArguments : Seq[Sort]) : String =
		s"Class$$${sortId(classId, typeArguments)}"

	private def fieldName(classId : ClassId, typeArguments : Seq[Sort], fieldId: FieldId) : String =
		s"Field$$${sortId(classId, typeArguments)}$$$fieldId"

	private def queryMethodName(classId : ClassId, typeArguments : Seq[Sort], methodId : MethodId) : String =
		s"Query$$${sortId(classId, typeArguments)}$$$methodId"

	private def updateMethodName(classId : ClassId, typeArguments : Seq[Sort], methodId : MethodId) : String =
		s"Update$$${sortId(classId, typeArguments)}$$$methodId"

	private def createRepTable() : RepTable = {
		import env.ctx

		// 1st iteration: Build the map with all datatypes for the classes
		val repMapBuilder = new RepMapBuilder
		for (classDecl <- program.classes) {
			classDecl match {
				case NativeClassDecl(classId, typeParameters, sortImpl, methods) =>
					repMapBuilder.addNativeClassBuilder(classId, sorts => {
						require(typeParameters.length == sorts.length)
						sortImpl(ctx, sorts)
					})

				case ObjectClassDecl(classId, typeParameters, invariant, fields, methods) =>
					val f : Seq[Sort] => (Sort, Map[FieldId, FieldRep]) = sorts => {
						require(typeParameters.length == sorts.length)

						/* 1. Initialize the sort of the class. */
						val sortName = className(classId, sorts)

						val numOfFields = fields.size
						val fieldSeq = fields.toSeq

						// Create the z3 sort for states of this class.
						val fieldNames = new Array[Z3Symbol](numOfFields)
						val fieldSorts = new Array[Sort](numOfFields)

						val typeVarSorts : Map[TypeVarId, Sort] = classDecl.typeParametersMapTo(sorts)

						for (((fieldId, fieldDecl), i) <- fieldSeq.zipWithIndex) {
							fieldNames(i) = ctx.mkSymbol(fieldName(classId, sorts, fieldId))
							fieldSorts(i) = repMapBuilder.resolveType(fieldDecl.typ, typeVarSorts)
						}

						val classSort = ctx.mkTupleSort(ctx.mkSymbol(sortName), fieldNames, fieldSorts)

						// Create the field accessors for the class
						val accessorBuilder = Map.newBuilder[FieldId, FieldRep]
						val accessorArr = classSort.getFieldDecls
						for (((fieldId, _), i) <- fieldSeq.zipWithIndex) {
							accessorBuilder.addOne(fieldId, FieldRep(accessorArr(i)))
						}

						(classSort, accessorBuilder.result())
					}

					repMapBuilder.addObjectClassBuilder(classId, f)
			}
		}

		// 2nd iteration: Build the method declarations for each class
		for (classDecl <- program.classes) {

			val classMethodBuilder = Map.newBuilder[MethodId, MethodRep]
			for ((methodId, methodDecl) <- classDecl.methods) {

				val f : Seq[Sort] => MethodRep = sorts => {
					val typeVarSorts : Map[TypeVarId, Sort] = classDecl.typeParametersMapTo(sorts)

					val declaredParameterSorts : Seq[Sort] = methodDecl.declaredParameters.map(decl => repMapBuilder.resolveType(decl.typ, typeVarSorts))
					val classSort = repMapBuilder.getClassSort(classDecl.classId, sorts).getOrElse(throw new ModelException("class not available: " + classDecl.classId))
					//Add the receiver object to the Z3 function parameters
					val actualParameterSorts : Seq[Sort] = Seq(classSort) ++ declaredParameterSorts

					methodDecl match {
						case query : QueryMethodDecl =>
							val methodName = queryMethodName(classDecl.classId, sorts, query.name)
							val returnSort = repMapBuilder.resolveType(query.returnTyp, typeVarSorts)
							val mthdDecl = ctx.mkFuncDecl(methodName, actualParameterSorts.toArray[Sort], returnSort)
							QueryMethodRep(mthdDecl)

						case update : UpdateMethodDecl =>
							val methodName = updateMethodName(classDecl.classId, sorts, update.name)
							val mthdDecl = ctx.mkFuncDecl(methodName, actualParameterSorts.toArray[Sort], classSort)


						case updateDecl@ObjectUpdateMethodDecl(name, parameters, body) =>
							val methodName = updateMethodName(classDecl.classId, sorts, name)
							val mthdDecl = ctx.mkFuncDecl(methodName, actualParameterSorts.toArray[Sort], classSort)

							val receiverExpr = ctx.mkFreshConst("s0", classSort)

							val declaredArguments : Seq[Expr[_]] = methodDecl.declaredParameters.map(varDecl => {
								val varSort = repMapBuilder.resolveType(varDecl.typ, typeVarSorts)
								ctx.mkFreshConst(varDecl.name, varSort)
							})

							val declaredArgumentsMap = methodDecl.declaredParameters.zip(declaredArguments).map(t => (t._1.name, t._2)).toMap


							val (bodyVal, bodyState) : (Expr[_], Expr[_]) = new MutableClassExpressionCompiler(classDecl.classId).compile(body, declaredArgumentsMap, receiverExpr)
//
//							val methodDef = ctx.mkForall(
//								(Seq(receiverExpr) ++ declaredArguments).toArray,
//								ctx.mkEq(ctx.mkApp(methodRep.funcDecl, (Seq(receiverExpr) ++ declaredArguments).toArray : _*), bodyState),
//								1,
//								null,
//								null,
//								null,
//								null
//							)
//
//							env.solver.add(methodDef)




							UpdateMethodRep(mthdDecl)
					}

					//TODO: Add method definition
				}

				repMapBuilder.addMethodBuilder(classDecl.classId, methodId, f)
			}

		}

//
//
//		// 3rd: Combine class and method map to create the type map
//		val repMapBuilder = Map.newBuilder[ClassId, ClassRep]
//		for ((classId, classRep) <- tempRepMap) {
//			classRep match {
//				case TempNativeClassRep(sort) =>
//					repMapBuilder.addOne(classId, NativeClassRep(
//						sort,
//						methodMap.getOrElse(classId, Map())
//					))
//
//				case TempObjectClassRep(sort, accessors) =>
//					repMapBuilder.addOne(classId, ObjectClassRep(sort, accessors, methodMap.getOrElse(classId, Map())))
//			}
//		}
//
//		repMapBuilder.result()

		???

	}

	private def addMethodDef(classDecl : ClassDecl[_], methodDecl : MethodDecl)(implicit repTable : RepTable, classTable : ClassTable) : Unit = {
		implicit val ctx : Context = env.ctx

//		val classRep = repTable
//			.getOrElse(classDecl.classId, throw new ModelException("class not in rep map: " + classDecl))
//
//		val methodRep = classRep.methods
//			.getOrElse(methodDecl.name,	throw new ModelException("method not found: " + methodDecl))
//
//		val receiverExpr = ctx.mkFreshConst("s0", classRep.sortFactory)
//
//		val declaredArguments : Seq[Expr[_]] = methodDecl.declaredParameters.map(varDecl => {
//			val varClassRep = repTable.getOrElse(varDecl.typ.name, throw new ModelException("Unknown type: " + varDecl.typ))
//			ctx.mkFreshConst(varDecl.name, varClassRep.sortFactory)
//		})
//
//		val declaredArgumentsMap = methodDecl.declaredParameters.zip(declaredArguments).map(t => (t._1.name, t._2)).toMap
//
//		methodDecl match {
//			case ObjectQueryMethodDecl(name, parameters, returnTyp, body) =>
//				val (bodyVal, bodyState) = new ClassExpressionCompiler(classDecl.classId).compile(body, declaredArgumentsMap, receiverExpr)
//
//				val methodDef = ctx.mkForall(
//					(Seq(receiverExpr) ++ declaredArguments).toArray,
//					ctx.mkEq(ctx.mkApp(methodRep.funcDecl, (Seq(receiverExpr) ++ declaredArguments).toArray : _*), bodyVal),
//					1,
//					null,
//					null,
//					null,
//					null
//				)
//
//				env.solver.add(methodDef)
//
//
//
//			case NativeQueryMethodDecl(name, declaredParameters, returnTyp, impl) =>
//				val implVal = impl.apply(ctx, receiverExpr, declaredArguments)
//
//				val methodDef = ctx.mkForall(
//					(Seq(receiverExpr) ++ declaredArguments).toArray,
//					ctx.mkEq(ctx.mkApp(methodRep.funcDecl, (Seq(receiverExpr) ++ declaredArguments).toArray : _*), implVal),
//					1,
//					null,
//					null,
//					null,
//					null
//				)
//
//				env.solver.add(methodDef)
//		}
	}

	private def addInvariantDef(classDecl : ObjectClassDecl)(implicit repTable : RepTable, classTable : ClassTable) : InvariantRep = {
//		implicit val ctx : Context = env.ctx
//
//		val typeRep = repTable.get(classDecl.classId) match {
//			case Some(x : ObjectClassRep) => x
//			case _ => throw new ModelException("class not in type map or no object class: " + classDecl)
//		}
//
//		val invDecl = ctx.mkFuncDecl(classDecl.classId + "$inv" , typeRep.sortFactory, ctx.getBoolSort)
//
//		val invArg = ctx.mkFreshConst("s0", typeRep.sortFactory)
//		val (invExpr, invState) = new ClassExpressionCompiler(classDecl.classId).compile(classDecl.invariant, Map(), invArg)
//
//		env.solver.add(
//			ctx.mkForall(Array(invArg),
//				ctx.mkEq(ctx.mkApp(invDecl, invArg), invExpr.asInstanceOf[Expr[BoolSort]]),
//				1,
//				null,
//				null,
//				null,
//				null
//			)
//		)
//
//		InvariantRep(invDecl)
		???
	}


	/*def parseMethod(method : MethodDecl) : Any = {
		env.ctx.mkDatatypeSort()

	}


	def parse(expr : IRExpr) : Z3Expr[_] = expr match {
		case Num(n) => env.ctx.mkInt(n)
		case Var(id) => env.ctx.
	}*/

}
