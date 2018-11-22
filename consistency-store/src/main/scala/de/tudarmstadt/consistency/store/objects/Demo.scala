package de.tudarmstadt.consistency.store.objects

import de.tudarmstadt.consistency.store.objects.DistributedObjects.InterpreterImpl
import de.tudarmstadt.consistency.store.objects.PropagationConsistencyDef._

/**
	* Created on 15.11.18.
	*
	* @author Mirko Köhler
	*/
object Demo {

	def interpExample() : Unit = {
		import InterpreterImpl._

		val replica1 = new CurrentTimeMillisReplica(1,
			Map(
				100 -> StoreEntry((0L, 1).asInstanceOf[Timestamp], Causal, Num(42)),
				101 -> StoreEntry((0L, 2) : Timestamp, Causal, Num(23)),
				102 -> StoreEntry((0L, 2) : Timestamp, Causal, Num(12))
			)
		)

		val replica2 = new CurrentTimeMillisReplica(2,
			Map(
				101 -> StoreEntry((0L, 2) : Timestamp, Causal, Num(23)),
				102 -> StoreEntry((1L, 2) : Timestamp, Causal, Num(56))
			)
		)

		val conf1 = Conf(replica1, Map.empty, Return(Num(99)))
		val conf2 = Conf(replica2, Map.empty, Return(Num(77)))

		var world : Option[Seq[Conf]] = Some(Seq(conf1, conf2))
		println(world)

		world = world.flatMap(ws => propagateStep(ws))
		println(world)

		world = world.flatMap(ws => propagateStep(ws))
		println(world)

		world = world.flatMap(ws => propagateStep(ws))
		println(world)

		world = world.flatMap(ws => propagateStep(ws))
		println(world)

		world = world.flatMap(ws => propagateStep(ws))
		println(world)
	}

	def typeExample() : Unit = {
		import InterpreterImpl._

		val expr1 : Expression = Fun('x, Local, Annotated(TRef(Annotated(TInt, Sequential)), Local),
			Return(Fun('y, Local, Annotated(TInt, Local),
				Do('a, UpdateRef(Var('x), Var('y)),
					Return(Var('a))
				)
			))
		)

		val lam1 : Expression = Fun('x, Inconsistent, Annotated(TInt, Sequential),
			Do('a, Return(Ref(Annotated(TInt, Causal), 1)),
				UpdateRef(Var('a), Var('x))
			)
		)

		val cmpt1 : Computation =
			Do('a, Deref(Ref(Annotated(TInt, Causal), 1)),
				Do('r, Return(Var('a)),
					UpdateRef(
						Ref(Annotated(TInt, Sequential), 2),
						Var('r)
					)
				)
			)



		implicit val ct : ClassTable = Map.empty
		println(typeOf(lam1, Map.empty : TypeEnvironment))

	}


	def typeExample2() : Unit = {
		import InterpreterImpl._

		def BoolBranchType(typ : Type) : Annotated = Annotated(typ, Local)


//		def True(typ : Type) : Expression = Fun('x, Local, BoolBranchType(typ),
//			Return(Fun('y, Local, BoolBranchType(typ),
//				Return(Var('x))
//		)))
//
//		//TRef(Annotated(TInt, Causal))
//
//		def False(typ : Type) : Expression = Fun('x, Local, BoolBranchType(typ),
//			Return(Fun('y, Local, BoolBranchType(typ),
//				Return(Var('y))
//			)))

		def ifte(e : Expression, thenBranch : Expression, elseBranch : Expression) : Computation =
			Do('x, App(e, thenBranch), App(Var('x), elseBranch))

		def BoolType(typ : Type) : Type = TFun(BoolBranchType(typ), Linearizable,
			Annotated(TFun(BoolBranchType(typ), Linearizable, BoolBranchType(typ)), Local))

		val BranchType : Type = TFun(Annotated(TUnit, Local), Sequential, Annotated(TUnit, Local))

		def doSomething : Computation =
			Do('weak, Return(Ref(Annotated(BoolType(BranchType), Linearizable), 1)),
				Do('i, Return(Ref(Annotated(TInt, Sequential), 2)),
					Do('weakBool, Deref(Var('weak)),
						Do('fun ,ifte(Var('weakBool),
									Fun('a, Sequential, Annotated(TUnit, Local), UpdateRef(Var('i), Num(42))),
									Fun('a, Sequential, Annotated(TUnit, Local), UpdateRef(Var('i), Num(41)))
								),
							App(Var('fun), UnitVal)
							)
						)
					)
				)


		def fun : Computation =
			Return(Fun('x, Causal, Annotated(TInt, Causal),
				Do('a, UpdateRef(Ref(Annotated(TInt, Sequential), 1), Num(2)),
					Do('b, UpdateRef(Ref(Annotated(TInt, Causal), 2), Num(522)),
						Return(Num(0))
					)
				)
			))


		implicit val ct : ClassTable = Map.empty
//		println(typeOf(ifte(True(TInt), Num(1), Num(2)), Local, Map.empty : TypeEnvironment))
		println(typeOf(doSomething, Local, Map.empty : TypeEnvironment))


	}

	/*
		class X {
			@Strong int i
			@Weak int j
			@Weak Ref[H] h
		}
		class H {
			@Strong int k
		}

		Process P0 executes the following program:

		@Strong Ref[H] h = new H(3) //$1
		Ref[X] x = new @Strong X(1, 2, h) //$2
		h.k = 45 //u1 Strong
		x.j = 60 //u2 Weak
		x.i = 75 //u3 Strong
	 */
	def googleDocExample(): Unit = {
		import InterpreterImpl._

		implicit val ct : ClassTable = Map(
			'X -> ClassDef('X, Root,
				Map(
					'i -> TRef(Annotated(TInt, Sequential)),
					'j -> TRef(Annotated(TInt, Causal)),
					'h -> TRef(Annotated(TClass(Class('H)), Causal))
				)
			),
			'H -> ClassDef('H, Root,
				Map(
					'k -> TRef(Annotated(TInt, Sequential))
				)
			)
		)

		val hconstFields : Map[FieldName, Expression] = Map(
			'k -> Ref(Annotated(TInt, Sequential), 200)
		)

		val xconstFields : Map[FieldName, Expression] = Map(
			'i -> Ref(Annotated(TInt, Sequential), 100),
			'j -> Ref(Annotated(TInt, Causal), 101),
			'h -> Ref(Annotated(TClass(Class('H)), Causal), 102)
		)

		val example1 =
			Do('href, Enref(Sequential, New(Class('H), hconstFields)),
			Do('xref, Enref(Sequential, New(Class('X), xconstFields)),
			Do('h1, Deref(Var('href)),
			Do('_, UpdateRef(FieldRead(Var('h1), 'k), Num(42)),
			Do('x1, Deref(Var('xref)),
			Do('xh, Deref(FieldRead(Var('x1), 'h)),
			Do('res, Deref(FieldRead(Var('xh), 'k)),
			Do('_, UpdateRef(FieldRead(Var('xh), 'k), Num(24)),
				Return(Var('res))
			))))))))


		println(typeOf(example1, Local, Map.empty))


	}


	def main(args : Array[String]) : Unit = {
		googleDocExample()

//		import PropagationConsistencyDef._
//		import PropagationConsistencyDef.PropagationConsistencyLattice._
//
//		assert(!smallerEq(Inconsistent, Local))
//		assert(!smallerEq(MonotonicReads, Causal))
//		assert(!smallerEq(Sequential, Linearizable))
//		assert(!smallerEq(Inconsistent, MonotonicWrites))
//		assert(!smallerEq(Inconsistent, MonotonicReads))
//
//		assert(smallerEq(Inconsistent, Inconsistent))
//		assert(smallerEq(Local, Local))
//		assert(smallerEq(Linearizable, Sequential))
//		assert(smallerEq(Linearizable, MonotonicWrites))
//		assert(smallerEq(Sequential, MonotonicReads))
//
//		assert(!smallerEq(MonotonicWrites, MonotonicReads))
//		assert(!smallerEq(MonotonicReads, MonotonicWrites))
//		assert(!smallerEq(Inconsistent, MonotonicReads))
//
//		assert(smallerEq(MonotonicWrites, MonotonicWrites))
//		assert(smallerEq(MonotonicReads, MonotonicReads))
	}
}
