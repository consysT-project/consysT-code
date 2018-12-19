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
				100 -> StoreEntry((0L, 1), Causal, Num(42)),
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

		val expr1 : Computation = Return(
				Fun('x, Local, Annotated(TRef(Annotated(TInt, Sequential)), Local),
				Return(Fun('y, Local, Annotated(TInt, Local),
					Do('a, UpdateRef(Id('x), Id('y)),
						Return(Id('a))
					)
				))
			)
		)

		val lam1 : Computation = Return(
			Fun('x, Inconsistent, Annotated(TInt, Sequential),
				Do('a, Return(Ref(Annotated(TInt, Causal), 1)),
					UpdateRef(Id('a), Id('x))
				)
			)
		)

		val cmpt1 : Computation =
			Do('a, Deref(Ref(Annotated(TInt, Causal), 1)),
				Do('r, Return(Id('a)),
					UpdateRef(
						Ref(Annotated(TInt, Causal), 2),
						Id('r)
					)
				)
			)

		implicit val ct : ClassTable = Map.empty
		println(typeOf(cmpt1, Map.empty : TypeEnvironment))

	}


	def typeExample2() : Unit = {
		import InterpreterImpl._

		def BoolBranchType(typ : Type) : Annotated = Annotated(typ, Local)

//		def True(typ : Type) : Expression = Fun('x, Local, BoolBranchType(typ),
//			Return(Fun('y, Local, BoolBranchType(typ),
//				Return(Var('x))
//		)))
//		def False(typ : Type) : Expression = Fun('x, Local, BoolBranchType(typ),
//			Return(Fun('y, Local, BoolBranchType(typ),
//				Return(Var('y))
//			)))

		def ifte(e : Expression, thenBranch : Expression, elseBranch : Expression) : Computation =
			Do('x, App(e, thenBranch), App(Id('x), elseBranch))

		def BoolType(typ : Type) : Type = TFun(BoolBranchType(typ), Causal,
			Annotated(TFun(BoolBranchType(typ), Causal, BoolBranchType(typ)), Local))

		val BranchType : Type = TFun(Annotated(TUnit, Local), Causal, Annotated(TUnit, Local))

		def doSomething : Computation =
			Do('weak, Return(Ref(Annotated(BoolType(BranchType), Causal), 1)),
				Do('i, Return(Ref(Annotated(TInt, Sequential), 2)),
					Do('weakBool, Deref(Id('weak)),
						Do('fun ,ifte(Id('weakBool),
									Fun('a, Sequential, Annotated(TUnit, Local), UpdateRef(Id('i), Num(42))),
									Fun('a, Sequential, Annotated(TUnit, Local), UpdateRef(Id('i), Num(41)))
								),
							App(Id('fun), UnitVal)
							)
						)
					)
				)

		implicit val ct : ClassTable = Map.empty
//		println(typeOf(ifte(True(TInt), Num(1), Num(2)), Local, Map.empty : TypeEnvironment))
		println(typeOf(doSomething, Map.empty : TypeEnvironment))
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

		val example1 : Computation =
			Do('href, Enref(Sequential, New(Class('H), hconstFields)),
			Do('xref, Enref(Sequential, New(Class('X), xconstFields)),
			Do('h1, Deref(Id('href)),
			Do('_, UpdateRef(FieldRead(Id('h1), 'k), Num(42)),
			Do('x1, Deref(Id('xref)),
			Do('xh, Deref(FieldRead(Id('x1), 'h)),
			Do('res, Deref(FieldRead(Id('xh), 'k)),
			Do('asd, UpdateRef(FieldRead(Id('xh), 'k), Num(24)),
				Return(Id('res))
			))))))))


		println(typeOf(example1, Map.empty : TypeEnvironment))


	}


	def main(args : Array[String]) : Unit = {
//		googleDocExample()
//		typeExample()
//			typeExample2()

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
