package de.tuda.stg.consys.core.store.akka

import de.tuda.stg.consys.Mergeable
import de.tuda.stg.consys.core.store.ConsistencyLevel
import de.tuda.stg.consys.core.store.akka.levels.{Strong, Weak}
import org.checkerframework.dataflow.qual.SideEffectFree

import scala.collection.mutable

object AkkaStoreDemo {

	case class Box(var f : Any) extends java.io.Serializable {
		@SideEffectFree def get : Any = f
	}

	class MergeableSet extends Mergeable[MergeableSet] with java.io.Serializable {

		private val underlying : mutable.Set[Int] = mutable.HashSet.empty

		def add(elem : Int) : Unit = {
			underlying.add(elem)
		}

		override def merge(other : MergeableSet) : Void = {
			underlying.addAll(other.underlying)
			null
		}

		override def toString : String = s"Mergeable<$underlying>"
	}


	def main(args : Array[String]) {

		val exampleConsistency : ConsistencyLevel[AkkaStore] = Strong

		val store1 = AkkaStore.fromAddress("127.0.0.1", 4445, 2181)
		val store2 = AkkaStore.fromAddress("127.0.0.2", 4446, 2182)

		store1.replica.addOtherReplica(store2.getAddress)
		store2.replica.addOtherReplica(store1.getAddress)


		store1.transaction(ctx => {
			val set1 = ctx.replicate[MergeableSet]("set1", exampleConsistency)
			set1.resolve(ctx).invoke("add", Seq(Seq(23)))
			set1.resolve(ctx).invoke("add", Seq(Seq(42)))
			println("Done 1")
			Some(())
		})


		store2.transaction(ctx => {
			val set1 = ctx.replicate[MergeableSet]("set1", exampleConsistency)
			set1.resolve(ctx).invoke("add", Seq(Seq(24)))
			set1.resolve(ctx).invoke("add", Seq(Seq(43)))
			println("Done 2")
			Some(())
		})


		store1.transaction(ctx => {
			val set1 = ctx.lookup[MergeableSet]("set1", exampleConsistency)
			val result = set1.resolve(ctx).invoke[String]("toString", Seq())
			println(s"store 1: $result")
			Some(())
		})

		store2.transaction(ctx => {
			val set1 = ctx.lookup[MergeableSet]("set1", exampleConsistency)
			val result = set1.resolve(ctx).invoke[String]("toString", Seq())
			println(s"store 2: $result")
			Some(())
		})
	}
}