package de.tuda.stg.consys.core.demo

import de.tuda.stg.consys.Mergeable
import de.tuda.stg.consys.annotations.methods.{StrongOp, WeakOp}
import de.tuda.stg.consys.core.store.akkacluster.AkkaClusterStore
import de.tuda.stg.consys.core.store.akkacluster.level.{Mixed, Strong, Weak}
import de.tuda.stg.consys.core.store.utils.SinglePortAddress
import de.tuda.stg.consys.logging.Logger

import java.util.concurrent.{Executors, ThreadPoolExecutor}
import scala.collection.mutable

object AkkaClusterDemo {


	class MergeableSet extends Mergeable[MergeableSet] with java.io.Serializable {

		private val underlying : mutable.Set[Int] = mutable.HashSet.empty

		@StrongOp def add(elem : Int) : Unit = {
			underlying.add(elem)
		}

		override def merge(other : MergeableSet) : Void = {
			underlying.addAll(other.underlying)
			null
		}

		@WeakOp override def toString : String = s"Mergeable<$underlying>"
	}


	def main(args : Array[String]) : Unit = {

		val nodes = Seq(SinglePortAddress("127.0.0.1", 4445), SinglePortAddress("127.0.0.2", 4446))

		val exec = Executors.newFixedThreadPool(4)

		exec.submit(new Runnable {
			override def run() : Unit = {
				val store1 = AkkaClusterStore.fromAddress("127.0.0.1", 4445, 2181, nodes)

				store1.transaction(ctx => {
					val s1 = ctx.replicate[MergeableSet]("set1", Mixed)
					s1.resolve().invoke("add", Seq(Seq(42)))
					Some(())
				})

				println("Done 1.1")
				Thread.sleep(2000)

				store1.transaction(ctx => {
					val s1 = ctx.lookup[MergeableSet]("set1", Mixed)
					val string = s1.resolve().invoke[String]("toString", Seq())
					Logger.info(string)
					Some(())
				})

				println("Done 1.2")
			}
		})


		exec.submit(new Runnable {
			override def run() : Unit = {
				val store2 = AkkaClusterStore.fromAddress("127.0.0.2", 4446, 2182, nodes)

				store2.transaction(ctx => {
					val s1 = ctx.replicate[MergeableSet]("set1", Mixed)
					s1.resolve().invoke("add", Seq(Seq(23)))
					val string = s1.resolve().invoke[String]("toString", Seq())
					Logger.info(string)
					Some(())
				})

				println("Done 2")
			}
		})




	}

}
