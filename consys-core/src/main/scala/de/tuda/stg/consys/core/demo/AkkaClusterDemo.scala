package de.tuda.stg.consys.core.demo

import de.tuda.stg.consys.core.store.akkacluster.AkkaClusterStore
import de.tuda.stg.consys.core.store.akkacluster.level.{Strong, Weak}
import de.tuda.stg.consys.core.store.utils.SinglePortAddress
import de.tuda.stg.consys.logging.Logger

import java.util.concurrent.{Executors, ThreadPoolExecutor}

object AkkaClusterDemo {

	def main(args : Array[String]) : Unit = {

		val nodes = Seq(SinglePortAddress("127.0.0.1", 4445), SinglePortAddress("127.0.0.2", 4446))

		val exec = Executors.newFixedThreadPool(4)

		exec.submit(new Runnable {
			override def run() : Unit = {
				val store1 = AkkaClusterStore.fromAddress("127.0.0.1", 4445, 2181, nodes)

				store1.transaction(ctx => {
					val s1 = ctx.replicate[String]("string1", Weak, "Hallo Welt!")
					Some(())
				})

				println("Done 1")
			}
		})


		exec.submit(new Runnable {
			override def run() : Unit = {
				val store2 = AkkaClusterStore.fromAddress("127.0.0.2", 4446, 2182, nodes)

				store2.transaction(ctx => {
					val s1 = ctx.lookup[String]("string1", Weak)
					val string = s1.resolve().invoke[String]("toString", Seq())
					Logger.info(string)
					Some(())
				})

				println("Done 2")
			}
		})




	}

}
