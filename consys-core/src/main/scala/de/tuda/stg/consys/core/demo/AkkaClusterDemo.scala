package de.tuda.stg.consys.core.demo

import de.tuda.stg.consys.core.store.akkacluster.AkkaClusterStore
import de.tuda.stg.consys.core.store.akkacluster.level.Strong
import de.tuda.stg.consys.core.store.utils.SinglePortAddress

object AkkaClusterDemo {

	def main(args : Array[String]) : Unit = {

		val nodes = Seq(SinglePortAddress("127.0.0.1", 4445), SinglePortAddress("127.0.0.2", 4446))

		val store1 = AkkaClusterStore.fromAddress("127.0.0.1", 4445, 2181, nodes)
		val store2 = AkkaClusterStore.fromAddress("127.0.0.2", 4446, 2182, nodes)

		store1.transaction(ctx => {
			val set1 = ctx.replicate[String]("string1", Strong, "Hallo Welt!")
			Some(())
		})

		println("Done")

	}

}
