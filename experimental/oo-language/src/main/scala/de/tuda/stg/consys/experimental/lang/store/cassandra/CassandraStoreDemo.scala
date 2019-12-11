package de.tuda.stg.consys.experimental.lang.store.cassandra

import java.net.InetSocketAddress

import com.datastax.oss.driver.api.core.CqlSession
import de.tuda.stg.consys.demo.Demo.A

/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
object CassandraStoreDemo extends App {

	val store = new CassandraStore("127.0.0.1", 9042)


	val count = store.transaction { ctx =>
		val obj1 = ctx.replicate("obj1", new ClsA, Weak)
		val count = obj1.invoke[Int]("inc", Seq(Seq()))
		println(count)
		Some(count)
	}

	println(count)


	val count2 = store.transaction { ctx =>
		val obj1 = ctx.lookup[ClsA]("obj1", Weak)
		val count = obj1.invoke[Int]("inc", Seq(Seq()))
		println(count)

		val obj2 = ctx.lookup[ClsA]("obj1", Weak)
		val count2 = obj2.invoke[Int]("inc", Seq(Seq()))

		Some(count2)
	}

	println(count2)

	store.close()

	class ClsA extends Serializable {
		var count = 0
		def inc(): Int = {
			count = count + 1;
			count
		}
	}

}
