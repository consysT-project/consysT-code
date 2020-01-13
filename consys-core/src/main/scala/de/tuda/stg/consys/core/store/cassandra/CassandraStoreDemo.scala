package de.tuda.stg.consys.core.store.cassandra

import java.util.concurrent.Executors

import scala.concurrent.duration.Duration
import scala.concurrent.{ExecutionContext, ExecutionContextExecutorService, Future}
import scala.util.{Failure, Success}

/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
object CassandraStoreDemo extends App {

	val store1 = CassandraStore.fromAddress("127.0.0.1", 9042, 2181, withTimeout = Duration(60, "s"), withInitialize = true)
	val store2 = CassandraStore.fromAddress("127.0.0.2", 9042, 2182, withTimeout = Duration(60, "s"), withInitialize = false)
	val store3 = CassandraStore.fromAddress("127.0.0.3", 9042, 2183, withTimeout = Duration(60, "s"), withInitialize = false)


	store1.transaction { ctx =>
		ctx.replicate[MyInt]("myint", new MyInt, Strong)
		Some(())
	}

	implicit val exec = ExecutionContext.fromExecutorService(Executors.newFixedThreadPool(4))

	Future {
		for (i <- 1 to 10) doTx(store2)
	} onComplete {
		case Failure(exception) => exception.printStackTrace()
		case Success(value) => println(store2.name + " woop woop")
	}
	Future {
		for (i <- 1 to 10) doTx(store3)
	} onComplete {
		case Failure(exception) => exception.printStackTrace()
		case Success(value) => println(store3.name + "woop woop")
	}


	private def doTx(store : CassandraStore) : Unit = store.transaction { ctx =>
		val obj1 = ctx.lookup[MyInt]("myint", Strong)
		obj1.invoke("double", Seq(Seq()))
		obj1.invoke("inc", Seq(Seq()))
		obj1.invoke("inc", Seq(Seq()))
		obj1.invoke("half", Seq(Seq()))
		println(store.name + ": " + obj1.invoke("get", Seq()))
		Some (())
	}

	Thread.sleep(100000)


	store1.close()
	store2.close()
	store3.close()



	class MyInt extends Serializable {
		var i : Int = 0

		def double() : Unit = {
			i = 2 * i
		}

		def half() : Unit = {
			i = i / 2
		}

		def inc() : Unit = {
			i = i + 1
		}

		def get : Int = {
			i
		}


	}

}
