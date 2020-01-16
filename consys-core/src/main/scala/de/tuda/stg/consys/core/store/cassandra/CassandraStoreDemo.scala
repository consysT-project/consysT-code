package de.tuda.stg.consys.core.store.cassandra

import java.util.concurrent.{ExecutorService, Executors}

import de.tuda.stg.consys.core.store.{Handler, StoreConsistencyLevel}

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

	val level = Strong

	println("transaction 1")
	store1.transaction { ctx =>
		import ctx._
		val int1 = replicate[MyInt]("myint1", new MyInt, level)
		val int2 = replicate[MyInt]("myint2", new MyInt, level)
		replicate[MyInts]("myints", new MyInts(int1, int2), level)

		Some(())
	}

//	println("transaction 2")
//	store2.transaction { ctx =>
//		import ctx._
//		val ints = lookup[MyInts]("myints", Strong)
//		ints.invoke("double", Seq(Seq()))
//
//		Some (())
//	}

	implicit val exec : ExecutionContext = ExecutionContext.fromExecutorService(Executors.newFixedThreadPool(4))

	println("transaction 3")
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
		case Success(value) => println(store3.name + " woop woop")
	}


	private def doTx(str : CassandraStore) : Unit = str.transaction { ctx =>
		import ctx._
		val obj1 = lookup[MyInt]("myint1", level)
		obj1.invoke("double", Seq(Seq()))
		obj1.invoke("inc", Seq(Seq()))
		obj1.invoke("inc", Seq(Seq()))
		obj1.invoke("half", Seq(Seq()))
		println(str.name + ": " + obj1.invoke("get", Seq()))
		Some (())
	}


	Thread.sleep(100000)

	store1.close()
	store2.close()
	store3.close()

	class MyInts(
		val i : CassandraHandler[MyInt],
		val j : CassandraHandler[MyInt]
  ) extends Serializable {
		def double() : Unit = {
			i.resolve().invoke("double", Seq(Seq()))
			j.resolve().invoke("double", Seq(Seq()))
		}
	}


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
