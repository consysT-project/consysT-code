package de.tuda.stg.consys.core.demo

import de.tuda.stg.consys.annotations.methods.{StrongOp, WeakOp}
import de.tuda.stg.consys.core.store.cassandra.levels.{Mixed, Strong}
import de.tuda.stg.consys.core.store.cassandra.{CassandraRef, CassandraStore}
import java.util.concurrent.Executors
import scala.concurrent.duration.Duration
import scala.concurrent.{ExecutionContext, Future}
import scala.util.{Failure, Success}

/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
object CassandraStoreDemo extends App {

	val store1 = CassandraStore.fromAddress("127.0.0.1", 9042, 2181, withTimeout = Duration(60, "s"), withInitialize = true)
	val store2 = CassandraStore.fromAddress("127.0.0.2", 9042, 2182, withTimeout = Duration(60, "s"))
	val store3 = CassandraStore.fromAddress("127.0.0.3", 9042, 2183, withTimeout = Duration(60, "s"))

	val level = Mixed

	println(s"Starting demo with consistency level $level")
	println("transaction 1")
	store1.transaction { ctx =>
		import ctx._
		val int1 = replicate[MyInt]("myint1", level, 47)
		println("replicated myint1")
		val int2 = replicate[MyInt]("myint2", level, 47)
		println("replicated myint2")
		val ints = replicate[MyInts]("myints", level, int1, int2)
		println("replicated myints")

		int1.invoke("inc", Seq(Seq()))
		println(int1.invoke("get", Seq(Seq())))

		Some(())
	}

	println("transaction 2")
	store2.transaction { ctx =>
		import ctx._
		val ints = lookup[MyInts]("myints", level)
		ints.invoke("double", Seq(Seq()))

		Some (())
	}

	println("transaction 3")
	store3.transaction { ctx =>
		import ctx._
		val int1 = lookup[MyInt]("myint1", level)
		val int2 = lookup[MyInt]("myint2", level)
		val ints = lookup[MyInts]("myints", level)

		println(s"int1: ${int1.invoke("toString", Seq(Seq()))}")
		println(s"int2: ${int2.invoke("toString", Seq(Seq()))}")
		println(s"ints: ${ints.invoke("toString", Seq(Seq()))}")

		Some(())
	}


	implicit val exec : ExecutionContext = ExecutionContext.fromExecutorService(Executors.newFixedThreadPool(4))

	println("transaction 3")
	Future {
		for (i <- 1 to 10) doTx(store2)
	} onComplete {
		case Failure(exception) => exception.printStackTrace()
		case Success(value) => println(store2.id + " woop woop")
	}
	Future {
		for (i <- 1 to 10) doTx(store3)
	} onComplete {
		case Failure(exception) => exception.printStackTrace()
		case Success(value) => println(store3.id + " woop woop")
	}


	private def doTx(str : CassandraStore) : Unit = str.transaction { ctx =>
		import ctx._
		val obj1 = lookup[MyInt]("myint1", level)
		obj1.invoke("double", Seq(Seq()))
		obj1.invoke("inc", Seq(Seq()))
		obj1.invoke("inc", Seq(Seq()))
		obj1.invoke("half", Seq(Seq()))
		println(str.id + ": " + obj1.invoke("get", Seq()))
		Some (())
	}


	Thread.sleep(10000)

	println("done.")
	store1.close()
	store2.close()
	store3.close()



	case class MyInts(
		i : CassandraRef[MyInt],
		j : CassandraRef[MyInt]
  ) {

		@StrongOp def double() : Unit = {
			i.resolve().invoke("double", Seq(Seq()))
			j.resolve().invoke("double", Seq(Seq()))
		}
	}

	case class MyInt(var i : Int = 0) {
		@StrongOp def double() : Unit = {
			i = 2 * i
		}

		@StrongOp def half() : Unit = {
			i = i / 2
		}

		@WeakOp def inc() : Unit = {
			i = i + 1
		}

		@WeakOp def get : Int = {
			i
		}


	}

}
