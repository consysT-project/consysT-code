//package de.tuda.stg.consys.demo
//
//import java.util.concurrent.Executors
//import de.tuda.stg.consys.core.store.akka.{AkkaRef, AkkaStore}
//import de.tuda.stg.consys.core.store.akka.levels.{Strong, Weak}
//import de.tuda.stg.consys.core.store.utils.Address
//import scala.concurrent.duration.Duration
//import scala.concurrent.{Await, ExecutionContext, Future}
//import scala.util.{Failure, Success}
//
///**
// * Created on 10.12.19.
// *
// * @author Mirko Köhler
// */
//object AkkaStoreDemo extends App {
//
//	implicit val exec : ExecutionContext = ExecutionContext.fromExecutorService(Executors.newFixedThreadPool(4))
//
//	val future1 = Future {
//		AkkaStore.fromAddress("127.0.0.1", 4121, 2181, Seq(Address("127.0.0.1", 4121), Address("127.0.0.2", 4122), Address("127.0.0.3", 4123)), Duration(60, "s"))
//	}
//	val future2 = Future {
//		AkkaStore.fromAddress("127.0.0.2", 4122, 2182, Seq(Address("127.0.0.1", 4121), Address("127.0.0.2", 4122), Address("127.0.0.3", 4123)), Duration(60, "s"))
//	}
//	val future3 = Future {
//		AkkaStore.fromAddress("127.0.0.3", 4123, 2183, Seq(Address("127.0.0.1", 4121), Address("127.0.0.2", 4122), Address("127.0.0.3", 4123)), Duration(60, "s"))
//	}
//
//	val store1 = Await.result(future1, Duration(60, "s"))
//	val store2 = Await.result(future2, Duration(60, "s"))
//	val store3 = Await.result(future3, Duration(60, "s"))
//
//	val level = Strong
//
//	println("transaction 1")
//	store1.transaction { ctx =>
//		import ctx._
//		val int1 = replicate[MyInt]("myint1", level, 47)
//		println("replicated myint1")
//		val int2 = replicate[MyInt]("myint2", level, 47)
//		println("replicated myint2")
//		val ints = replicate[MyInts]("myints", level, int1, int2)
//		println("replicated myints")
//		Some(())
//	}
//
//	println("transaction 2")
//	store2.transaction { ctx =>
//		import ctx._
//		val ints = lookup[MyInts]("myints", level)
//		ints.invoke("double", Seq(Seq()))
//		ints.syncAll()
//
//		Some (())
//	}
//
//	println("transaction 3")
//	store3.transaction { ctx =>
//		import ctx._
//		val int1 = lookup[MyInt]("myint1", level)
//		val int2 = lookup[MyInt]("myint2", level)
//		val ints = lookup[MyInts]("myints", level)
//
//		println(s"int1: ${int1.invoke("toString", Seq(Seq()))}")
//		println(s"int2: ${int2.invoke("toString", Seq(Seq()))}")
//		println(s"ints: ${ints.invoke("toString", Seq(Seq()))}")
//
//		Some(())
//	}
//	println("transaction 3")
//
//	Future {
//		for (i <- 1 to 10) doTx(store2)
//	} onComplete {
//		case Failure(exception) => exception.printStackTrace()
//		case Success(value) => println(store2.id + " woop woop")
//	}
//	Future {
//		for (i <- 1 to 10) doTx(store3)
//	} onComplete {
//		case Failure(exception) => exception.printStackTrace()
//		case Success(value) => println(store3.id + " woop woop")
//	}
//
//
//	private def doTx(str : AkkaStore) : Unit = str.transaction { ctx =>
//		import ctx._
//		val obj1 = lookup[MyInt]("myint1", level)
//		obj1.invoke("double", Seq(Seq()))
//		obj1.invoke("inc", Seq(Seq()))
//		obj1.invoke("inc", Seq(Seq()))
//		obj1.invoke("half", Seq(Seq()))
//		obj1.syncAll()
//		println(str.id + ": " + obj1.invoke("get", Seq()))
//		Some (())
//	}
//
//
//	Thread.sleep(10000)
//
//	println("done.")
//	store1.close()
//	store2.close()
//	store3.close()
//
//
//
//	case class MyInts(
//		i : AkkaRef[MyInt],
//		j : AkkaRef[MyInt]
//  ) {
//		def double() : Unit = {
//			i.resolve().invoke("double", Seq(Seq()))
//			j.resolve().invoke("double", Seq(Seq()))
//		}
//	}
//
//	case class MyInt(var i : Int = 0) extends java.io.Serializable {
//		def double() : Unit = {
//			i = 2 * i
//		}
//		def half() : Unit = {
//			i = i / 2
//		}
//		def inc() : Unit = {
//			i = i + 1
//		}
//		def get : Int = {
//			i
//		}
//
//
//	}
//
//}
