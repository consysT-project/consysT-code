package de.tudarmstadt.consistency.store.scala

import java.util.UUID
import java.util.concurrent.{Executors, TimeUnit}

import com.datastax.driver.core.utils.UUIDs
import de.tudarmstadt.consistency.checker.qual.Strong
import de.tudarmstadt.consistency.store.scala.cassandra.CassandraBlobStore
import de.tudarmstadt.consistency.store.scala.impl.ReadWriteStore
import de.tudarmstadt.consistency.store.scala.local.MapStore
import de.tudarmstadt.consistency.store.scala.shim.VersionedStore

import scala.concurrent.{ExecutionContext, Future}
import scala.util.Random

/**
	* Created on 08.08.18.
	*
	* @author Mirko Köhler
	*/
object Demo {

	private val executor = Executors.newFixedThreadPool(4)
	private implicit val executionContext: ExecutionContext = ExecutionContext.fromExecutor(executor)


	val ids = Seq(new UUID(573489594L, 8675789563L),
		new UUID(573489512L, 1675789528L),
		new UUID(573489456L, 1675789879L),
		new UUID(573489465L, 1675789841L))




	def main(args : Array[String]): Unit = {



		val store = new VersionedStore[Char, String] {
			override type Id = UUID
			override val store : ReadWriteStore[Id, Update] = CassandraBlobStore.local[UUID, Update](3)
			override val idFactory : () => Id = () => UUIDs.random()
		}


		try {
			example1 (store)
			Thread.sleep(5000)
		} finally {
			//Close all asynchronous constructs
			executor.shutdown()
			executor.awaitTermination(30, TimeUnit.SECONDS)

			store.close()
		}

	}



	def example1(store : VersionedStore[Char, String]): Unit = {
		store.commit(session => {
			val x = session.obtain[String]('x', classOf[Strong])
			val y = session.obtain[String]('y', classOf[Strong])

			x := "Oopsie"
			y := "Doopsie"
		})


		Future {
			store.commit(session => {
				val x = session.obtain[String]('x', classOf[Strong])
				val y = session.obtain[String]('y', classOf[Strong])

				x := "Hello"
				y := "World!"

				val xVal = x()
				val yVal = y()

				synchronized {

					print("1: ")
					println(xVal + yVal)
					session.printSessionTree()
				}
			})
		}

		Future {
			store.commit(session => {
				try {
					val x = session.obtain[String]('x', classOf[Strong])
					val y = session.obtain[String]('y', classOf[Strong])

					val s = x()
					y := "not " + s

					val xVal = x()
					val yVal = y()

					synchronized {
						print("2: ")
						println(xVal + yVal)
						session.printSessionTree()
					}
				} catch {
					case e : Exception => e.printStackTrace()
				}

			})
		}
	}

	def example2(store : VersionedStore[Char, String]): Unit = {

		store.commit(session => {
				val alice = session.obtain[String]('a', classOf[Strong])
				val bob = session.obtain[String]('b', classOf[Strong])
				val charlie = session.obtain[String]('c', classOf[Strong])

				alice := "null-a"
				bob := "null-b"
				charlie := "null-c"

				session.printSessionTree()
			})

		//Alice session
		Future {
			store.commit(session => {
				try {
					val alice = session.obtain[String]('a', classOf[Strong])
					val bob = session.obtain[String]('b', classOf[Strong])
					val charlie = session.obtain[String]('c', classOf[Strong])

					alice := "w1"

					Thread.sleep(200)

					val r4 = bob()
					println(s"r4 = $r4")

					alice := "w6"

					Thread.sleep(200)

					val r7 = charlie()
					println(s"r7 = $r4")

					alice := "w8"

					session.printSessionTree()
				} catch {
					case e : Exception => e.printStackTrace()
				}
			})
		}


		//Bob session
		Future {
			store.commit(session => {
				try {
					val alice = session.obtain[String]('a', classOf[Strong])
					val bob = session.obtain[String]('b', classOf[Strong])

					Thread.sleep(100)

					val r2 = alice()
					println(s"r2 = $r2")

					bob := "w3"

					session.printSessionTree()
				} catch {
					case e : Exception => e.printStackTrace()
				}
			})
		}

		//Carol session
		Future {
			store.commit(session => {

				val charlie = session.obtain[String]('c', classOf[Strong])

				Thread.sleep(400)
				charlie := "w5"

				session.printSessionTree()
			})
		}

	}

}
