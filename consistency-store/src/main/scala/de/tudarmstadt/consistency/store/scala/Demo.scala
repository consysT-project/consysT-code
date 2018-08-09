package de.tudarmstadt.consistency.store.scala

import java.util.concurrent.Executors

import de.tudarmstadt.consistency.checker.qual.Strong
import de.tudarmstadt.consistency.store.scala.impl.ReadWriteStore
import de.tudarmstadt.consistency.store.scala.local.MapStore
import de.tudarmstadt.consistency.store.scala.shim.{Update, VersionedStore}

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

	def main(args : Array[String]): Unit = {
		val store = new VersionedStore[Char, String] {
			override type Id = Int
			override val store: ReadWriteStore[Id, Update[Id, Char, String]] = new MapStore[Id, Update[Id, Char, String]]
			override val idFactory: () => Id = () => Random.nextInt()
		}

		example2(store)

		executor.shutdown()

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
			})
		}
	}

	def example2(store : VersionedStore[Char, String]): Unit = {

		//Alice session
		Future {
			store.commit(session => {

				val alice = session.obtain[String]('a', classOf[Strong])
				val bob = session.obtain[String]('b', classOf[Strong])
				val charlie = session.obtain[String]('c', classOf[Strong])

				alice := "w1"
				Thread.sleep(200)
				val r4 = bob()
				alice := "w6"
				Thread.sleep(200)
				val r7 = charlie()
				alice := "w8"

				session.printSessionTree()
			})
		}


		//Bob session
		Future {
			store.commit(session => {

				val alice = session.obtain[String]('a', classOf[Strong])
				val bob = session.obtain[String]('b', classOf[Strong])

				Thread.sleep(100)
				val r2 = alice()
				bob := "w3"

				session.printSessionTree()
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
