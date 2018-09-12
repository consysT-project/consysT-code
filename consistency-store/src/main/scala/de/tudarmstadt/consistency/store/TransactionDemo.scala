package de.tudarmstadt.consistency.store

import de.tudarmstadt.consistency.store.ConnectionParams.{LocalCluster, LocalClusterNode1, LocalClusterNode2, LocalClusterNode3}
import de.tudarmstadt.consistency.store.shim.SysnameVersionedStore
import de.tudarmstadt.consistency.utils.Log

import scala.concurrent._
import scala.concurrent.duration.Duration

/**
	* Created on 20.08.18.
	*
	* @author Mirko Köhler
	*/
object TransactionDemo {


	/*
CREATE FUNCTION sumLength(sum int, s text)
CALLED ON NULL INPUT
RETURNS int
LANGUAGE java
AS '
if (s == null && sum == null)
return 0;
else if (sum == null)
return s.length();
else if (s == null)
return sum;
else
return sum + s.length();'


CREATE AGGREGATE aggregateLength(text)
SFUNC sumLength
STYPE int
INITCOND 0;




CREATE OR REPLACE FUNCTION biggerRow(max tuple<int, text>, id int, data text)
CALLED ON NULL INPUT
RETURNS tuple<int, text>
LANGUAGE java
AS '
if (max == null) {
	max.setInt(0, id);
	max.setString(1, data);
	return max;
}


if (max.getInt(0) >= id) {
	return max;
} else {
	max.setInt(0, id);
	max.setString(1, data);
	return max;
}'


CREATE OR REPLACE AGGREGATE maxRow(int, text)
SFUNC biggerRow
STYPE tuple<int, text>
INITCOND (-1, '_');


CREATE FUNCTION function_name(arg0 type0, arg1 type1)
    RETURNS NULL ON NULL INPUT or CALLED ON NULL INPUT
    RETURNS type0
    LANGUAGE java
    AS '
    return (type0) arg0 + arg1';

CREATE AGGREGATE aggregate_name(type1)
    SFUNC function_name
    STYPE type0
    FINALFUNC function_name2
    INITCOND null;


	CREATE FUNCTION maxRow(row <tuple<text, int>>,


	 */

	def timed[T](f : => T) : T = {
		val before = System.nanoTime()
		val t = f
		val after = System.nanoTime()
		Log.info(null, s"Time taken: ${(after - before) / 1000 / 1000}ms")
		t
	}

	def simpleExample(): Unit = {

		val store = Stores.Simple.newStore[String](LocalCluster, initialize = true)
		import store._


		startSession { session =>
			import session._


			val transactionA : Transaction[Unit] = tx => {
				tx.update("x", "Hallo", consistencyLevels.causal)
				tx.update("y", "Welt", consistencyLevels.causal)

				Some ()
			}

			val transactionB : Transaction[Unit] = tx => {
				tx.update("x", "Hello", consistencyLevels.causal)
				tx.update("z", "World", consistencyLevels.causal)

				Some ()
			}

			val transactionB2 : Transaction[Unit] = tx => {
				tx.update("x", "Hola", consistencyLevels.causal)
				tx.update("z", "Amigos", consistencyLevels.causal)

				None
			}

			val transactionC : Transaction[String] = tx => {
				val x = tx.read("x", consistencyLevels.causal)
				println(s"x = $x")
				val y = tx.read("y", consistencyLevels.causal)
				println(s"y = $y")
				val z = tx.read("z", consistencyLevels.causal)
				println(s"z = $z")

				val s = List(x, y, z).flatten.mkString(" ")
				tx.update("s", s, consistencyLevels.causal)

				Some (s)
			}

			val transactionD : Transaction[Unit] = tx => {
				tx.update("x", "Bonjour", consistencyLevels.causal)
				None //Aborts the transaction
			}

			val transactionE : Transaction[String] = tx => {
				val x : Option[String] = tx.read("x", consistencyLevels.causal)

				if (x.contains("Bonjour")) {
					None
				}

				x
			}


			Log.info(null, startTransaction(isolationLevels.snapshotIsolation){
				transactionA
			})


			Log.info(null, startTransaction(isolationLevels.snapshotIsolation){
				transactionB
			})

			Log.info(null, startTransaction(isolationLevels.snapshotIsolation){
				transactionB2
			})

			Log.info(null, startTransaction(isolationLevels.snapshotIsolation){
				transactionD
			})

			Log.info(null, startTransaction(isolationLevels.snapshotIsolation){
				transactionC
			})

			print()

		}

		System.exit(0)
	}


	def multiExample(): Unit = {

		val idOps = Stores.Simple.createSeqIds

		//Note: We a creating a test store. Test stores provide extra meta data when reading a value.
		val stores : Seq[SysnameVersionedStore[Integer, String, Integer, String, String, String, Option[Integer]]]  =  Seq(
			Stores.Simple.newStore[Integer](LocalClusterNode1, idOps = idOps, initialize = true),
			Stores.Simple.newStore[Integer](LocalClusterNode1, idOps = idOps),
			Stores.Simple.newStore[Integer](LocalClusterNode2, idOps = idOps),
			Stores.Simple.newStore[Integer](LocalClusterNode3, idOps = idOps)
		)

		implicit val executionContext : ExecutionContext = ExecutionContext.global

		//Sequential
		{
			val store = stores(0)
			import store._

			startSession { session =>
				//Commit a transaction
				session.startTransaction(isolationLevels.snapshotIsolation) { tx =>
					tx.update("alice", 1000, consistencyLevels.causal)
					tx.update("bob", 1000, consistencyLevels.causal)
					tx.update("carol", 1000, consistencyLevels.causal)
					Some()
				}
			}
		}

		//Parallel
		val future1 = Future {
			println("### future 1")
			val store = stores(1)
			import store._

			startSession { session =>
				//Commit a transaction
				val tx1 = session.startTransaction(isolationLevels.snapshotIsolation) { tx =>
					(tx.read("alice", consistencyLevels.causal), tx.read("bob", consistencyLevels.causal)) match {
						case (Some(a), Some(b)) =>
							tx.update("alice", a - 200, consistencyLevels.causal)
							tx.update("bob", b + 200, consistencyLevels.causal)
							Some ()
						case _ =>
							Some ()
					}
				}

				println(s"future 1, tx1 $tx1")

				//Commit a transaction
				val tx2 = session.startTransaction(isolationLevels.snapshotIsolation) { tx =>
					val a = tx.read("alice", consistencyLevels.causal)
					val b = tx.read("bob", consistencyLevels.causal)

					println(s"alice $a, bob $b")

					Some()
				}

				println(s"future 1, tx2 $tx2")
			}

			store.close()
		} recover {
			case e  => e.printStackTrace(System.out)
		}

		val future2 = Future {
			println("### future 2")

			val store = stores(2)
			import store._

			startSession { session =>
				//Commit a transaction
				val tx1 = session.startTransaction(isolationLevels.snapshotIsolation) { tx =>
					(tx.read("alice", consistencyLevels.causal), tx.read("carol", consistencyLevels.causal)) match {
						case (Some(a), Some(c)) =>
							tx.update("alice", a - 300, consistencyLevels.causal)
							tx.update("carol", c + 300, consistencyLevels.causal)
							Some ()
						case _ =>
							Some ()
					}
				}

				println(s"future 2, tx1 $tx1")

				//Commit a transaction
				val tx2 = session.startTransaction(isolationLevels.snapshotIsolation) { tx =>
					val c = tx.read("carol", consistencyLevels.causal)
					println(s"carol $c")
					Some()
				}

				println(s"future 2, tx2 $tx2")
			}

			store.close()
		} recover {
			case e  => e.printStackTrace(System.out)
		}

		val future3 = Future {
			println("### future 3")

			val store = stores(3)
			import store._

			startSession { session =>
				//Commit a transaction
				val tx1 = session.startTransaction(isolationLevels.snapshotIsolation) { tx =>
					(tx.read("alice", consistencyLevels.causal), tx.read("carol", consistencyLevels.causal)) match {
						case (Some(a), Some(c)) =>
							tx.update("alice", a - 50, consistencyLevels.causal)
							tx.update("carol", c + 50, consistencyLevels.causal)
							Some ()
						case _ =>
							Some ()
					}
				}

				println(s"future 3, tx1 $tx1")

				//Commit a transaction
				val tx2 = session.startTransaction(isolationLevels.snapshotIsolation) { tx =>
					val c = tx.read("carol", consistencyLevels.causal)
					println(s"carol $c")
					Some()
				}

				println(s"future 3, tx2 $tx2")

			}

			store.close()
		} recover {
			case e  => e.printStackTrace(System.out)
		}

		Await.result(future1, Duration.Inf)
		Await.result(future2, Duration.Inf)
		Await.result(future3, Duration.Inf)

		{
			val store = stores(0)
			import store._

			startSession { session =>
				session.startTransaction(isolationLevels.snapshotIsolation) { tx =>
					val a = tx.read("alice", consistencyLevels.causal)
					val b = tx.read("bob", consistencyLevels.causal)
					val c = tx.read("carol", consistencyLevels.causal)

					println(s"alice = $a, bob = $b, carol = $c")
					Some ()
				}

			}
		}
	}




	def multiBug(): Unit = {

		val idOps = Stores.Simple.createSeqIds

		//Note: We a creating a test store. Test stores provide extra meta data when reading a value.
		val stores : Seq[SysnameVersionedStore[Integer, String, Integer, String, String, String, Option[Integer]]]  =  Seq(
			Stores.Simple.newStore[Integer](LocalClusterNode1, idOps = idOps, initialize = true),
			Stores.Simple.newStore[Integer](LocalClusterNode1, idOps = idOps),
			Stores.Simple.newStore[Integer](LocalClusterNode2, idOps = idOps)
		)

		implicit val executionContext : ExecutionContext = ExecutionContext.global

		//Sequential
		{
			val store = stores(0)
			import store._

			startSession { session =>
				//Commit a transaction
				session.startTransaction(isolationLevels.snapshotIsolation) { tx =>
					tx.update("alice", 1000, consistencyLevels.causal)
					Some()
				}
			}
		}

		//Parallel
		val future1 = Future {
			println("### future 1")
			val store = stores(1)
			import store._

			startSession { session =>
				//Commit a transaction
				val tx1 = session.startTransaction(isolationLevels.snapshotIsolation) { tx =>
					tx.read("alice", consistencyLevels.causal) match {
						case Some(a) =>
							Thread.sleep(500) //<-- Problem the database changed between read and write!!!
							tx.update("alice", a - 200, consistencyLevels.causal)
							tx.update("bob", 200, consistencyLevels.causal)
						case _ =>
					}
					Some ()
				}
				println(s"future 1, tx1 $tx1")
			}

			store.close()
		} recover {
			case e  => e.printStackTrace(System.out)
		}

		val future2 = Future {
			println("### future 2")
			val store = stores(2)
			import store._

			startSession { session =>
				//Commit a transaction
				val tx1 = session.startTransaction(isolationLevels.snapshotIsolation) { tx =>
					tx.read("alice", consistencyLevels.causal) match {
						case Some(a) =>
							tx.update("alice", a - 300, consistencyLevels.causal)
							tx.update("carol", 300, consistencyLevels.causal)
						case _ =>
					}
					Some()
				}
				println(s"future 2, tx1 $tx1")
			}

			store.close()
		} recover {
			case e  => e.printStackTrace(System.out)
		}

		Await.result(future1, Duration.Inf)
		Await.result(future2, Duration.Inf)

		{
			val store = stores(0)
			import store._

			startSession { session =>
				session.startTransaction(isolationLevels.snapshotIsolation) { tx =>
					val a = tx.read("alice", consistencyLevels.causal)
					val b = tx.read("bob", consistencyLevels.causal)
					val c = tx.read("carol", consistencyLevels.causal)

					println(s"alice = $a, bob = $b, carol = $c")
					Some ()
				}

			}

			store.close()
		}
	}

	def main(args : Array[String]): Unit = {
		multiBug()
	}
}
