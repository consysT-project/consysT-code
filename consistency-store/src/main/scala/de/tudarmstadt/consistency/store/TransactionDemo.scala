package de.tudarmstadt.consistency.store

import de.tudarmstadt.consistency.store.ConnectionParams.LocalCluster
import de.tudarmstadt.consistency.utils.Log

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

		val store = Stores.Simple.newStore(LocalCluster, initialize = true)
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

//			Log.info(null, startTransaction(isolationLevelOps.snapshotIsolation){
//				transactionE
//			})
//			Log.info(null, startTransaction(isolationLevelOps.readCommitted){
//				transactionE
//			})
//
//			print()
		}

		System.exit(0)
	}

//	def concurrentExample(): Unit = {
//
//		import de.tudarmstadt.consistency.store.scala.transactions.SimpleCassandraTransactionStore._
//		initialize()
//
//		val executor = Executors.newFixedThreadPool(4)
//		implicit val executionContext: ExecutionContext = ExecutionContext.fromExecutor(executor)
//
//		Thread.sleep(1000)
//
//		Future {
//			val session = newSession
//			try {
//				Log.info(null, "### A ===> " + commitTransaction(session, List(Write("x", "Hallo", Set.empty), Write("y", "Welt", Set.empty))))
//			} catch {
//				case e => TransactionDemo.synchronized {
//					System.err.println("NODE A")
//					e.printStackTrace()
//				}
//			}
//			Log.info(null, "A done.")
//		}
//
//		Future {
//			val session = newSession
//			try {
//				Log.info(null, "### B ===> " + commitTransaction(session, List(Write("x", "Hello", Set.empty), Write("y", "World", Set.empty))))
//			} catch {
//				case e => TransactionDemo.synchronized {
//					System.err.println("NODE B")
//					e.printStackTrace()
//				}
//			}
//			Log.info(null, "B done.")
//		}
//
//		Future {
//			val session = newSession
//			try {
//				Log.info(null, "### C ===> " + commitTransaction(session, List(Write("x", "Hallösche", Set.empty), Write("z", "Zusamme", Set.empty))))
//			} catch {
//				case e => TransactionDemo.synchronized {
//					System.err.println("NODE C")
//					e.printStackTrace()
//				}
//			}
//			Log.info(null, "C done.")
//		}
//
//		Thread.sleep(3000)
//
//		val session = newSession
//
//		printTables(session)
//
//		Thread.sleep(1000)
//
//		timed {
//			Log.info(null, "x = " + read(session, "x"))
//		}
//		timed {
//			Log.info(null, "y = " + read(session, "y"))
//		}
//		timed {
//			Log.info(null, "z = " + read(session, "z"))
//		}
//		timed {
//			Log.info(null, "x = " + read(session, "x"))
//		}
//
//		Thread.sleep(1000)
//
//		printTables(session)
//
//		System.exit(0)
//
//	}

	def main(args : Array[String]): Unit = {
		simpleExample()
	}
}
