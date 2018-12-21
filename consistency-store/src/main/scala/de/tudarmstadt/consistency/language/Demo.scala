package de.tudarmstadt.consistency.language

import java.nio.ByteBuffer

import de.tudarmstadt.consistency.language.CassandraIntegration.Strong
import de.tudarmstadt.consistency.store.cassandra.ConnectionParams.LocalCluster

/**
	* Created on 20.12.18.
	*
	* @author Mirko Köhler
	*/
object Demo {

	def main(args: Array[String]): Unit = {
		val ci = new CassandraIntegration(LocalCluster)
		import ci._

		session {language =>
			import language._

			val x = Ref[ByteBuffer, Strong]("x")

			x.update(ByteBuffer.wrap(Array(1, 2, 3)))
			println(x.deref)
			x.update(ByteBuffer.wrap(Array(2, 3, 4)))

			isolate {
				val four : Byte = 4
				x.update(x.deref.get.put(four))
			}
		}




		sys.exit()
	}


}
