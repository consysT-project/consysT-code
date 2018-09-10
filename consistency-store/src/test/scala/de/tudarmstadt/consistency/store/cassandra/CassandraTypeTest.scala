package de.tudarmstadt.consistency.store.cassandra

import de.tudarmstadt.consistency.annotations.CassandraType
import org.junit.Test

import scala.reflect.runtime.universe._

/**
	* Created on 10.09.18.
	*
	* @author Mirko Köhler
	*/
class CassandraTypeTest {

	@Test
	def testAnnotatedType(): Unit = {

		@CassandraType(cassandraType = "timeuuid")
		type T =  Int

		println(cassandraTypeOf[T](typeTag[Int]))
	}

}
