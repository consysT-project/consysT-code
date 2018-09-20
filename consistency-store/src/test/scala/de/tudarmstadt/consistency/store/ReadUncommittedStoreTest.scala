package de.tudarmstadt.consistency.store

import de.tudarmstadt.consistency.store.isolationTests.{DirtyReadTests, DirtyWriteTests}

import scala.language.postfixOps

/**
	* Created on 13.09.18.
	*
	* @author Mirko Köhler
	*/
class ReadUncommittedStoreTest extends SimpleStoreTest.Multi[Int] with DirtyWriteTests {

	override def isolationValue : Isolation =
		stores(0).IsolationLevels.RU



}
