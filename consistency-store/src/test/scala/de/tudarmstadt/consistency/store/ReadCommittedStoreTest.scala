package de.tudarmstadt.consistency.store

import de.tudarmstadt.consistency.store.isolationTests.{DirtyReadTests, DirtyWriteTests, FuzzyReadTests, LostUpdateTests}

import scala.language.postfixOps

/**
	* Created on 13.09.18.
	*
	* @author Mirko Köhler
	*/
class ReadCommittedStoreTest extends SimpleStoreTest.Multi[Int]
	with DirtyReadTests
	with DirtyWriteTests {

	override def isolationValue : Isolation =
		stores(0).IsolationLevels.RC

}
