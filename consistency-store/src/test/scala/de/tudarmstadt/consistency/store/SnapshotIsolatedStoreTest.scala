package de.tudarmstadt.consistency.store

import de.tudarmstadt.consistency.store.isolationTests.{DirtyReadTests, DirtyWriteTests}
import org.junit.Assert._
import org.junit.Test

import scala.language.postfixOps

/**
	* Created on 13.09.18.
	*
	* @author Mirko Köhler
	*/
class SnapshotIsolatedStoreTest extends SimpleStoreTest.Multi[Int] with DirtyReadTests with DirtyWriteTests {

	override def isolationValue : Isolation =
		stores(0).isolationLevels.snapshotIsolation
}
