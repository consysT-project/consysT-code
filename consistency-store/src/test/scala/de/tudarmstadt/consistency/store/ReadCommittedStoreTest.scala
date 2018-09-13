package de.tudarmstadt.consistency.store

import de.tudarmstadt.consistency.store.ConnectionParams.LocalCluster
import de.tudarmstadt.consistency.store.isolationTests.{DirtyReadTests, DirtyWriteTests}
import de.tudarmstadt.consistency.store.shim.Event.Update
import de.tudarmstadt.consistency.store.shim.SysnameVersionedStore
import org.junit.{Before, Test}
import org.junit.Assert._

import scala.concurrent.Await
import scala.language.postfixOps

/**
	* Created on 13.09.18.
	*
	* @author Mirko Köhler
	*/
class ReadCommittedStoreTest extends SimpleStoreTest.Multi[Int] with DirtyReadTests with DirtyWriteTests {

	override def isolationValue : Isolation =
		stores(0).isolationLevels.readCommitted



}
