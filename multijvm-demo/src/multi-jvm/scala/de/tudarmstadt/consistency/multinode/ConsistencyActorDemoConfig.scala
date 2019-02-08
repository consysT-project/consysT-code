package de.tudarmstadt.consistency.multinode

import akka.remote.testconductor.RoleName
import akka.remote.testkit.MultiNodeConfig

/**
	* Created on 08.02.19.
	*
	* @author Mirko Köhler
	*/
object ConsistencyActorDemoConfig extends MultiNodeConfig {
  val node1 : RoleName = role("node1")
  val node2 : RoleName = role("node2")
}
