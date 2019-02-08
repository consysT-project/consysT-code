package de.tuda.multijvm

import com.typesafe.config.{Config, ConfigFactory}

/**
	* Created on 06.02.19.
	*
	* @author Mirko Köhler
	*/
package object test {

	private[test] val config : Config = ConfigFactory.parseString(
		"""
			|akka {
			|  actor {
			|    provider = "cluster"
			|  }
			|  remote {
			|    log-remote-lifecycle-events = off
			|    netty.tcp {
			|      hostname = "127.0.0.1"
			|      port = 0
			|    }
			|  }
			|
			|  cluster {
			|    seed-nodes = [
			|      "akka.tcp://ClusterSystem@127.0.0.1:2551",
			|      "akka.tcp://ClusterSystem@127.0.0.1:2552"]
			|
			|    # auto downing is NOT safe for production deployments.
			|    # you may want to use it during development, read more about it in the docs.
			|    #
			|    # auto-down-unreachable-after = 10s
			|  }
			|}
		""".stripMargin)
	config.resolve()

}
