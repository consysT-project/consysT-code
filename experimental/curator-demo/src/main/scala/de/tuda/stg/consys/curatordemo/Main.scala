package de.tuda.stg.consys.curatordemo

import org.apache.curator.framework.CuratorFrameworkFactory
import org.apache.curator.retry.RetryNTimes

/**
 * Created on 13.01.20.
 *
 * @author Mirko Köhler
 */
object Main {

	def main(args : Array[String]) : Unit = {
		val sleepMsBetweenRetries = 100
		val maxRetries = 3
		val retryPolicy = new RetryNTimes(maxRetries, sleepMsBetweenRetries)

		val client = CuratorFrameworkFactory.newClient("127.0.0.1:2181", retryPolicy)
		client.start()

		println(client.checkExists.forPath("/"))

		client.create().orSetData().forPath("/consys/test")
		println("created")
	}

}
