package de.tuda.stg.consys.experimental.lang.store.cassandra

import java.util.concurrent.{CountDownLatch, TimeUnit}

import org.apache.curator.framework.{CuratorFramework, CuratorFrameworkFactory}
import org.apache.curator.retry.ExponentialBackoffRetry
import org.apache.zookeeper.Watcher.Event.KeeperState
import org.apache.zookeeper.recipes.lock.{LockListener, WriteLock}
import org.apache.zookeeper.{CreateMode, KeeperException, WatchedEvent, Watcher, ZooDefs, ZooKeeper}
import org.apache.curator.framework.recipes.locks.InterProcessMutex


import scala.concurrent.duration.Duration

/**
 * Created on 07.01.20.
 *
 * @author Mirko Köhler
 */
object ZookeeperDemo {

	val store1 = CassandraStore.fromAddress("127.0.0.1", 9042, 2181, withTimeout = Duration(60, "s"), withInitialize = true)
	val store2 = CassandraStore.fromAddress("127.0.0.2", 9042, 2182, withTimeout = Duration(60, "s"), withInitialize = false)
	val store3 = CassandraStore.fromAddress("127.0.0.3", 9042, 2183, withTimeout = Duration(60, "s"), withInitialize = false)





	def main(args : Array[String]) : Unit = {



		val retryPolicy = new ExponentialBackoffRetry(1000, 3)
		val client = CuratorFrameworkFactory.newClient("127.0.0.1:2181", retryPolicy)
		client.start()
		println("started")
		println(client.getState)
		println("connected")
		client.create().forPath("/consys/mylocks")
		println("created")



		val latch1 = new CountDownLatch(1)
		val latch2 = new CountDownLatch(1)
		val latch3 = new CountDownLatch(1)


//		new Thread(new Runnable {
//			override def run() : Unit = {
//				try {
//
//
//					println("1 start")
//					val client1 = CuratorFrameworkFactory.newClient("127.0.0.1:2181", retryPolicy)
//					client1.start()
//					client1.create().forPath("/consys/locks")
//					println("1 started")
//					val lock = new InterProcessMutex(client1, "/consys/locks")
//					println("1 try acquire")
//					lock.acquire()
//					println("1 acquired")
//					Thread.sleep(1000)
//					latch1.countDown()
//					Thread.sleep(5000)
//					lock.release()
//					println("1 released")
//					Thread.sleep(1000)
//					latch3.countDown()
//					client1.close()
//				} catch {
//					case x => x.printStackTrace()
//				}
//			}
//		}).start()
//
//
//		new Thread(new Runnable {
//			override def run() : Unit = {
//				println("2 start")
//				val client2 = CuratorFrameworkFactory.newClient("127.0.0.2:2182", retryPolicy)
//				client2.start()
//				println("2 started")
//				val lock = new InterProcessMutex(client2, "/consys/locks")
//
//				latch1.await()
//				println("2 try acquire")
//				lock.acquire()
//				println("2 acquired")
//				latch3.await()
//			}
//		}).start()

		Thread.sleep(100000)

	}


}
