package de.tuda.stg.consys.experimental.lang.store.cassandra

import java.util
import java.util.List
import java.util.concurrent.{CountDownLatch, TimeUnit, TimeoutException}

import de.tuda.stg.consys.core.Address
import de.tuda.stg.consys.experimental.lang.store.Store
import org.apache.zookeeper.Watcher.Event.KeeperState
import org.apache.zookeeper.data.ACL
import org.apache.zookeeper.{CreateMode, KeeperException, WatchedEvent, Watcher, ZooDefs, ZooKeeper}
import org.apache.zookeeper.recipes.lock.{LockListener, WriteLock}

import scala.util.control.Breaks

/**
 * Created on 08.01.20.
 *
 * @author Mirko Köhler
 */
trait ZookeeperStoreExt extends Store { self : CassandraStore =>

	def zookeeperServer : Address

	val zoo : ZooKeeper = {
		val connectedSignal = new CountDownLatch(1)

		val zk = new ZooKeeper(zookeeperServer.toString, timeout.toMillis.toInt, new Watcher {
			override def process(event : WatchedEvent) : Unit = {
				if (event.getState == KeeperState.SyncConnected) {
					connectedSignal.countDown()
				}
			}
		})

		if (!connectedSignal.await(timeout.toMillis, TimeUnit.MILLISECONDS))
			throw new TimeoutException("could not connect to Zookeeper service")

		zk
	}

	//Initialize locks.
	createZnodeIfNotExists("/consys")
	createZnodeIfNotExists("/consys/locks")

	private def createZnodeIfNotExists(
    path : String,
    data : Array[Byte] = Array.emptyByteArray,
    acl : util.List[ACL] = ZooDefs.Ids.OPEN_ACL_UNSAFE,
    mode : CreateMode = CreateMode.PERSISTENT
  ) : Unit = {
		try {
			zoo.create(path, data, acl, mode)
		} catch {
			case e : KeeperException if e.code() == KeeperException.Code.NODEEXISTS =>
				//Don't do anything when the node already exists
		}
	}

	def lock(addr : Addr) : Unit = {
		val path = s"/consys/locks/$addr"
		createZnodeIfNotExists(path)

		println(s"$name tries to lock $addr")

		val lockedSignal = new CountDownLatch(1)

		val writeLock = new WriteLock(zoo, path, null)
		writeLock.setRetryDelay(100)
		writeLock.setLockListener(new LockListener {
			override def lockAcquired() : Unit = {
				println(name + " acquired")
				if (writeLock.isOwner) lockedSignal.countDown()
			}
			override def lockReleased() : Unit = {
				println(name + " released")
			}
		})

		val startTime = System.nanoTime()
		var locked = false

		val breaks = new Breaks
		import breaks._
		breakable {
			while (System.nanoTime() <= startTime + timeout.toNanos) {
				if (writeLock.isOwner) break
				else if (writeLock.lock()) break
				Thread.sleep((math.random() * zoo.getSessionTimeout).toInt)
			}
		}


		if (!writeLock.isOwner) {
			writeLock.unlock()
			throw new TimeoutException(s"timeout during acquiring the lock for $addr")
		}
		println(s"locked $addr")
	}

	def unlock(addr : Addr) : Unit = {
		val path = s"/consys/locks/$addr"
		val writeLock = new WriteLock(zoo, path, null)
		writeLock.unlock()
		println(s"unlocked $addr")
	}

	override def close() : Unit = {
		zoo.close()
	}

}
