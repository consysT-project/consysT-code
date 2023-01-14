package de.tuda.stg.consys.core.store.cassandra.backend

import org.apache.cassandra.db.Mutation
import org.apache.cassandra.db.partitions.Partition
import org.apache.cassandra.triggers.ITrigger

import java.rmi.{Remote, RemoteException}
import java.rmi.registry.LocateRegistry
import java.util
import java.util.Collections

class CassandraReplicaTrigger extends ITrigger {
  override def augment(partition: Partition): util.Collection[Mutation] = {
    try {
      val clientURL = s"rmi://127.0.0.1:1234/test"
      val port = 1234
      val registry = LocateRegistry.getRegistry(port)
      val server = registry.lookup(clientURL).asInstanceOf[RMIServerInterface]
      server.print();
    } catch {
      case e: Exception =>
        System.err.println("Client exception: " + e.toString)
        e.printStackTrace()
    }
    Collections.emptyList
  }
}

/**
 * Remote trait which acts as an interface to the server
 */
trait RMIServerInterface extends Remote {
  @throws(classOf[RemoteException])
  def print(): Unit
}


