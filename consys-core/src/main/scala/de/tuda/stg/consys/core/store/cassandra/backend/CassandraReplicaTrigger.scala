package de.tuda.stg.consys.core.store.cassandra.backend

import org.apache.cassandra.db.{Clustering, Mutation}
import org.apache.cassandra.db.partitions.Partition
import org.apache.cassandra.db.rows.{Unfiltered, UnfilteredRowIterator}
import org.apache.cassandra.triggers.ITrigger

import java.rmi.{Remote, RemoteException}
import java.rmi.registry.LocateRegistry
import java.util
import java.util.Collections

/*
class CassandraReplicaTrigger extends ITrigger {
  override def augment(partition: Partition): util.Collection[Mutation] = {
    try {
      val clientURL = s"rmi://127.0.0.1:1234/test"
      val port = 1234
      val registry = LocateRegistry.getRegistry(port)
      val server = registry.lookup(clientURL).asInstanceOf[RMIServerInterface]

      var test: String = ""

      val it: UnfilteredRowIterator = partition.unfilteredIterator

      while (it.hasNext) {
        val item: Unfiltered = it.next

        if (item.isRow) {
          val clustering = item.clustering.asInstanceOf[Clustering]
          test = clustering.toCQLString(partition.metadata)
        }
      }

      server.print(test);
    } catch {
      case e: Exception =>
        System.err.println("Client exception: " + e.toString)
        e.printStackTrace()
    }
    Collections.emptyList[Mutation]()
  }
}


 */


