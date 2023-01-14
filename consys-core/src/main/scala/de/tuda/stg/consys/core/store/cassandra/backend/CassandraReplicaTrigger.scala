package de.tuda.stg.consys.core.store.cassandra.backend

import java.rmi.registry.LocateRegistry

object CassandraReplicaTrigger extends App {
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

}
