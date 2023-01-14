package de.tuda.stg.consys.demo.webshop.extras

import de.tuda.stg.consys.core.store.cassandra.backend.RMIServerInterface

import java.rmi.registry.LocateRegistry

object RMIClient extends App {

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