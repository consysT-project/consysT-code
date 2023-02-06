package de.tuda.stg.consys.core.store.cassandra.backend.trigger

import java.rmi.{Remote, RemoteException}

trait RMIServerInterface extends Remote {
  @throws(classOf[RemoteException])
  def trigger(data: String): Unit
}
