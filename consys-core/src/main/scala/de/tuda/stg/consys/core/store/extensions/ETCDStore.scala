package de.tuda.stg.consys.core.store.extensions

import de.tuda.stg.consys.core.store.Store
import io.etcd.jetcd.Client
import io.etcd.jetcd.lease.LeaseKeepAliveResponse
import io.grpc.stub.StreamObserver

import java.util.concurrent.TimeUnit
import scala.concurrent.duration.FiniteDuration

trait ETCDStore extends Store {
	protected[store] def etcdClient : Client
	protected[store] def etcdLease : Long
}

object ETCDStore {
	def createClientAndLease(host : String, port : Int, timeout : FiniteDuration) : (Client, Long) = {
		val client = Client.builder().endpoints(s"http://$host:$port").build()
		val lease = client.getLeaseClient.grant(timeout.toSeconds).get(timeout.toMillis, TimeUnit.MILLISECONDS).getID
		client.getLeaseClient.keepAlive(lease, noopStreamObserver)
		client -> lease
	}

	private object noopStreamObserver extends StreamObserver[LeaseKeepAliveResponse] {
		def onNext(response: LeaseKeepAliveResponse) = { }
		def onError(throwable: Throwable) = { }
		def onCompleted() = { }
	}
}
