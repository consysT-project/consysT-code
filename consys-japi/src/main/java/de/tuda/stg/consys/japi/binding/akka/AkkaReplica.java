package de.tuda.stg.consys.japi.binding.akka;

import de.tuda.stg.consys.core.store.CoordinationMechanism;
import de.tuda.stg.consys.core.store.akka.AkkaStore;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import scala.concurrent.duration.Duration;
import scala.concurrent.duration.FiniteDuration;

import java.util.concurrent.TimeUnit;

/**
 * Created on 27.01.20.
 *
 * @author Mirko Köhler
 */
public class AkkaReplica {

	public static AkkaStoreBinding create(String host, int akkaPort, CoordinationMechanism coordinationMechanism, FiniteDuration timeout) {
		AkkaStore store = AkkaStore.fromAddress(host, akkaPort, coordinationMechanism, timeout);
		return new AkkaStoreBinding(store);
	}

	public static AkkaStoreBinding create(String host, int akkaPort, CoordinationMechanism coordinationMechanism) {
		AkkaStore store = AkkaStore.fromAddress(host, akkaPort, coordinationMechanism, Duration.apply(30, TimeUnit.SECONDS));
		return new AkkaStoreBinding(store);
	}

	public static AkkaStoreBinding create(AkkaStore store) {
		return new AkkaStoreBinding(store);
	}

}






