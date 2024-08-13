package de.tuda.stg.consys.japi.binding.akkacluster;

import de.tuda.stg.consys.core.store.CoordinationMechanism;
import de.tuda.stg.consys.core.store.akka.AkkaStore;
import de.tuda.stg.consys.core.store.akkacluster.AkkaClusterStore;
import de.tuda.stg.consys.core.store.utils.SinglePortAddress;
import scala.collection.JavaConverters$;
import scala.concurrent.duration.Duration;
import scala.concurrent.duration.FiniteDuration;
import scala.jdk.javaapi.CollectionConverters;

import java.util.Arrays;
import java.util.concurrent.TimeUnit;

/**
 * Created on 27.01.20.
 *
 * @author Mirko Köhler
 */
public class AkkaClusterReplica {

	public static AkkaClusterStoreBinding create(String host, int akkaPort, CoordinationMechanism coordinationMechanism, FiniteDuration timeout, Iterable<SinglePortAddress> nodes) {
		AkkaClusterStore store = AkkaClusterStore.fromAddress(host, akkaPort, coordinationMechanism, CollectionConverters.asScala(nodes), "consys-akka-cluster", timeout);
		return create(store);
	}

	public static AkkaClusterStoreBinding create(String host, int akkaPort, CoordinationMechanism coordinationMechanism, Iterable<SinglePortAddress> nodes) {
		return create(host, akkaPort, coordinationMechanism, Duration.apply(30, TimeUnit.SECONDS), nodes);
	}

	public static AkkaClusterStoreBinding create(AkkaClusterStore store) {
		return new AkkaClusterStoreBinding(store);
	}

}






