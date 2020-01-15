package de.tuda.stg.consys.japi.impl;

import com.typesafe.config.Config;
import de.tuda.stg.consys.core.Address;
import de.tuda.stg.consys.core.akka.AkkaReplicaSystem;
import de.tuda.stg.consys.core.akka.AkkaReplicaSystemFactory;
import de.tuda.stg.consys.japi.impl.akka.JAkkaReplicaSystem;
import scala.collection.JavaConverters;
import scala.collection.Seq;

import java.time.Duration;

/**
 * Created on 01.03.19.
 *
 * @author Mirko Köhler
 */
public class JReplicaSystems {


	public static JAkkaReplicaSystem fromActorSystem(Address hostname, Iterable<Address> others, Duration timeout) {
		return new JAkkaReplicaSystem(AkkaReplicaSystemFactory.create(
			hostname,
			JavaConverters.iterableAsScalaIterable(others).toSeq(),
			scala.concurrent.duration.Duration.fromNanos(timeout.toNanos())
		));
	}

	public static JAkkaReplicaSystem fromActorSystem(Address hostname, Iterable<Address> others) {
		return new JAkkaReplicaSystem(AkkaReplicaSystemFactory.create(
			hostname,
			JavaConverters.iterableAsScalaIterable(others).toSeq(),
			scala.concurrent.duration.Duration.apply("60s")
		));
	}

	public static JAkkaReplicaSystem fromActorSystem(Config config) {
		return new JAkkaReplicaSystem((AkkaReplicaSystem) AkkaReplicaSystemFactory.create(config));
	}

	public static JAkkaReplicaSystem fromActorSystem(String configPath) {
		return new JAkkaReplicaSystem((AkkaReplicaSystem) AkkaReplicaSystemFactory.create(configPath));
	}

	public static JAkkaReplicaSystem[] fromActorSystemForTesting(Iterable<Address> hosts) {
		Seq<AkkaReplicaSystem> scalaSeq = AkkaReplicaSystemFactory.createForTesting(JavaConverters.iterableAsScalaIterable(hosts).toSeq());

		return JavaConverters.asJavaCollection(scalaSeq).stream()
			.map(system -> new JAkkaReplicaSystem(system))
			.toArray(JAkkaReplicaSystem[]::new);
	}

	public static JAkkaReplicaSystem[] fromActorSystemForTesting(int numOfReplicas) {
		Seq<AkkaReplicaSystem> scalaSeq = AkkaReplicaSystemFactory.createForTesting(numOfReplicas);

		return JavaConverters.asJavaCollection(scalaSeq).stream()
			.map(system -> new JAkkaReplicaSystem(system))
			.toArray(JAkkaReplicaSystem[]::new);
	}

}

