package de.tuda.stg.consys.japi;

import com.typesafe.config.Config;
import de.tuda.stg.consys.core.Address;
import de.tuda.stg.consys.core.actors.AkkaReplicaSystem;
import de.tuda.stg.consys.core.actors.AkkaReplicaSystemFactory;
import scala.collection.JavaConverters;
import scala.collection.Seq;

import java.time.Duration;

/**
 * Created on 01.03.19.
 *
 * @author Mirko Köhler
 */
public class JReplicaSystems {


	public static JReplicaSystem fromActorSystem(Address hostname, Iterable<Address> others, Duration timeout) {
		return new JReplicaSystemAkkaImpl(AkkaReplicaSystemFactory.create(
			hostname,
			JavaConverters.iterableAsScalaIterable(others).toSeq(),
			scala.concurrent.duration.Duration.fromNanos(timeout.toNanos())
		));
	}

	public static JReplicaSystem fromActorSystem(Address hostname, Iterable<Address> others) {
		return new JReplicaSystemAkkaImpl(AkkaReplicaSystemFactory.create(
			hostname,
			JavaConverters.iterableAsScalaIterable(others).toSeq(),
			scala.concurrent.duration.Duration.apply("60s")
		));
	}

	public static JReplicaSystem fromActorSystem(Config config) {
		return new JReplicaSystemAkkaImpl((AkkaReplicaSystem) AkkaReplicaSystemFactory.create(config));
	}

	public static JReplicaSystem fromActorSystem(String configPath) {
		return new JReplicaSystemAkkaImpl((AkkaReplicaSystem) AkkaReplicaSystemFactory.create(configPath));
	}

	public static JReplicaSystem[] fromActorSystemForTesting(Iterable<Address> hosts) {
		Seq<AkkaReplicaSystem> scalaSeq = AkkaReplicaSystemFactory.createForTesting(JavaConverters.iterableAsScalaIterable(hosts).toSeq());

		return JavaConverters.asJavaCollection(scalaSeq).stream()
			.map(system -> new JReplicaSystemAkkaImpl(system))
			.toArray(JReplicaSystem[]::new);
	}

	public static JReplicaSystem[] fromActorSystemForTesting(int numOfReplicas) {
		Seq<AkkaReplicaSystem> scalaSeq = AkkaReplicaSystemFactory.createForTesting(numOfReplicas);

		return JavaConverters.asJavaCollection(scalaSeq).stream()
			.map(system -> new JReplicaSystemAkkaImpl(system))
			.toArray(JReplicaSystem[]::new);
	}

}

