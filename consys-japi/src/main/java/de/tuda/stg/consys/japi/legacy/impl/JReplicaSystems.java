package de.tuda.stg.consys.japi.legacy.impl;

import com.typesafe.config.Config;
import de.tuda.stg.consys.core.legacy.akka.AkkaReplicaSystem;
import de.tuda.stg.consys.core.legacy.akka.AkkaReplicaSystemFactory;
import de.tuda.stg.consys.core.legacy.akka.AkkaReplicaSystems;
import de.tuda.stg.consys.core.store.utils.Address;
import de.tuda.stg.consys.japi.legacy.impl.akka.JAkkaReplicaSystem;
import scala.collection.JavaConverters;
import scala.collection.Seq;

import java.time.Duration;
import java.util.function.Supplier;

/**
 * Created on 01.03.19.
 *
 * @author Mirko Köhler
 */
public class JReplicaSystems {

	public static interface ReplicaSystemInterface {
		public <T> T use(Supplier<T> f);
	}

	public static class AkkaReplicaSystemInterface implements ReplicaSystemInterface {
		private final AkkaReplicaSystemFactory.AkkaReplicaSystemBinding system;

		AkkaReplicaSystemInterface(AkkaReplicaSystemFactory.AkkaReplicaSystemBinding system) {
			this.system = system;
		}

		public <T> T use(Supplier<T> f) {
			T result = AkkaReplicaSystems.withValue(system, f::get);
			system.close();
			return result;
		}
	}

	public static JAkkaReplicaSystem getSystem() {
		AkkaReplicaSystem system = AkkaReplicaSystems.system();
		if (system == null) {
			throw new IllegalStateException("replica system has been retrieved but not been initialized.");
		}
		return new JAkkaReplicaSystem(system);
	}

	public static AkkaReplicaSystemInterface withSystem(JAkkaReplicaSystem system) {
		return new AkkaReplicaSystemInterface((AkkaReplicaSystemFactory.AkkaReplicaSystemBinding) system.replicaSystem);
	}

	public static AkkaReplicaSystemInterface withActorSystem(Address hostname, Iterable<Address> others, Duration timeout) {
		return new AkkaReplicaSystemInterface(AkkaReplicaSystemFactory.create(
				hostname,
				JavaConverters.iterableAsScalaIterable(others).toSeq(),
				scala.concurrent.duration.Duration.fromNanos(timeout.toNanos())
		));
	}

	public static AkkaReplicaSystemInterface withActorSystem(Address hostname, Iterable<Address> others) {
		return new AkkaReplicaSystemInterface(AkkaReplicaSystemFactory.create(
				hostname,
				JavaConverters.iterableAsScalaIterable(others).toSeq(),
				scala.concurrent.duration.Duration.apply("60s")
		));
	}

	public static AkkaReplicaSystemInterface withActorSystem(Config config) {
		return new AkkaReplicaSystemInterface(
				/* TODO Fix unsafe cast */
				(AkkaReplicaSystemFactory.AkkaReplicaSystemBinding) AkkaReplicaSystemFactory.create(config)
		);
	}


	@Deprecated
	public static JAkkaReplicaSystem fromActorSystem(Address hostname, Iterable<Address> others, Duration timeout) {
		return new JAkkaReplicaSystem(AkkaReplicaSystemFactory.create(
			hostname,
			JavaConverters.iterableAsScalaIterable(others).toSeq(),
			scala.concurrent.duration.Duration.fromNanos(timeout.toNanos())
		));
	}

	@Deprecated
	public static JAkkaReplicaSystem fromActorSystem(Address hostname, Iterable<Address> others) {
		return new JAkkaReplicaSystem(AkkaReplicaSystemFactory.create(
			hostname,
			JavaConverters.iterableAsScalaIterable(others).toSeq(),
			scala.concurrent.duration.Duration.apply("60s")
		));
	}

	@Deprecated
	public static JAkkaReplicaSystem fromActorSystem(Config config) {
		return new JAkkaReplicaSystem((AkkaReplicaSystem) AkkaReplicaSystemFactory.create(config));
	}

	@Deprecated
	public static JAkkaReplicaSystem fromActorSystem(String configPath) {
		return new JAkkaReplicaSystem((AkkaReplicaSystem) AkkaReplicaSystemFactory.create(configPath));
	}

	@Deprecated
	public static JAkkaReplicaSystem[] fromActorSystemForTesting(Iterable<Address> hosts) {
		Seq<AkkaReplicaSystemFactory.AkkaReplicaSystemBinding> scalaSeq =
				AkkaReplicaSystemFactory.createForTesting(JavaConverters.iterableAsScalaIterable(hosts).toSeq());

		return JavaConverters.asJavaCollection(scalaSeq).stream()
			.map(system -> new JAkkaReplicaSystem(system))
			.toArray(JAkkaReplicaSystem[]::new);
	}

	@Deprecated
	public static JAkkaReplicaSystem[] fromActorSystemForTesting(int numOfReplicas) {
		Seq<AkkaReplicaSystemFactory.AkkaReplicaSystemBinding> scalaSeq =
				AkkaReplicaSystemFactory.createForTesting(numOfReplicas);

		return JavaConverters.asJavaCollection(scalaSeq).stream()
			.map(system -> new JAkkaReplicaSystem(system))
			.toArray(JAkkaReplicaSystem[]::new);
	}

}

