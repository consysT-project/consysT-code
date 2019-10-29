package de.tuda.stg.consys.objects.japi;

import akka.actor.ActorSystem;
import de.tuda.stg.consys.objects.actors.AkkaReplicaSystem;
import de.tuda.stg.consys.objects.actors.package$;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;

import java.time.Duration;

/**
 * Created on 01.03.19.
 *
 * @author Mirko Köhler
 */
public class JReplicaSystems {

	public static JReplicaSystem fromActorSystem(ActorSystem actorSystem) {
		return new JReplicaSystemAkkaImpl(package$.MODULE$.createReplicaSystem(actorSystem));
	}

	public static JReplicaSystem fromActorSystem(int port) {
		return new JReplicaSystemAkkaImpl(package$.MODULE$.createReplicaSystem(port));
	}

	public static JReplicaSystem fromActorSystem(String hostname, int port) {
		return new JReplicaSystemAkkaImpl(package$.MODULE$.createReplicaSystem(hostname, port));
	}

	public static JReplicaSystem fromActorSystem(ActorSystem actorSystem, Duration timeout) {
		return new JReplicaSystemAkkaImpl(package$.MODULE$.createReplicaSystem(actorSystem, scala.concurrent.duration.Duration.fromNanos(timeout.toNanos())));
	}

	public static JReplicaSystem fromActorSystem(int port, Duration timeout) {
		return new JReplicaSystemAkkaImpl(package$.MODULE$.createReplicaSystem(port, scala.concurrent.duration.Duration.fromNanos(timeout.toNanos())));
	}

	public static JReplicaSystem fromActorSystem(String hostname, int port, Duration timeout) {
		return new JReplicaSystemAkkaImpl(package$.MODULE$.createReplicaSystem(hostname, port, scala.concurrent.duration.Duration.fromNanos(timeout.toNanos())));
	}

}

