package de.tuda.stg.consys.japi;

import de.tuda.stg.consys.core.store.legacy.Replicated;
import de.tuda.stg.consys.core.store.legacy.akka.AkkaReplicaSystem;
import de.tuda.stg.consys.japi.impl.akka.JAkkaReplicaSystem;

import java.io.Serializable;
import java.lang.reflect.Field;
import java.util.Optional;

/**
 * Created on 26.07.19.
 *
 * @author Mirko Köhler
 */
public interface JReplicated extends Replicated, Serializable {
	//Instances of this interface have to define the following field:
	//public transient AkkaReplicaSystem<String> replicaSystem = null;


	default Optional<JReplicaSystem> getSystem() {

		Field field = null;
		try {
			field = this.getClass().getField("replicaSystem");
			field.setAccessible(true);

			AkkaReplicaSystem replicaSystem = (AkkaReplicaSystem) field.get(this);

			if (replicaSystem != null)
				return Optional.of(new JAkkaReplicaSystem(replicaSystem));


		} catch (NoSuchFieldException e) {
			e.printStackTrace();
		} catch (IllegalAccessException e) {
			e.printStackTrace();
		}

		return Optional.empty();
	}

}
