package compiler;

import de.tuda.stg.consys.japi.JConsistencyLevels;
import de.tuda.stg.consys.japi.JRef;
import de.tuda.stg.consys.japi.JReplicaSystem;
import de.tuda.stg.consys.japi.JReplicaSystems;

import java.io.Serializable;
import java.util.Objects;

/**
 * Created on 30.09.19.
 *
 * @author Mirko Köhler
 */
public class TestClass {

	public static class Box implements Serializable {
		public int i;
		public Box(int i) {
			this.i = i;
		}
		public int incBy(int amount) {
			i += amount;
			return i;
		}
	}

	public static void main(String[] args) throws Exception {

		JReplicaSystem[] systems = JReplicaSystems.fromActorSystemForTesting(2);

		JReplicaSystem replicaSystem1 = systems[0];
		JReplicaSystem replicaSystem2 = systems[1];

		try {
			JRef<Box> ref1Strong = replicaSystem1.replicate("os", new Box(42), JConsistencyLevels.STRONG);
			JRef<Box> ref2Strong = replicaSystem2.lookup("os", Box.class, JConsistencyLevels.STRONG);

			ref1Strong.ref().incBy(23);
			System.out.println(Objects.toString(ref2Strong.ref().i));
			ref2Strong.ref().i = 777;
			System.out.println(Objects.toString(ref1Strong.ref().i));

			ref2Strong.ref().i = ref2Strong.ref().i;

		} finally {
			replicaSystem1.close();
			replicaSystem2.close();
		}

	}

}
