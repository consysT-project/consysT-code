package compiler;

import de.tuda.stg.consys.objects.japi.JConsistencyLevels;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;
import de.tuda.stg.consys.objects.japi.JReplicaSystems;

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

		JReplicaSystem replicaSystem1 = JReplicaSystems.fromActorSystem(2552);
		JReplicaSystem replicaSystem2 = JReplicaSystems.fromActorSystem(2553);

		try {
			replicaSystem1.addReplicaSystem("127.0.0.1", 2553);
			replicaSystem2.addReplicaSystem("127.0.0.1", 2552);

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
