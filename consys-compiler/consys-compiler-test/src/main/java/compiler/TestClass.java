package compiler;

import de.tuda.stg.consys.objects.japi.Demo;
import de.tuda.stg.consys.objects.japi.JConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;

/**
 * Created on 30.09.19.
 *
 * @author Mirko Köhler
 */
public class TestClass {

	public static void main(String[] args) throws Exception {

		JReplicaSystem replicaSystem1 = JReplicaSystem.fromActorSystem(2552);
		JReplicaSystem replicaSystem2 = JReplicaSystem.fromActorSystem(2553);

		System.out.println("system1 = " + replicaSystem1);
		System.out.println("system2 = " + replicaSystem2);

		try {
			replicaSystem1.addReplicaSystem("127.0.0.1", 2553);
			replicaSystem2.addReplicaSystem("127.0.0.1", 2552);

			JRef<String> ref1Strong = replicaSystem1.replicate("os", "Hello World!", JConsistencyLevel.STRONG);
			JRef<String> ref2Strong = replicaSystem2.ref("os", String.class, JConsistencyLevel.STRONG);

			char c = ref1Strong.invoke("charAt", 3);//ref().charAt(3);
			System.out.println(c);

		} finally {
			replicaSystem1.close();
			replicaSystem2.close();
		}

	}

}
