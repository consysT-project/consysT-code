package de.tuda.stg.consys.checker.testfiles.legacy;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.legacy.JConsistencyLevels;
import de.tuda.stg.consys.japi.legacy.JRef;
import de.tuda.stg.consys.japi.legacy.JReplicaSystem;

/**
 * Created on 27.05.19.
 *
 * @author Mirko Köhler
 */
public class RemoteObjectWithImplicitFlow {

	JReplicaSystem replicaSystem;


	static class A {
		int f;
		A(int f) { this.f = f; }
	}


	void testErrors() {
		JRef<@Strong A> x = replicaSystem.<@Strong A>replicate(new A(42), JConsistencyLevels.STRONG);
		JRef<@Weak A> y = replicaSystem.<@Weak A>replicate(new A(34), JConsistencyLevels.WEAK);

		if (y.ref().f == 31) {
			//TODO: Does this error need to be here? error: (invocation.receiver.implicitflow)
			// :: error: (assignment.type.implicitflow)
			x.ref().f = 40;
		}
	}

}
