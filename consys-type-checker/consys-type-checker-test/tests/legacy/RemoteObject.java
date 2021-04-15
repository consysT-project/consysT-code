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
public class RemoteObject {

	JReplicaSystem replicaSystem;


	static class A {
		int f;
		A(int f) { this.f = f; }
	}


	void testExpected() {
		JRef<@Strong A> x1 = replicaSystem.<@Strong A>replicate(new A(42), JConsistencyLevels.STRONG);
		JRef<@Weak A> y1 = replicaSystem.<@Weak A>replicate(new A(34), JConsistencyLevels.WEAK);

		JRef<@Strong A> x2 = replicaSystem.<@Strong A>replicate(new A(2), JConsistencyLevels.STRONG);
		JRef<@Weak A> y2 = replicaSystem.<@Weak A>replicate(new A(1), JConsistencyLevels.WEAK);

		//Assign the same consistency levels
		x1.ref().f = x2.ref().f;
		y1.ref().f = y2.ref().f;

		//Assign accross consistency levels
		y1.ref().f = x1.ref().f;

		//Assign references
		x1 = x2;
		y2 = y1;
		//y1 = x1; //TODO: This seems to be quite "unwanted". A ref should always have the correct declared type.

	}

	void testErrors() {
		JRef<@Strong A> x1 = replicaSystem.<@Strong A>replicate(new A(42), JConsistencyLevels.STRONG);
		JRef<@Weak A> y1 = replicaSystem.<@Weak A>replicate(new A(34), JConsistencyLevels.WEAK);


		// :: error: (assignment.type.incompatible)
		x1 = y1;

		// :: error: (assignment.type.incompatible)
		x1.ref().f = y1.ref().f;
	}
}
