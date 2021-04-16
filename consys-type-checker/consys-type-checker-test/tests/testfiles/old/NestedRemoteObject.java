package de.tuda.stg.consys.checker.testfiles.testfiles;

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
public class NestedRemoteObject {

	JReplicaSystem replicaSystem;


	static class A {
		int f;
		A(int f) { this.f = f; }
	}

	static class B {
		JRef<@Weak A> a;
		B(JRef<@Weak A> a) { this.a = a; }

		void setA(JRef<@Weak A> a) { this.a = a; }

		int getF() { return a.ref().f; }
	}


	void testExpected() {
		JRef<@Strong A> aStrong = replicaSystem.<@Strong A>replicate(new A(42), JConsistencyLevels.STRONG);
		JRef<@Weak A> aWeak = replicaSystem.<@Weak A>replicate(new A(34), JConsistencyLevels.WEAK);

		JRef<@Strong B> bStrong = replicaSystem.replicate(new B(aWeak), JConsistencyLevels.STRONG);


//		bStrong.ref().setA(aStrong);




	}
}
