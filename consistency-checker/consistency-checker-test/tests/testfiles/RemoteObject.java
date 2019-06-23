import de.tuda.stg.consys.checker.Inferred;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.objects.japi.JConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;

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


	void m() {
		JRef<@Strong A> x = replicaSystem.<@Strong A>replicate(new A(42), JConsistencyLevel.STRONG);
		JRef<@Weak A> y = replicaSystem.<@Weak A>replicate(new A(34), JConsistencyLevel.WEAK);

		// :: error: (assignment.type.incompatible)
		x = y;

		// :: error: (assignment.type.incompatible)
		x.ref().f = y.ref().f;
	}
}
