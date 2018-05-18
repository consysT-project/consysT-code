import de.tu_darmstadt.consistency_types.cassandra.CollectionWrapper;
import de.tu_darmstadt.consistency_types.cassandra.ConsistencyObject;
import de.tu_darmstadt.consistency_types.cassandra.IntermediateWrapper;
import org.junit.Test;

import java.util.HashSet;

public class CycleTest {

    @Test
    public void testCyclicDependency() {
        A first = new A();
        A second = new A(first);
        first.read();
        second.read();
        assert true;
    }

    @Test
    public void testCyclicCollection() {
        B o1 = new B();
        B o2 = new B();
        o1.collectionWrapper.add(o2);
        o2.collectionWrapper.add(o1);
        o1.read();
        o2.read();
        assert true;
    }

    class A extends ConsistencyObject {
        IntermediateWrapper other;

        A(A otherA) {
            this.other = new IntermediateWrapper<>(otherA);
            otherA.other = this.getWrapper();
        }

        A() {
            super();
        }
    }

    class B extends ConsistencyObject {
        CollectionWrapper collectionWrapper;

        B() {
            this.collectionWrapper = new CollectionWrapper(new HashSet<B>());
        }
    }
}
