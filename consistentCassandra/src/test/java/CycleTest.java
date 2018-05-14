import com.github.allprojects.consistencyTypes.cassandraInterface.IntermediateWrapper;
import com.github.allprojects.consistencyTypes.cassandraInterface.Wrappable;
import org.junit.Test;

public class CycleTest {

    @Test
    public void testCyclicDependency() {
        A first = new A();
        A second = new A(first);
        first.write();
        second.write();
        assert true;
    }

    class A extends Wrappable {
        IntermediateWrapper other;

        A(A otherA) {
            this.other = new IntermediateWrapper<>(otherA);
            otherA.other = this.getWrapper();
        }

        A() {
            super();
        }
    }

}
