package cassandra;

import java.util.HashSet;
import java.util.Set;

public class Scope {

    private Set<AbstractConsistencyWrapper> processed = new HashSet<>();

    public void write(AbstractConsistencyWrapper wrapper) {
        if (processed.add(wrapper)) {
            wrapper.write(this);
        }
    }

    public void read(AbstractConsistencyWrapper wrapper) {
        if (processed.add(wrapper)) {
            wrapper.read(this);
        }
    }
}
