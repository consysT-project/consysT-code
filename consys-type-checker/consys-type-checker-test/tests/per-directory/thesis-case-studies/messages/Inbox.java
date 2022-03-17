package messages


import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;
import java.io.Serializable;
import java.util.*;

/* The message inbox of a user */
public class Inbox {
		private final Set<String> entries = new HashSet<>();

		public void add(String msg) {
				entries.add(msg);
		}
}



