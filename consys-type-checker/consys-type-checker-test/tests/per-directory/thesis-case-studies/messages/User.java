package demos.messages;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;
import java.io.Serializable;
import java.util.*;

/* A user of the messenger application */
public @Mixed class User {

	private final Ref<@Weak Inbox> inbox;
	private final String name;

	public User(Ref<@Weak Inbox> inbox, String name) {
		this.inbox = inbox;
		this.name = name;
	}

	@Transactional
	@WeakOp public void send(String msg) {
		inbox.ref().add(msg);
	}
}