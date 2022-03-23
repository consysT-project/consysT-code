package demos.messages;


import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;
import java.io.Serializable;
import java.util.*;

/* A group chat of users */
public @Mixed class Group {

	private List<Ref<User>> users = Lists.newLinkedList();
	private int capacity = 100;

	@Transactional
	@WeakOp public void addPost(String msg) {
		for (Ref<User> user : users) {
			user.ref().send(msg);
		}
	}

	@StrongOp public void addUser(Ref<User> user) {
		if (users.size() < capacity)
			users.add(user);
	}

	@WeakOp public void changeCapacity(int capacity) {
		this.capacity = capacity;
	}


}