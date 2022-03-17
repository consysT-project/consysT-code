package messages


import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;
import java.io.Serializable;
import java.util.*;

/* A group chat of users */
public class Group {

	private final List<Ref<User>> users = LinkedList.empty;

	@Transactional
	@WeakOp public void addPost(String msg) {
		for (Ref<User> user : users) {
			user.ref().send(msg);
		}
	}

	@StrongOp public void addUser(Ref<User> user) {
		users.add(user);
	}
}