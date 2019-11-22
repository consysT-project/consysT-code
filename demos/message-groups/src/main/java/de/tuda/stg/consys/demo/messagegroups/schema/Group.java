package de.tuda.stg.consys.demo.messagegroups.schema;

import de.tuda.stg.consys.objects.japi.JRef;

import java.io.Serializable;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.Objects;

/**
 * Created on 04.04.19.
 *
 * @author Mirko Köhler
 */
public class Group implements Serializable {

	public final JRef<User>[] users = new JRef[100];

	//Message delivery
	public void addPost(String msg) {
		List<Integer> l = null;

		for (JRef<User> user : (Iterable) () -> l.iterator()) {
			if (user != null) user.ref().send(msg);
		}
	}

	//Join group
	public void addUser(JRef<User> user) {
		for (int i = 0; i < users.length; i++) {
			if (users[i] == null) {
				users[i] = user;
				return;
			}
		}
		throw new IllegalArgumentException("no space for users");
	}

	public JRef<User> getUser(int index) {
		JRef<User> user = users[index];
		Objects.requireNonNull(user, "no user at index "+ index);

		return user;
	}
}
