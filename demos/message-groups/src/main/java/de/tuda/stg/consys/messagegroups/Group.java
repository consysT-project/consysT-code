package de.tuda.stg.consys.messagegroups;

import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.objects.japi.JRef;

import java.io.Serializable;
import java.util.Objects;

/**
 * Created on 04.04.19.
 *
 * @author Mirko Köhler
 */
public class Group implements Serializable {

	public final JRef<@Weak User>[] users = new JRef[100];

	//Message delivery
	void addPost(String msg) {
		for (JRef<User> user : users) {
			if (user != null) user.ref().send(msg);
		}
	}

	//Join group
	void addUser(JRef<User> user) {
		for (int i = 0; i < users.length; i++) {
			if (users[i] == null) {
				users[i] = user;
				return;
			}
		}
		throw new IllegalArgumentException("no space for users");
	}

	JRef<User> getUser(int index) {
		JRef<User> user = users[index];
		Objects.requireNonNull(user, "no user at index "+ index);

		return user;
	}
}
