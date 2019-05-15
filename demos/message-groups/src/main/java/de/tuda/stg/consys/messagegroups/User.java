package de.tuda.stg.consys.messagegroups;

import de.tuda.stg.consys.objects.japi.JRef;

import java.io.Serializable;
import java.util.Set;


/**
 * message delivery (Figure 4), user creation, inbox checking, and group joining
 *
 * @author Mirko Köhler
 */
public class User implements Serializable {

	public final JRef<Inbox> inbox;
	public final String name;

	public User(JRef<Inbox> inbox, String name) {
		this.inbox = inbox;
		this.name = name;
	}

	public void send(String msg) {
//		System.out.println("[Message] " + name + ": " + msg);
		inbox.invoke("add", msg);
	}

	public Set<String> getInbox() {
		return inbox.invoke("getEntries");
	}


	public void printInbox() {
		String s = "[Inbox] " + name + ": " + inbox.invoke("toString");
		System.out.println(s);
	}
}
