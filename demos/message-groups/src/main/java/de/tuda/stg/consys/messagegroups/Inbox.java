package de.tuda.stg.consys.messagegroups;

import java.io.Serializable;
import java.util.HashSet;
import java.util.Set;

/**
 * Created on 04.04.19.
 *
 * @author Mirko Köhler
 */
public class Inbox implements Serializable {

	Set<String> entries = new HashSet<>();

	Set<String> getEntries() {
		return entries;
	}

	void add(String msg) {
		entries.add(msg);
	}
}
