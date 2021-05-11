package de.tuda.stg.consys.integrationtest.bank;

import de.tuda.stg.consys.checker.qual.Mixed;

import java.io.Serializable;

public class User extends Object implements Serializable {

	private String name;

	//TODO: These two entries should be internal only.
	private int timestamp = 0;
	private final int replicaId;

	/*@
   @ ensures name == n;
   @*/
	public User(@Mixed String n, int replicaId) {
		this.name = n;
		this.replicaId = replicaId;
	}

	public String getName() {
		return name;
	}

	/*@
    @ ensures name == n;
    @*/
	public void setName(String n) {
		name = n;
	}

	/*@
   @ ensures (\old(timestamp) == other.timestamp && replicaId < other.replicaId ) ==> (name == \old(name)) && (timestamp == \old(timestamp));
   @ ensures (\old(timestamp) == other.timestamp && replicaId > other.replicaId ) ==> (name == other.name) && (timestamp == other.timestamp);
   @ ensures (\old(timestamp) == other.timestamp && replicaId == other.replicaId ) ==> (name == \old(name)) && (timestamp == \old(timestamp)) && (name == other.name) && (timestamp == other.timestamp);
   @*/
	//TODO: The merge function should be internal only.
	public void merge(User other) {
		if (timestamp > other.timestamp) {
			//Do nothing
		} else if (timestamp < other.timestamp || replicaId > other.replicaId) {
			name = other.name;
			timestamp = other.timestamp;
		} else if (replicaId < other.replicaId) {

		} else {
			//replicaId == other.replicaId && timestamp == other.timestamp
			//This case *should* never happen. One replica should always have increasing timestamps.
			throw new IllegalArgumentException("cannot merge two values with same timestamp from same replica.");
		}
	}

}
