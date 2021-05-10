package de.tuda.stg.consys.integrationtest.bank;

import de.tuda.stg.consys.checker.qual.Mixed;

import java.io.Serializable;

public class User extends Object implements Serializable {

	private String name;
	private int timestamp = 0;

	/*@
   @ ensures name == n;
   @*/
	public User(@Mixed String n) {
		this.name = n;
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
   @ requires \old(value) >= 0;
   @ requires other.value >= 0;
   @ requires \old(timestamp) == other.timestamp ==> \old(value) == other.value; //TODO: This seems to be unnecessary?
   @ ensures (\old(timestamp) > other.timestamp) ==> (value == \old(value)) && (timestamp == \old(timestamp));
   @ ensures (\old(timestamp) < other.timestamp) ==> (value == other.value) && (timestamp == other.timestamp);
   @ ensures (\old(timestamp) == other.timestamp) ==> (value == \old(value)) && (timestamp == \old(timestamp)) &&
													  (value == other.value) && (timestamp == other.timestamp); //TODO: This seems wrong
   @*/
	public void merge(User other) {
		if (timestamp > other.timestamp) {
			//Do nothing
		} else if (timestamp < other.timestamp) {
			name = other.name;
			timestamp = other.timestamp;
		} else {
			//TODO: Deterministically choose one value
		}

	}
}
