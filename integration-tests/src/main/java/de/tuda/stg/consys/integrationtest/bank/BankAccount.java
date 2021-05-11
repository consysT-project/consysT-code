package de.tuda.stg.consys.integrationtest.bank;

import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;

public class BankAccount implements Serializable {

    private int value = 0;
    private Ref<@Mixed User> user;

    //TODO: These two entries should be internal only.
    private int timestamp = 0;
    private final int replicaId;

    //@ public invariant value >= 0;

    /*@
    @ ensures value == 0;
    @ ensures timestamp == 0;
    @ ensures user == u;
    @*/
    public BankAccount(Ref<@Mixed User> u, int replicaId) {
        this.user = u;
        this.replicaId = replicaId;
    }

    /*@
    @ requires d >= 0;
    @ ensures value == \old(value) + d;
    @ ensures timestamp == \old(timestamp) + 1;
    @*/
    public void deposit(int d) {
        if (d >= 0) {
            value = value + d;
            timestamp += 1;
        } else {
            throw new IllegalArgumentException("cannot deposit negative amount");
        }
    }

    /*@
    @ requires \old(value) - w >= 0;
    @ ensures value == \old(value) - w;
    @ ensures timestamp == \old(timestamp) + 1;
    @*/
    public void withdraw(int w) {
        if (value - w >= 0) {
            value = value - w;
            timestamp += 1;
        } else {
            throw new IllegalArgumentException("not enough money in account for withdraw");
        }
    }

    public int getBalance() {
        return value;
    }


    /*@
    @ requires \old(value) >= 0;
    @ requires other.value >= 0;
    @ requires \old(user) == other.user;
    @ ensures (\old(timestamp) == other.timestamp && replicaId < other.replicaId ) ==> (value == \old(value)) && (timestamp == \old(timestamp));
    @ ensures (\old(timestamp) == other.timestamp && replicaId > other.replicaId ) ==> (value == other.value) && (timestamp == other.timestamp);
    @ ensures (\old(timestamp) == other.timestamp && replicaId == other.replicaId ) ==> (value == \old(value)) && (timestamp == \old(timestamp)) && (value == other.value) && (timestamp == other.timestamp);
    @*/
    //TODO: The merge function should be internal only.
    public void merge(BankAccount other) {
        if (value >= 0 && other.value >= 0) {
            if (timestamp > other.timestamp) {
                //Do nothing
            } else if (timestamp < other.timestamp || replicaId > other.replicaId) {
                value = other.value;
                timestamp = other.timestamp;
            } else if (replicaId < other.replicaId) {

            } else {
                //replicaId == other.replicaId && timestamp == other.timestamp
                //This case *should* never happen. One replica should always have increasing timestamps.
                throw new IllegalArgumentException("cannot merge two values with same timestamp from same replica.");
            }
        }
    }
}
