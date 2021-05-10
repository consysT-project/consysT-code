package de.tuda.stg.consys.integrationtest.bank;

import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;

public class BankAccount implements Serializable {

    private int value = 0;
    private int timestamp = 0;
    private Ref<@Mixed User> user;

    //@ public invariant value >= 0;

    /*@
    @ ensures value == 0;
    @ ensures timestamp == 0;
    @ ensures user == u;
    @*/
    public BankAccount(@Mixed Ref<@Mixed User> u) {
        this.user = u;
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
    @ requires \old(timestamp) == other.timestamp ==> \old(value) == other.value; //TODO: This seems to be unnecessary?
    @ ensures (\old(timestamp) > other.timestamp) ==> (value == \old(value)) && (timestamp == \old(timestamp));
    @ ensures (\old(timestamp) < other.timestamp) ==> (value == other.value) && (timestamp == other.timestamp);
    @ ensures (\old(timestamp) == other.timestamp) ==> (value == \old(value)) && (timestamp == \old(timestamp)) &&
                                                       (value == other.value) && (timestamp == other.timestamp); //TODO: This seems wrong
    @*/
    public void merge(BankAccount other) {
        if (value >= 0 && other.value >= 0) {
            if (timestamp > other.timestamp) {
                //Do nothing
            } else if (timestamp < other.timestamp) {
                value = other.value;
                timestamp = other.timestamp;
            } else {
                //TODO: Deterministically choose one value
            }
        }
    }
}
