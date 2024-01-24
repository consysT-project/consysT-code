package de.tuda.stg.consys.invariants.lib.examples.bankaccount;

import de.tuda.stg.consys.Mergeable;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.lang.Math;

import static de.tuda.stg.consys.invariants.utils.InvariantUtils.numOfReplicas;
import static de.tuda.stg.consys.invariants.utils.InvariantUtils.replicaId;
import static de.tuda.stg.consys.invariants.utils.InvariantUtils.arrayMax;


@ReplicatedModel public class BankAccount implements Mergeable<BankAccount>, Serializable {
    /* Constants */
    // Constants have to be declared with static final.
    public static final String ACCOUNT_TYPE = "BANK";

    /* Fields */
    // Virtual fields that can be accessed in constraints with `this` or using normal field references.
    public final int[] incs, decs ;

    /* Invariants */
    // Invariant definitions can use constants and fields.
    // Pure methods (i.e. methods that do not change the object state) that only use Z3 types can be used in constraints.

    //@ public invariant getValue() >= 0;

    /* Constructors */
    // Constructors define the initial state of an object.

    //@ ensures getValue() == 0;
    //@ ensures (\forall int i; true; incs[i] == 0);
    //@ ensures (\forall int i; true; decs[i] == 0);
    public BankAccount() {
        incs = new int[numOfReplicas()];
        decs = new int[numOfReplicas()];
    }


    /* Methods */
    // Methods define the interface for a replicated object.
    // Constraints on methods can use fields, constants, and method parameters.
    // Methods need an @assignable clause which specifies the fields that can change.
    // \old in postconditions defines the state before the method call.
    // \result in postconditions defines the return value of the method.

    //@ assignable \nothing;
    //@ ensures \result == (\sum int i; i >= 0 && i < numOfReplicas(); \old(incs[i]));
     
    int sumIncs() {
        int res = 0;
        for (int inc : incs) {
            res += inc;
        }
        return res;
    }

    //@ assignable \nothing;
    //@ ensures \result == (\sum int i; i >= 0 && i < numOfReplicas(); \old(decs[i]));
      int sumDecs() {
        int result = 0;
        for (int dec : decs) {
            result += dec;
        }
        return result;
    }

    //@ assignable \nothing;
    //@ ensures \result == sumIncs() - sumDecs();
      public int getValue() {
        return sumIncs() - sumDecs();
    }


    //@ requires val >= 0;
    //@ assignable incs[replicaId()];
    //@ ensures incs[replicaId()] == \old(incs[replicaId()]) + val;
     public void deposit(int val) {
        if (val < 0)
            throw new IllegalArgumentException("value negative");

        incs[replicaId()] = incs[replicaId()] + val;
    }


    //@ requires val >= 0;
    //@ requires  getValue() >= val;
    //@ assignable decs[replicaId()];
    //@ ensures decs[replicaId()] == \old(decs[replicaId()]) + val;
    @StrongOp public void withdraw(int val) {
        if (val < 0)
            throw new IllegalArgumentException("value negative");
        if (val > getValue())
            throw new IllegalArgumentException("not enough balance to withdraw");

        decs[replicaId()] = decs[replicaId()] + val;
    }


    /* Merge method */
    // Merge defines the conflict resolution of replicated objects.
    // Constraints can use fields, constants, and the other parameter.
    //@ requires (\sum int i; i >= 0 && i < numOfReplicas(); Math.max(incs[i], other.incs[i])) - (\sum int i; i >= 0 && i < numOfReplicas(); Math.max(decs[i], other.decs[i])) >= 0;
    //@ ensures (\forall int i; true; incs[i] == Math.max(\old(incs[i]), other.incs[i]) && decs[i] == Math.max(\old(decs[i]), other.decs[i]));
    public Void merge(BankAccount other) {
        for (int i = 0; i < numOfReplicas(); i++) {
            incs[i] = Math.max(incs[i], other.incs[i]);
            decs[i] = Math.max(decs[i], other.decs[i]);
        }
        return null;
    }
}


// ensures incs == arrayMax(\old(incs), other.incs) && decs == arrayMax(\old(decs), other.decs);
