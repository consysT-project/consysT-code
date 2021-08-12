package de.tuda.stg.consys.invariants.examples.multicounter;

import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;

import static de.tuda.stg.consys.utils.InvariantUtils.*;

@ReplicatedModel
public class SimpleCounter {

    public SimpleNumber[] incs;

    /* Constructors */
    //@ ensures (\forall int i; i >= 0 && i < numOfReplicas(); incs[i].hasValue(0));
    public SimpleCounter(int id) {
        this.incs = new SimpleNumber[numOfReplicas()];
        for(int i = 0; i < numOfReplicas(); ++i)
            incs[i] = new SimpleNumber(0);
    }

    //@ assignable \nothing;
    //@ ensures \result ==  (\sum int i; i >= 0 && i < numOfReplicas(); incs[i].getValue());
    int getValue() {
        int res = 0;
        for (int i = 0; i < numOfReplicas(); ++i) {
            res += incs[i].getValue();
        }
        return res;
    }

    //@ assignable incs[replicaId()];
    //@ ensures stateful( incs[replicaId()].setValue(incs[replicaId()].getValue() + 1) );
    void inc() {
        incs[replicaId()].setValue(incs[replicaId()].getValue() + 1);
    }

    /*@
    @ ensures (\forall int i; i >= 0 && i < numOfReplicas();
                     \old(incs[i].getValue()) >= other.incs[i].getValue() ?
                        stateful( incs[i].setValue(incs[i].getValue()) )
                        : stateful( incs[i].setValue(other.incs[i].getValue()) ));
    @*/
    void merge(SimpleCounter other) {
        for (int i = 0; i < numOfReplicas(); i++) {
            incs[i].setValue(Math.max(incs[i].getValue(), other.incs[i].getValue()));
        }
    }

}