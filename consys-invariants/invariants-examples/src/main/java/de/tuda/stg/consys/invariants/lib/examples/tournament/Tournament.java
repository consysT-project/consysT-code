package de.tuda.stg.consys.invariants.lib.examples.tournament;

import com.google.common.collect.Sets;
import de.tuda.stg.consys.annotations.invariants.DataModel;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import org.checkerframework.dataflow.qual.SideEffectFree;


import java.io.Serializable;
import java.util.Set;

@DataModel public class Tournament implements Serializable {
    private final Set<Player> enrolled = Sets.newHashSet();
    private int capacity = 10;
    private boolean active = false;

     public void enroll(Player p) {
        enrolled.add(p);
    }

     public void disenroll(Player p) {
        enrolled.remove(p);
    }

    //@ assignable \nothing;
      public boolean hasParticipant(Player p) {
        return enrolled.contains(p);
    }

    //@ assignable \nothing;
      public int numOfPlayers() {
        return enrolled.size();
    }

    //@ assignable \nothing;
      public boolean isActive() {
        return active;
    }

     public void setActive(boolean active) {
        this.active = active;
    }

    //@ assignable \nothing;
      public int getCapacity() {
        return capacity;
    }

     public void setCapacity(int c) {
        capacity = c;
    }

}
