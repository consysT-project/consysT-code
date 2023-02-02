package org.conloc.invariants.lib.examples.tournament;

import com.google.common.collect.Sets;
import org.conloc.annotations.invariants.DataModel;


import java.util.Set;

import static org.conloc.invariants.utils.InvariantUtils.numOfReplicas;
import static org.conloc.invariants.utils.InvariantUtils.replicaId;
import static org.conloc.invariants.utils.InvariantUtils.stateful;

@DataModel
public class Tournament {
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
