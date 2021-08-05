import de.tuda.stg.consys.annotations.invariants.DataModel;

import com.google.inject.internal.util.Sets;

import java.util.Set;

@DataModel public class Tournament {
    private final Set<Player> enrolled = Sets.newHashSet();
    private int capacity = 10;
    private boolean active = false;

    public void enroll(Player p) {
        enrolled.add(p);
    }

    public void disenroll(Player p) {
        enrolled.remove(p);
    }

    public boolean hasParticipant(Player p) {return enrolled.contains(p); }

    public int numOfPlayers() {
        return enrolled.size();
    }

    public boolean isActive() {
        return active;
    }

    public void setActive(boolean active) {
        this.active = active;
    }

    public int getCapacity() { return capacity; }

    public void setCapacity(int c) {capacity = c;}
}
