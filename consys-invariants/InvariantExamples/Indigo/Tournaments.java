import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;

import com.google.inject.internal.util.Sets;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;

import java.util.Set;


// 1 EnrollTournament pre-condition: Invariant("forall(P:p,T:t):− enrolled(p,t)=> player(p) and tournament(t)")
// 2 Done:  Invariant("forall(P:p):− budget(p)>=0")
// 3 Done: Invariant("forall(T:t):− nrPlayers(t)<=Capacity")
// 4 Done: Invariant("forall(T:t):− active(t) => nrPlayers(t) >= 1")
// 5 Kinda implemented in general but not sure where exactly we can say: Invariant("forall(T:t,P:p):− active(t) and enrolled(p,t)=>participant(p,t)")
@ReplicatedModel public abstract class Tournaments {

    private final Set<Player> players = Sets.newHashSet();
    private final Set<Tournament> tournaments = Sets.newHashSet();

    /*@
    @ public invariant (\forall Player p; players.contains(p); p.getBudget() >= 0);
    @ public invariant (\forall Tournament t; tournaments.contains(t); t.numOfPlayers() <= t.getCapacity() );
    @ public invariant (\forall Tournament t; tournaments.contains(t) && t.isActive(); t.numOfPlayers() >= 1);
    @*/


    /*@
    @ ensures players.isEmpty();
    @ ensures tournaments.isEmpty();
    @*/
    public Tournaments() {

    }

    // True("player($0)")
    // WeakOp
    /*@
    @ assignable players;
    @ ensures players.contains(p);
    @ ensures (\forall Player p2; \old(players.contains(p2)); players.contains(p2));
    @ ensures (\forall Player p2; players.contains(p2) && p2.equals(p) == false; \old(players.contains(p2)));
    @*/
    void addPlayer(Player p) {
        players.add(p);
    }

    // False("player($0)")
    // StrongOp
    /*@
    @ requires players.contains(p);
    @ assignable players;
    @ ensures players.contains(p) == false;
    @ ensures (\forall Player p2; \old(players.contains(p2)) && p2.equals(p) == false; players.contains(p2));
    @ ensures (\forall Player p2; players.contains(p2); \old(players.contains(p2)));
    @*/
    void removePlayer(Player p) {
        players.remove(p);
    }

    // True("tournament($0)")
    // WeakOp
    /*@
    @ assignable tournaments;
    @ ensures tournaments.contains(t);
    @ ensures (\forall Tournament t2; \old(tournaments.contains(t2)); tournaments.contains(t2));
    @ ensures (\forall Tournament t2; tournaments.contains(t2) && t2.equals(t) == false; \old(tournaments.contains(t2)));
    @*/
    void addTournament(Tournament t) {
        tournaments.add(t);
    }

    // False("tournament($0)")
    // WeakOp
    /*@
    @ requires tournaments.contains(t);
    @ assignable tournaments;
    @ ensures tournaments.contains(t) == false;
    @ ensures (\forall Tournament t2; \old(tournaments.contains(t2)) && t2.equals(t) == false; tournaments.contains(t2));
    @ ensures (\forall Tournament t2; tournaments.contains(t2); \old(tournaments.contains(t2)));
    @*/
    void removeTournament(Tournament t) {
        tournaments.remove(t);
    }

    // True("enrolled($0,$1)")
    // False("participant($0,$1)")
    // Increments("nrPlayers($1,1)")
    // Decrements("budget($0,1)")
    // StrongOp

    /*@
    @ requires tournaments.contains(t);
    @ requires players.contains(p);
    @ requires t.hasParticipant(p) == false;
    @ assignable p, t;
    @ ensures t.hasParticipant(p);
    @ ensures p.getBudget() == \old(p.getBudget) - 1;
    @ ensures (\forall Player p2; \old(t.hasParticipant(p2)) ; t.hasParticipant(p2));
    @ ensures (\forall Player p2; t.hasParticipant(p2) && p2.equals(p) == false; \old(t.hasParticipant(p2)));
    @*/
    void enrollTournament(Player p,Tournament t) {
        t.enroll(p);
        p.incBudget(-1);
    }

    // False("enrolled($0,$1)")
    // Decrements("nrPlayers($1,1)")
    // WeakOp
    /*@
    @ requires tournaments.contains(t);
    @ requires players.contains(p);
    @ requires t.hasParticipant(p);
    @ assignable t;
    @ ensures t.hasParticipant(p) == false;
    @ ensures (\forall Player p2; \old(t.hasParticipant(p2)) && p2.equals(p) == false; t.hasParticipant(p2));
    @ ensures (\forall Player p2; t.hasParticipant(p2); \old(t.hasParticipant(p2)));
    @*/
    void disenrollTournament(Player p,Tournament t) {
        t.disenroll(p);
    }

    // True("active($0)")
    // True("participant(_,$0)")
    // WeakOp
    /*@
    @ requires tournaments.contains(t);
    @ requires t.isActive() == false;
    @ assignable t;
    @ ensures t.isActive();
    @ ensures (\forall Player p2; \old(t.hasParticipant(p2)) ; t.hasParticipant(p2));
    @ ensures (\forall Player p2; t.hasParticipant(p2); \old(t.hasParticipant(p2)));
    @*/
    void beginTournament(Tournament t) {
        t.setActive(true);
    }

    // False("active($0)")
    // WeakOp
    /*@
    @ requires tournaments.contains(t);
    @ requires t.isActive();
    @ assignable t;
    @ ensures t.isActive() == false;
    @ ensures (\forall Player p2; \old(t.hasParticipant(p2)) ; t.hasParticipant(p2));
    @ ensures (\forall Player p2; t.hasParticipant(p2); \old(t.hasParticipant(p2)));
    @*/
    void endTournament(Tournament t) {
        t.setActive(false);
    }

    // Increments("budget($0,$1)")
    // WeakOp
    /*@
    @ requires amount >= 0;
    @ assignable p;
    @ ensures p.getBudget() == \old(p.getBudget()) + amount;
    @*/
    void addFunds(Player p, int amount) {
        p.incBudget(amount);
    }
}
