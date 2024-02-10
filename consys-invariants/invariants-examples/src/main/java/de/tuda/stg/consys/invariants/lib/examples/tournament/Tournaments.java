package de.tuda.stg.consys.invariants.lib.examples.tournament;

import de.tuda.stg.consys.Mergeable;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import de.tuda.stg.consys.annotations.methods.WeakOp;


import java.io.Serializable;

import static de.tuda.stg.consys.invariants.utils.InvariantUtils.stateful;



// 1 EnrollTournament pre-condition: Invariant("forall(P:p,T:t):− enrolled(p,t)=> player(p) and tournament(t)")
// 2 Done:  Invariant("forall(P:p):− budget(p)>=0")
// 3 Done: Invariant("forall(T:t):− nrPlayers(t)<=Capacity")
// 4 Done: Invariant("forall(T:t):− active(t) => nrPlayers(t) >= 1")
// 5 Kinda implemented in general but not sure where exactly we can say: Invariant("forall(T:t,P:p):− active(t) and enrolled(p,t)=>participant(p,t)")
@ReplicatedModel public class Tournaments implements Mergeable<Tournaments>, Serializable {


    private final TwoPhaseSetPlayer players;
    private final TwoPhaseSetTournament tournaments;

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
        players = new TwoPhaseSetPlayer();
        tournaments = new TwoPhaseSetTournament();
    }

    // True("player($0)")
    // WeakOp
    /*@
    @ assignable players;
    @ ensures players.contains(p);
    @ ensures (\forall Player p2; \old(players.contains(p2)); players.contains(p2));
    @ ensures (\forall Player p2; players.contains(p2) && p2.equals(p) == false; \old(players.contains(p2)));
    @*/
    @WeakOp public void addPlayer(Player p) {
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
    @WeakOp public void removePlayer(Player p) {
        if (!players.contains(p))
            throw new IllegalArgumentException();

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
    @WeakOp public void addTournament(Tournament t) {
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
    @WeakOp public void removeTournament(Tournament t) {
        if (!tournaments.contains(t))
            throw new IllegalArgumentException();

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
    @ ensures p.getBudget() == \old(p.getBudget()) - 1;
    @ ensures (\forall Player p2; \old(t.hasParticipant(p2)) ; t.hasParticipant(p2));
    @ ensures (\forall Player p2; t.hasParticipant(p2) && p2.equals(p) == false; \old(t.hasParticipant(p2)));
    @*/
    @WeakOp public void enrollTournament(Player p,Tournament t) {
        if (!tournaments.contains(t))
            throw new IllegalArgumentException();
        if (!players.contains(p))
            throw new IllegalArgumentException();
        if (t.hasParticipant(p))
            throw new IllegalArgumentException();

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
    @WeakOp public void disenrollTournament(Player p,Tournament t) {
        if (!tournaments.contains(t))
            throw new IllegalArgumentException();
        if (!players.contains(p))
            throw new IllegalArgumentException();
        if (!t.hasParticipant(p))
            throw new IllegalArgumentException();

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
    @WeakOp public void beginTournament(Tournament t) {
        if (!tournaments.contains(t))
            throw new IllegalArgumentException();
        if (t.isActive())
            throw new IllegalArgumentException();

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
    @WeakOp public void endTournament(Tournament t) {
        if (!tournaments.contains(t))
            throw new IllegalArgumentException();
        if (!t.isActive())
            throw new IllegalArgumentException();


        t.setActive(false);
    }

    // Increments("budget($0,$1)")
    // WeakOp
    /*@
    @ requires amount >= 0;
    @ assignable p;
    @ ensures p.getBudget() == \old(p.getBudget()) + amount;
    @*/
    @WeakOp public void addFunds(Player p, int amount) {
        if (amount < 0)
            throw new IllegalArgumentException();

        p.incBudget(amount);
    }

    /*@
	@ ensures stateful(players.merge(other.players));
	@ ensures stateful(tournaments.merge(other.tournaments));
    @*/
    public Void merge(Tournaments other) {
        players.merge(other.players);
        tournaments.merge(other.tournaments);

        return null;
    }

}
