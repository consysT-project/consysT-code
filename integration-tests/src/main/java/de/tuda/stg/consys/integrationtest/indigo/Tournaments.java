package de.tuda.stg.consys.integrationtest.indigo;

import com.google.inject.internal.util.Sets;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;

import java.util.Set;


//@Invariant("forall(P:p,T:t):− enrolled(p,t)=> player(p) and tournament(t)")
//@Invariant("forall(P:p):− budget(p)>=0")
//@Invariant("forall(T:t):− nrPlayers(t)<=Capacity")
//@Invariant("forall(T:t):− active(t) => nrPlayers(t) >= 1")
//@Invariant("forall(T:t,P:p):− active(t) and enrolled(p,t)=>participant(p,t)")
public abstract class Tournaments {

	private final Set<Player> players = Sets.newHashSet();
	private final Set<Tournament> tournaments = Sets.newHashSet();

	//@True("player($0)")
	@WeakOp
	void addPlayer(Player p) {
		players.add(p);
	}

	//@False("player($0)")
	@StrongOp
	void removePlayer(Player p) {
		players.remove(p);
	}

	//@True("tournament($0)")
	@WeakOp
	void addTournament(Tournament t) {
		tournaments.add(t);
	}

	//@False("tournament($0)")
	@WeakOp
	void removeTournament(Tournament t) {
		tournaments.remove(t);
	}

	//@True("enrolled($0,$1)")
	//@False("participant($0,$1)")
	//@Increments("nrPlayers($1,1)")
	//@Decrements("budget($0,1)")
	@StrongOp
	void enrollTournament(Player p,Tournament t) {
		t.enroll(p);
		p.incBudget(-1);
	}

	//@False("enrolled($0,$1)")
	//@Decrements("nrPlayers($1,1)")
	@WeakOp
	void disenrollTournament(Player p,Tournament t) {
		t.disenroll(p);
	}

	//@True("active($0)")
	//@True("participant(_,$0)")
	@WeakOp
	void beginTournament(Tournament t) {
		t.setActive(true);
	}

	//@False("active($0)")
	@WeakOp
	void endTournament(Tournament t) {
		t.setActive(false);
	}

	//@Increments("budget($0,$1)")
	@WeakOp
	void addFunds(Player p, int amount) {
		p.incBudget(amount);
	}
}














