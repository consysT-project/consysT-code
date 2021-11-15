package de.tuda.stg.consys.integrationtest.indigo;

import com.google.inject.internal.util.Sets;
import de.tuda.stg.consys.checker.qual.Mutable;

import java.util.Set;

public class Tournament {
	private final Set<Player> enrolled = (@Mutable Set) Sets.newHashSet();
	private boolean active = false;

	public void enroll(Player p) {
		enrolled.add(p);
	}

	public void disenroll(Player p) {
		enrolled.remove(p);
	}


	public int numOfPlayers() {
		return enrolled.size();
	}

	public boolean isActive() {
		return active;
	}

	public void setActive(boolean active) {
		this.active = active;
	}
}
