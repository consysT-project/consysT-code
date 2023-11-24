package de.tuda.stg.consys.demo.crdts.invariants.examples;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.crdts.CRDTBenchRunnable;
import de.tuda.stg.consys.invariants.lib.examples.tournament.Player;
import de.tuda.stg.consys.invariants.lib.examples.tournament.Tournament;
import de.tuda.stg.consys.invariants.lib.examples.tournament.Tournaments;
import scala.Option;

import java.util.Random;
import java.util.stream.IntStream;

public class TournamentsBench extends CRDTBenchRunnable<Tournaments> {

	public static void main(String[] args) {
		JBenchExecution.execute("invariants-tournaments", TournamentsBench.class, args);
	}

	public TournamentsBench(JBenchStore adapter, BenchmarkConfig config) {
		super(adapter, config, Tournaments.class);
	}

	public final Player[] players = IntStream.range(0,99)
			.mapToObj(i -> new Player("player" + i)) // or x -> new Object(x).. or any other constructor
			.toArray(Player[]::new);

	public final Tournament[] tournaments = IntStream.range(0,9)
			.mapToObj(i -> new Tournament()) // or x -> new Object(x).. or any other constructor
			.toArray(Tournament[]::new);

	@Override
	@SuppressWarnings("consistency")
	public BenchmarkOperations operations() {
		final Random rand = new Random();

		return BenchmarkOperations.withUniformDistribution(new Runnable[] {
				() -> store().transaction(ctx -> {
					crdt.invoke("addPlayer", players[rand.nextInt(players.length)]);
					return Option.apply(0);
				}),
				() -> store().transaction(ctx -> {
					try {
						crdt.invoke("removePlayer", players[rand.nextInt(players.length)]);
					} catch (RuntimeException e) {

					}
					return Option.apply(0);
				}),
				() -> store().transaction(ctx -> {
					crdt.invoke("addTournament", tournaments[rand.nextInt(tournaments.length)]);
					return Option.apply(0);
				}),
				() -> store().transaction(ctx -> {
					try {
						crdt.invoke("removeTournament", tournaments[rand.nextInt(tournaments.length)]);
					} catch (RuntimeException e) {

					}
					return Option.apply(0);
				}),
				() -> store().transaction(ctx -> {
					try {
						crdt.invoke("enrollTournament", players[rand.nextInt(players.length)], tournaments[rand.nextInt(tournaments.length)]);
					} catch (RuntimeException e) {

					}
					return Option.apply(0);
				}),
				() -> store().transaction(ctx -> {
					try {
						crdt.invoke("disenrollTournament", players[rand.nextInt(players.length)], tournaments[rand.nextInt(tournaments.length)]);
					} catch (RuntimeException e) {

					}
					return Option.apply(0);
				}),
				() -> store().transaction(ctx -> {
					try {
						crdt.invoke("beginTournament", tournaments[rand.nextInt(tournaments.length)]);
					} catch (RuntimeException e) {

					}
					return Option.apply(0);
				}),
				() -> store().transaction(ctx -> {
					try {
						crdt.invoke("endTournament", tournaments[rand.nextInt(tournaments.length)]);
					} catch (RuntimeException e) {

					}
					return Option.apply(0);
				}),
				() -> store().transaction(ctx -> {
					try {
						crdt.invoke("addFunds", players[rand.nextInt(players.length)], rand.nextInt(99));
					} catch (RuntimeException e) {

					}
					return Option.apply(0);
				})
		});
	}


}
