package de.tuda.stg.consys.invariants.solver;

import de.tuda.stg.consys.invariants.solver.subset.ProgramConfig;

import java.nio.file.Path;
import java.nio.file.Paths;

public class Examples {

	public static final ProgramConfig DEFAULT_CONFIG = new ProgramConfig(
			false,
			false,
			true,
			1,
			"replica-01",
			3
	);

	public static final ProgramConfig STATEFUL_CONFIG = new ProgramConfig(
			true,
			false,
			true,
			1,
			"replica-01",
			3
	);


	public static final Path[] BANK_ACCOUNT = new Path[] {
			Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/bankaccount/BankAccount.java")
	};

	public static final Path[] CREDIT_ACCOUNT = new Path[] {
			Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/creditaccount/SequentialCounter.java"),
			Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/creditaccount/SequentialCreditAccount.java"),
			//Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/creditaccount/ReplicatedCounter.java"),
			Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/crdtlib/PNCounter.java"),
			Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/creditaccount/ReplicatedCreditAccount.java")
	};

	public static final Path[] REPLICATED_CREDIT_ACCOUNT = new Path[] {
			Paths.get("consys-annotations/src/main/java/de/tuda/stg/consys/Mergeable.java"),
			Paths.get("consys-invariants/src/main/java/de/tuda/stg/consys/invariants/crdts/PNCounter.java"),
			Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/creditaccount/ReplicatedCreditAccount.java")
	};

	public static final Path[] REPLICATED_CREDIT_ACCOUNT_OLD = new Path[] {
			Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/crdtlib/PNCounter.java"),
			Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/creditaccountold/ReplicatedCreditAccount.java")
	};

	public static final Path[] GSET = new Path[] {
			Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/gset/GSet.java")
	};

	public static final Path[] MULTICLASS_COUNTER = new Path[] {
			Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/multicounter/SimpleNumber.java"),
			Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/multicounter/SimpleCounter.java")
	};

	public static final Path[] JOINTBANKACCOUNT = new Path[] {
			//Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/pncounter/PNCounterCRDT.java"),
			Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/crdtlib/PNCounter.java"),
			Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/jointbankaccount/JointBankAccount.java")
	};

	public static final Path[] TOURNAMENT = new Path[] {
			Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/tournament/Player.java"),
			Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/tournament/Tournament.java"),
			Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/tournament/GSetPlayer.java"),
			Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/tournament/TwoPhaseSetPlayer.java"),
			Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/tournament/GSetTournament.java"),
			Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/tournament/TwoPhaseSetTournament.java"),
			Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/tournament/Tournaments.java")
	};
	
	public static final Path[] CRDTLIB = new Path[] {
			Paths.get("consys-annotations/src/main/java/de/tuda/stg/consys/Mergeable.java"),

			//Paths.get("consys-invariants/crdtlib/GCounter.java"),
			//Paths.get("consys-invariants/crdtlib/PNCounter.java"),
			//Paths.get("consys-invariants/crdtlib/GSet.java"),
			//Paths.get("consys-invariants/crdtlib/TwoPhaseSet.java"),
			//Paths.get("consys-invariants/crdtlib/ORSet.java")
			Paths.get("consys-invariants/src/main/java/de/tuda/stg/consys/invariants/crdts/GCounter.java"),
			Paths.get("consys-invariants/src/main/java/de/tuda/stg/consys/invariants/crdts/PNCounter.java"),
			//Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/crdtlib/GSet.java"),
			//Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/crdtlib/TwoPhaseSet.java"),
			//Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/crdtlib/ORSet.java"),

//			Paths.get("consys-invariants/src/main/java/de/tuda/stg/consys/invariants/crdts/GMap.java"),
//			Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/crdtlib/LWWRegister.java"),
//			Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/crdtlib/ORMap.java")
	};

	public static final Path[] IMMUTABLE_CRDTLIB = new Path[] {
//			Paths.get("consys-annotations/src/main/java/de/tuda/stg/consys/Mergeable.java"),
//			Paths.get("consys-invariants/invariants-lib/src/main/java/de/tuda/stg/consys/invariants/lib/Array.java"),
			Paths.get("consys-invariants/invariants-examples/src/main/java/de/tuda/stg/consys/invariants/lib/crdts/immutable/GCounter.java")
	};



}
