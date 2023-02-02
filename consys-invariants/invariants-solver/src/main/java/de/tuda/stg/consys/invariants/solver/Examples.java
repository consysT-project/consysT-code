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
			Paths.get("consys-invariants/invariants-examples/src/main/java/de/tuda/stg/consys/invariants/lib/examples/bankaccount/BankAccount.java")
	};

	public static final Path[] BANK_ACCOUNT_LWW = new Path[] {
			Paths.get("consys-invariants/invariants-examples/src/main/java/de/tuda/stg/consys/invariants/lib/examples/bankaccountlww/BankAccountLWW.java")
	};

	public static final Path[] CREDIT_ACCOUNT = new Path[] {
//			Paths.get("consys-invariants/invariants-examples/src/main/java/de/tuda/stg/consys/invariants/lib/examples/creditaccount/SequentialCounter.java"),
//			Paths.get("consys-invariants/invariants-examples/src/main/java/de/tuda/stg/consys/invariants/lib/examples/creditaccount/SequentialCreditAccount.java"),
			Paths.get("consys-invariants/invariants-examples/src/main/java/de/tuda/stg/consys/invariants/lib/crdts/PNCounter.java"),
			Paths.get("consys-invariants/invariants-examples/src/main/java/de/tuda/stg/consys/invariants/lib/examples/creditaccount/ReplicatedCreditAccount.java")
	};

	public static final Path[] REPLICATED_CREDIT_ACCOUNT = new Path[] {
			Paths.get("consys-invariants/invariants-examples/src/main/java/de/tuda/stg/consys/invariants/lib/crdts/immutable/GCounter.java"),
			Paths.get("consys-invariants/invariants-examples/src/main/java/de/tuda/stg/consys/invariants/lib/crdts/immutable/PNCounter.java"),
			Paths.get("consys-invariants/invariants-examples/src/main/java/de/tuda/stg/consys/invariants/lib/examples/creditaccount/ReplicatedCreditAccount.java")
	};


	public static final Path[] JOINT_BANK_ACCOUNT = new Path[] {
			Paths.get("consys-invariants/invariants-examples/src/main/java/de/tuda/stg/consys/invariants/lib/crdts/PNCounter.java"),
			Paths.get("consys-invariants/invariants-examples/src/main/java/de/tuda/stg/consys/invariants/lib/examples/jointbankaccount/JointBankAccount.java")
	};

	public static final Path[] RESETTABLE_COUNTER = new Path[] {
			Paths.get("consys-invariants/invariants-examples/src/main/java/de/tuda/stg/consys/invariants/lib/examples/resettablecounter/ResettableCounter.java")
	};


	public static final Path[] CONSENSUS = new Path[] {
			Paths.get("consys-invariants/invariants-examples/src/main/java/de/tuda/stg/consys/invariants/lib/examples/consensus/Consensus.java"),
	};

	public static final Path[] DISTRIBUTED_LOCK = new Path[] {
			Paths.get("consys-invariants/invariants-examples/src/main/java/de/tuda/stg/consys/invariants/lib/examples/distributedlock/DistributedLock.java"),
	};

	public static final Path[] TOURNAMENT = new Path[] {
			Paths.get("consys-invariants/invariants-examples/src/main/java/de/tuda/stg/consys/invariants/lib/examples/tournament/Player.java"),
			Paths.get("consys-invariants/invariants-examples/src/main/java/de/tuda/stg/consys/invariants/lib/examples/tournament/Tournament.java"),
			Paths.get("consys-invariants/invariants-examples/src/main/java/de/tuda/stg/consys/invariants/lib/examples/tournament/GSetPlayer.java"),
			Paths.get("consys-invariants/invariants-examples/src/main/java/de/tuda/stg/consys/invariants/lib/examples/tournament/TwoPhaseSetPlayer.java"),
			Paths.get("consys-invariants/invariants-examples/src/main/java/de/tuda/stg/consys/invariants/lib/examples/tournament/GSetTournament.java"),
			Paths.get("consys-invariants/invariants-examples/src/main/java/de/tuda/stg/consys/invariants/lib/examples/tournament/TwoPhaseSetTournament.java"),
			Paths.get("consys-invariants/invariants-examples/src/main/java/de/tuda/stg/consys/invariants/lib/examples/tournament/Tournaments.java")
	};
	
	public static final Path[] CRDTLIB = new Path[] {
			Paths.get("consys-invariants/invariants-examples/src/main/java/de/tuda/stg/consys/invariants/lib/crdts/GCounter.java"),
			Paths.get("consys-invariants/invariants-examples/src/main/java/de/tuda/stg/consys/invariants/lib/crdts/PNCounter.java"),
			Paths.get("consys-invariants/invariants-examples/src/main/java/de/tuda/stg/consys/invariants/lib/crdts/GSet.java"),
			Paths.get("consys-invariants/invariants-examples/src/main/java/de/tuda/stg/consys/invariants/lib/crdts/TwoPhaseSet.java"),
	};

	public static final Path[] GCOUNTER = new Path[] {
			Paths.get("consys-invariants/invariants-examples/src/main/java/de/tuda/stg/consys/invariants/lib/crdts/GCounter.java"),
	};

	public static final Path[] PNCOUNTER = new Path[] {
			Paths.get("consys-invariants/invariants-examples/src/main/java/de/tuda/stg/consys/invariants/lib/crdts/PNCounter.java"),
	};

	public static final Path[] GSET = new Path[] {
			Paths.get("consys-invariants/invariants-examples/src/main/java/de/tuda/stg/consys/invariants/lib/crdts/GSet.java"),
	};

	public static final Path[] TWOPHASESET = new Path[] {
			Paths.get("consys-invariants/invariants-examples/src/main/java/de/tuda/stg/consys/invariants/lib/crdts/GSet.java"),
			Paths.get("consys-invariants/invariants-examples/src/main/java/de/tuda/stg/consys/invariants/lib/crdts/TwoPhaseSet.java"),
	};


}
