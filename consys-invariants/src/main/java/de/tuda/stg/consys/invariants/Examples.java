package de.tuda.stg.consys.invariants;

import de.tuda.stg.consys.invariants.subset.ProgramConfig;

import java.nio.file.Path;
import java.nio.file.Paths;

public class Examples {

	public static final ProgramConfig DEFAULT_CONFIG = new ProgramConfig(
			false,
			false,
			1,
			"replica-01",
			3
	);

	public static final ProgramConfig STATEFUL_CONFIG = new ProgramConfig(
			true,
			false,
			1,
			"replica-01",
			3
	);


	public static final Path[] BANK_ACCOUNT = new Path[] {
			Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/bankaccount/BankAccount.java")
	};

	public static final Path[] CREDIT_ACCOUNT = new Path[] {
			Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/creditaccount/SequentialCounter.java"),
			Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/creditaccount/SequentialCreditAccount.java")
	};

	public static final Path[] GSET = new Path[] {
			Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/gset/GSet.java")
	};

	public static final Path[] MULTICLASS_COUNTER = new Path[] {
			Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/multicounter/SimpleNumber.java"),
			Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/multicounter/SimpleCounter.java")
	};




}
