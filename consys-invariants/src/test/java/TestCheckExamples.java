import de.tuda.stg.consys.invariants.Examples;
import de.tuda.stg.consys.invariants.Main;
import de.tuda.stg.consys.invariants.subset.ProgramConfig;
import org.junit.Test;

import java.nio.file.Path;
import java.nio.file.Paths;


public class TestCheckExamples {
	/* INFO: to run the tests in IntelliJ, change the working directory in the run configurations to the consys-code folder. */

	public static Path[] ADDITIONAL_LIBS = new Path[]{
			Paths.get("consys-invariants", "src", "main", "resources", "guava-14.0.1.jar")
	};

	@Test
	public void testBankAccount() {
		Main.runChecker(Examples.DEFAULT_CONFIG, null, Examples.BANK_ACCOUNT);
	}

	@Test
	public void testCreditAccount() {
		Main.runChecker(Examples.STATEFUL_CONFIG, null, Examples.CREDIT_ACCOUNT);
	}

	@Test
	public void testGSet() {
		Main.runChecker(Examples.DEFAULT_CONFIG, null, Examples.GSET);
	}

	@Test
	public void testSimpleCounter() {
		Main.runChecker(Examples.STATEFUL_CONFIG, null, Examples.MULTICLASS_COUNTER);
	}

	@Test
	public void testTournament() {
		Main.runChecker(Examples.STATEFUL_CONFIG, ADDITIONAL_LIBS, Examples.TOURNAMENT);
	}

	@Test
	public void testJointBankAccount() {
		Main.runChecker(Examples.STATEFUL_CONFIG, ADDITIONAL_LIBS, Examples.JOINTBANKACCOUNT);
	}

	@Test
	public void testCRDTLIB() {
		Main.runChecker(Examples.STATEFUL_CONFIG, ADDITIONAL_LIBS, Examples.CRDTLIB);
	}

}
