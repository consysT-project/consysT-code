import de.tuda.stg.consys.invariants.Examples;
import de.tuda.stg.consys.invariants.Main;
import de.tuda.stg.consys.invariants.subset.ProgramConfig;
import org.junit.Test;


public class TestCheckExamples {
	/* INFO: to run the tests in IntelliJ, change the working directory in the run configurations to the consys-code folder. */

	@Test
	public void testBankAccount() {
		Main.runChecker(Examples.DEFAULT_CONFIG, Examples.BANK_ACCOUNT);
	}

	@Test
	public void testCreditAccount() {
		Main.runChecker(Examples.STATEFUL_CONFIG, Examples.CREDIT_ACCOUNT);
	}

	@Test
	public void testGSet() {
		Main.runChecker(Examples.DEFAULT_CONFIG, Examples.GSET);
	}

	@Test
	public void testSimpleCounter() {
		Main.runChecker(Examples.STATEFUL_CONFIG, Examples.MULTICLASS_COUNTER);
	}
}
