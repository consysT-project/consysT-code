import de.tuda.stg.consys.invariants.Main;
import org.junit.Test;

import java.nio.file.Path;
import java.nio.file.Paths;


public class TestCheckExamples {
	/* INFO: to run the tests in IntelliJ, change the working directory in the run configurations to the consys-code folder. */

	@Test
	public void testBankAccountCRDT() {
		Main.runChecker(new Path[] {
				Paths.get("consys-invariants", "InvariantExamples", "BankAccountCRDT", "BankAccountCRDT.java")
		});
	}

	@Test
	public void testSimpleCounter() {
		Main.runChecker(new Path[] {
				Paths.get("consys-invariants","InvariantExamples","MultiClassTestExample","SimpleNumber.java"),
				Paths.get("consys-invariants","InvariantExamples","MultiClassTestExample","SimpleCounter.java")
		});
	}
}
