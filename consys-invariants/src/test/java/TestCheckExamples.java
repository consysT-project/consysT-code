import de.tuda.stg.consys.invariants.Main;
import de.tuda.stg.consys.invariants.subset.ProgramConfig;
import org.junit.Test;

import java.nio.file.Path;
import java.nio.file.Paths;


public class TestCheckExamples {
	/* INFO: to run the tests in IntelliJ, change the working directory in the run configurations to the consys-code folder. */

	public static final ProgramConfig defaultConfig = new ProgramConfig(
			false
	);

	public static final ProgramConfig statefulConfig = new ProgramConfig(
			true
	);

	@Test
	public void testBankAccountCRDT() {
		Main.runChecker(defaultConfig, new Path[] {
				Paths.get("consys-invariants", "InvariantExamples", "BankAccountCRDT", "BankAccountCRDT.java")
		});
	}

	@Test
	public void testGSetCRDT() {
		Main.runChecker(defaultConfig, new Path[] {
				Paths.get("consys-invariants", "InvariantExamples", "GSetCRDT", "GSetCRDT.java")
		});
	}

	@Test
	public void testSimpleCounter() {
		Main.runChecker(statefulConfig, new Path[] {
				Paths.get("consys-invariants","InvariantExamples","MultiClassTestExample","SimpleNumber.java"),
				Paths.get("consys-invariants","InvariantExamples","MultiClassTestExample","SimpleCounter.java")
		});
	}
}
