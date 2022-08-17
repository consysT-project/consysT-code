package de.tuda.stg.consys.bench

trait BenchmarkRunnable {

	/** Sets up the benchmark before measuring iterations. This includes, e.g., creating data structures. */
	def setup() : Unit

	/** A single iteration to be measured. The iteration is repeatedly executed  */
	def operations : BenchmarkOperations

	/** Finishes the iterations. This is measured by the run time measure as well. */
	def closeOperations() : Unit = { }

	/** Cleans up all data structures after the measurement. This is not measured. */
	def cleanup() : Unit

}
