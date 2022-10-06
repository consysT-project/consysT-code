package de.tuda.stg.consys.bench

import java.util.concurrent.TimeUnit
import scala.concurrent.duration.FiniteDuration

object BenchmarkUtils {

	def printProgress(iteration : Int) : Unit = {
		System.out.print(if (iteration % 100 == 0) iteration
		else ".")
	}

	def printDone() : Unit = {
		System.out.println(" DONE")
	}

	def printTest() : Unit = {
		System.out.println(" TEST")
	}

	/** Converts Java's durations to Scala' durations. */
	def convertDuration(duration : java.time.Duration) : FiniteDuration = {
		FiniteDuration(duration.toNanos, TimeUnit.NANOSECONDS)
	}

}
