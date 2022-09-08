package de.tuda.stg.consys.bench

import java.util.function.Consumer

trait BenchmarkOperations {
	def getOperation : Runnable
}

object BenchmarkOperations {

	def withZipfDistribution(operations : Array[Runnable]) : BenchmarkOperations =
		new ProbabilityBenchmarkOperations(operations.toSeq, ProbabilityDistribution.zipf)

	def withUniformDistribution(operations : Array[Runnable]) : BenchmarkOperations =
		new ProbabilityBenchmarkOperations(operations.toSeq, ProbabilityDistribution.uniform)

	private class ProbabilityBenchmarkOperations(val operations : Seq[Runnable], val distFactory : Int => ProbabilityDistribution) extends BenchmarkOperations {
		val dist = distFactory(operations.length)
		override def getOperation : Runnable = operations(dist.randomRank())
	}
}
