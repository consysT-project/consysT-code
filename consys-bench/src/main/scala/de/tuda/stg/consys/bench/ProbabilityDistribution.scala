package de.tuda.stg.consys.bench

import scala.::
import scala.util.Random

trait ProbabilityDistribution {
	def numberOfElements : Int
	def randomRank() : Int
}

object ProbabilityDistribution {

	def uniform(numberOfElements : Int) : ProbabilityDistribution = new UniformDistribution(numberOfElements)
	def zipf(numberOfElements : Int) : ProbabilityDistribution = new ZipfDistribution(numberOfElements)

	private class UniformDistribution(override val numberOfElements : Int) extends ProbabilityDistribution {
		private val rand = new Random()
		override def randomRank() : Int = rand.nextInt(numberOfElements)
	}

	private class ZipfDistribution(override val numberOfElements : Int, val exponent : Double = 1.0) extends ProbabilityDistribution {
		private val zipf = new org.apache.commons.math3.distribution.ZipfDistribution(numberOfElements, exponent)
		def randomRank() : Int = zipf.sample() - 1
	}

	def main(args : Array[String]) : Unit = {
		val dist = new ZipfDistribution(6)
		for(n <- 1 to 20)	println(dist.randomRank())
	}
}