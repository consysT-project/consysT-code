package de.tuda.stg.consys.bench

import java.io.PrintWriter
import java.nio.file.{Path, Paths}

import de.tuda.stg.consys.objects.Address

/**
 * Created on 29.10.19.
 *
 * @author Mirko Köhler
 */
class ConfigFileGenerator(
	val hosts : Seq[Address],
	val warmupIterations : Int,
	val measureIterations : Int,
	val outputFile : Path
) {

	private def generateConfigForHost(hostId : Int) : String = {
		val hostAddress = hosts(hostId)
		val otherReplicas = hosts.filter(addr => addr != hostAddress)

		s"""consys {
			 |    bench {
			 |        hostname = "$hostAddress"
			 |        processId = $hostId
			 |        otherReplicas = ${otherReplicas.mkString("[\"", "\",\"", "\"]")}
			 |
			 |        warmupIterations = $warmupIterations
			 |        measureIterations = $measureIterations
			 |
			 |        outputFile = "${outputFile.normalize()}"
			 |    }		 |
			 |}
			 |""".stripMargin
	}

	def create(resourcePath : Path) : Unit = {
		for (i <- hosts.indices) {
			var writer : PrintWriter = null
			try {
				writer = new PrintWriter(resourcePath.resolve(s"bench$i.conf").toFile)
				writer.println(generateConfigForHost(i))
			} finally {
				writer.close()
			}
		}
	}

}

object ConfigFileGenerator {

	def main(args : Array[String]) : Unit = {
		if (args.length < 5) {
			println("Wrong usage. Expected at least 5 parameters.")
			println("Usage: configOutputPath benchmarkOutputPath warmupIterations measureIterations hosts...")
			System.exit(1)
		}

		val resourcePath = Paths.get(args(0))
		val outputFile = Paths.get(args(1))
		val warmupIterations = args(2).toInt
		val measureIterations = args(3).toInt
		val hosts = args.drop(4).map(addrString => Address.parse(addrString))


		new ConfigFileGenerator(hosts, warmupIterations, measureIterations, outputFile)
			.create(resourcePath)
	}

}
