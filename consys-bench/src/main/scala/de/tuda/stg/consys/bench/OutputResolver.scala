package de.tuda.stg.consys.bench

import de.tuda.stg.consys.logging.Logger
import java.io.{IOException, OutputStream, PrintWriter}
import java.nio.file.{Files, Path, Paths}
import java.text.SimpleDateFormat
import java.util.Date

trait OutputResolver {
	def latencyWriter(processId : Int) : PrintWriter
	def runtimeWriter(processId : Int) : PrintWriter
}

object OutputResolver {

	class ConsoleOutputResolver extends OutputResolver {
		override def latencyWriter(processId : Int) : PrintWriter = {
			new PrintWriter(OutputStream.nullOutputStream() /* Logger.infoWriter */, false)
		}

		override def runtimeWriter(processId : Int) : PrintWriter = {
			new PrintWriter(OutputStream.nullOutputStream() /* Logger.infoWriter */, false)
		}
	}


	class DateTimeOutputResolver(className : String, basePath : String) extends OutputResolver {
		private val sdf = new SimpleDateFormat("YY-MM-dd_kk-mm-ss")
 		private val outputDir = Paths.get("benchmark", "measurements", className, basePath, sdf.format(new Date))

		//Initialize output dir
		try {
			Files.createDirectories(outputDir)
		} catch {
			case e : IOException =>
				throw new IllegalStateException("cannot instantiate output file", e)
		}

		override def latencyWriter(processId : Int) : PrintWriter = {
			val latencyPath = outputDir.resolve("proc" + processId + ".csv")
			try {
				Files.deleteIfExists(latencyPath)
				Files.createFile(latencyPath)
			} catch {
				case e : IOException =>
					throw new IllegalStateException("cannot instantiate output file", e)
			}
			new PrintWriter(latencyPath.toFile)
		}

		override def runtimeWriter(processId : Int) : PrintWriter = {
			val runtimePath = outputDir.resolve("runtime" + processId + ".csv")
			try {
				Files.deleteIfExists(runtimePath)
				Files.createFile(runtimePath)
			} catch {
				case e : IOException =>
					throw new IllegalStateException("cannot instantiate output file", e)
			}
			new PrintWriter(runtimePath.toFile)
		}
	}


	class SimpleOutputResolver(className : String, basePath : String) extends OutputResolver {
		private val outputDir = Paths.get("benchmark", "measurements", className, basePath)
		//Initialize output dir
		try {
			Files.createDirectories(outputDir)
		} catch {
			case e : IOException =>
				throw new IllegalStateException("cannot instantiate output file", e)
		}

		override def latencyWriter(processId : Int) : PrintWriter = {
			val latencyPath = outputDir.resolve("proc" + processId + ".csv")
			try {
				Files.deleteIfExists(latencyPath)
				Files.createFile(latencyPath)
			} catch {
				case e : IOException =>
					throw new IllegalStateException("cannot instantiate output file", e)
			}
			println(s"latency file = $latencyPath")
			new PrintWriter(latencyPath.toFile)
		}

		override def runtimeWriter(processId : Int) : PrintWriter = {
			val runtimePath = outputDir.resolve("runtime" + processId + ".csv")
			try {
				Files.deleteIfExists(runtimePath)
				Files.createFile(runtimePath)
			} catch {
				case e : IOException =>
					throw new IllegalStateException("cannot instantiate output file", e)
			}
			println(s"runtime file = $runtimePath")
			new PrintWriter(runtimePath.toFile)
		}
	}

}


