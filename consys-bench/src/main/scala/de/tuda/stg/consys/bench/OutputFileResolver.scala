package de.tuda.stg.consys.bench

import java.io.IOException
import java.nio.file.{Files, Path, Paths}
import java.text.SimpleDateFormat
import java.util.Date

trait OutputFileResolver {
	def resolveLatencyFile(processId : Int) : Path
	def resolveRuntimeFile(processId : Int) : Path
}

object OutputFileResolver {

	class DateTimeOutputResolver(className : String, basePath : String) extends OutputFileResolver {
		private val sdf = new SimpleDateFormat("YY-MM-dd_kk-mm-ss")
 		private val outputDir = Paths.get("results", className, basePath, sdf.format(new Date))

		//Initialize output dir
		try {
			Files.createDirectories(outputDir)
		} catch {
			case e : IOException =>
				throw new IllegalStateException("cannot instantiate output file", e)
		}

		override def resolveLatencyFile(processId : Int) : Path = {
			val latencyFile = outputDir.resolve("proc" + processId + ".csv")
			try {
				Files.deleteIfExists(latencyFile)
				Files.createFile(latencyFile)
			} catch {
				case e : IOException =>
					throw new IllegalStateException("cannot instantiate output file", e)
			}
			latencyFile
		}

		override def resolveRuntimeFile(processId : Int) : Path = {
			val runtimeFile = outputDir.resolve("runtime" + processId + ".csv")
			try {
				Files.deleteIfExists(runtimeFile)
				Files.createFile(runtimeFile)
			} catch {
				case e : IOException =>
					throw new IllegalStateException("cannot instantiate output file", e)
			}
			runtimeFile
		}
	}


	class SimpleOutputResolver(className : String, basePath : String) extends OutputFileResolver {
		private val outputDir = Paths.get("results", className, basePath)
		//Initialize output dir
		try {
			Files.createDirectories(outputDir)
		} catch {
			case e : IOException =>
				throw new IllegalStateException("cannot instantiate output file", e)
		}

		override def resolveLatencyFile(processId : Int) : Path = {
			val latencyFile = outputDir.resolve("proc" + processId + ".csv")
			try {
				Files.deleteIfExists(latencyFile)
				Files.createFile(latencyFile)
			} catch {
				case e : IOException =>
					throw new IllegalStateException("cannot instantiate output file", e)
			}
			println(s"latency file = $latencyFile")
			latencyFile
		}

		override def resolveRuntimeFile(processId : Int) : Path = {
			val runtimeFile = outputDir.resolve("runtime" + processId + ".csv")
			try {
				Files.deleteIfExists(runtimeFile)
				Files.createFile(runtimeFile)
			} catch {
				case e : IOException =>
					throw new IllegalStateException("cannot instantiate output file", e)
			}
			println(s"runtime file = $runtimeFile")
			runtimeFile
		}
	}

}


