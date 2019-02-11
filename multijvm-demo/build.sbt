import com.typesafe.sbt.SbtMultiJvm.multiJvmSettings
import com.typesafe.sbt.SbtMultiJvm.MultiJvmKeys.MultiJvm

val akkaVersion = "2.5.18"

val `akka-sample-multi-node-scala` = project
  .in(file("."))
  .settings(multiJvmSettings: _*)
  .settings(
    organization := "de.tu-darmstadt.consistency-types",
    scalaVersion := "2.12.8",
    resolvers += Resolver.mavenLocal,
    libraryDependencies ++= Seq(
      "com.typesafe.akka" %% "akka-actor" % akkaVersion,
      "com.typesafe.akka" %% "akka-remote" % akkaVersion,
      "com.typesafe.akka" %% "akka-multi-node-testkit" % akkaVersion,
      "de.tu-darmstadt.consistency-types" % "replicated-objects" % "1.0.0" cross false,
      "org.scalatest" %% "scalatest" % "3.0.5" % Test),
    // disable parallel tests
    parallelExecution in Test := false
  )
  .configs (MultiJvm)
