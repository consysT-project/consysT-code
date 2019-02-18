import com.typesafe.sbt.SbtMultiJvm.multiJvmSettings
import com.typesafe.sbt.SbtMultiJvm.MultiJvmKeys.MultiJvm

val akkaVersion = "2.5.21"

organization := "de.tu-darmstadt.consistency-types"

name := "replicated-objects-demo"

version := "1.0.0"

scalaVersion := "2.12.8"

//resolvers += Resolver.mavenLocal

MultiJvm / unmanagedJars +=
  file("/home/mirko/.m2/repository/de/tu-darmstadt/consistency-types/replicated-objects/1.0.0/replicated-objects-1.0.0.jar")

libraryDependencies ++= Seq(
  "com.typesafe.akka" %% "akka-actor" % akkaVersion,
  "com.typesafe.akka" %% "akka-remote" % akkaVersion,
  "com.typesafe.akka" %% "akka-multi-node-testkit" % akkaVersion,
  "com.typesafe.akka" %% "akka-persistence" % akkaVersion,
//  "de.tu-darmstadt.consistency-types" % "replicated-objects" % "1.0.0",
  "org.scalatest" %% "scalatest" % "3.0.5" % Test)

// disable parallel tests
parallelExecution in Test := false

val `replicated-objects-demo` = project
  .in(file("."))
  .settings(multiJvmSettings: _*)
  .configs (MultiJvm)
