name := "multi-jvm-test"

version := "0.1"

scalaVersion := "2.12.8"

lazy val root = (project in file("."))
	.enablePlugins(MultiJvmPlugin)
	.configs(MultiJvm)

jvmOptions in MultiJvm := Seq("-Xmx256M")

libraryDependencies ++= Seq(
	"com.typesafe.akka" %% "akka-actor" % "2.5.20",
	"com.typesafe.akka" %% "akka-testkit" % "2.5.20" % Test,
	"com.typesafe.akka" %% "akka-cluster" % "2.5.20"
)
