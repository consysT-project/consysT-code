/* sbt build is not working (yet?) */

/*
name := "consistency-types"

version := "0.1"

scalaVersion := "2.12.6"

val checkerframeworkVersion = "2.5.2"
val javaVersion = "1.8"
val cassandraVersion = "3.5.1"

lazy val commonSettings = Seq(
  organization := "de.tu-darmstadt.rpt.consistency",
  version := "1.0.0",
  scalaVersion := "2.12.2"
)


lazy val consistencyChecker = (project in file("consistency-checker")) 
	.settings(
		commonSettings,
		name := "consistency-checker",
		libraryDependencies ++= Seq(
			"org.checkerframework" % "checker-qual" % checkerframeworkVersion,
			"org.checkerframework" % "checker" % checkerframeworkVersion
		),
		javacOptions ++= Seq("-source", javaVersion , "-target", javaVersion)
	)

lazy val consistencyStore = (project in file("consistency-store"))
	.dependsOn(consistencyChecker)
	.settings(
		commonSettings,
		name := "consistency-store",
		libraryDependencies ++= Seq(
			"com.datastax.cassandra" % "cassandra-driver-core" % cassandraVersion,
        	"com.datastax.cassandra" % "cassandra-driver-mapping" % cassandraVersion,
        	"com.datastax.cassandra" % "cassandra-driver-extras" % cassandraVersion,
        	"org.cassandraunit" % "cassandra-unit" % "3.3.0.2"
		),
		javacOptions ++= Seq("-source", javaVersion , "-target", javaVersion)
	)

lazy val storeIntegrationDemo = (project in file("store-integration-demo"))
	.dependsOn(consistencyStore)
	.settings(
		commonSettings,
		name := "store-integration-demo",
		libraryDependencies ++= Seq(
			"com.datastax.cassandra" % "cassandra-driver-core" % cassandraVersion,
        	"org.cassandraunit" % "cassandra-unit" % "3.3.0.2"
		),
		javacOptions ++= Seq("-source", javaVersion , "-target", javaVersion)
	)
*/