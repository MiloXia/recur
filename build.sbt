name := "recur"

version := "1.0.0"

scalaVersion := "2.12.1"

scalacOptions := Seq("-unchecked", "-deprecation", "-encoding", "utf8")

resolvers += "main" at "http://repo1.maven.org/maven2"
resolvers += Resolver.mavenLocal
resolvers ++= Seq(
  Resolver.sonatypeRepo("releases"),
  Resolver.sonatypeRepo("snapshots")
)

run <<= run in Compile in core

lazy val macros = (project in file("macros")).settings(
  scalaVersion := "2.12.1",
//  scalaBinaryVersion := "2.12",
  libraryDependencies += "org.scala-lang" % "scala-reflect" % "2.12.1",
  libraryDependencies += "com.chuusai" % "shapeless_2.12" % "2.3.2",
  addCompilerPlugin("org.spire-math" % "kind-projector_2.12" % "0.9.3")
)

lazy val core = (project in file("core")).settings(
  scalaVersion := "2.12.1",
//  scalaBinaryVersion := "2.12",
  addCompilerPlugin("org.spire-math" %% "kind-projector" % "0.9.3")
) dependsOn macros


