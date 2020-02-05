
ThisBuild / version      := "0.1.0-SNAPSHOT"
ThisBuild / organization := "ch.lara.epfl"
ThisBuild / scalaVersion := "2.12.9"

lazy val root = project
  .in(file("."))
  .enablePlugins(StainlessPlugin)
  .settings(
    name := "verifythis2020",
    stainlessEnabled := true,
    Compile / run / mainClass := Some("pgp.Main"),
  )

