resolvers ++= Seq(
  Resolver.bintrayRepo("epfl-lara", "princess"),
  Resolver.bintrayIvyRepo("epfl-lara", "sbt-plugins"),
)

val StainlessVersion = "0.6.2"

addSbtPlugin("ch.epfl.lara" % "sbt-stainless" % StainlessVersion)

