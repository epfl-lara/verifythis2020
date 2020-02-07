package pgp

import stainless.collection._
import stainless.annotation._

object ListLemmas {
  def mapPred[A,B](@induct l: List[A], f: A => B, p: B => Boolean): Unit = {
    require(l.forall(a => p(f(a))))

  }.ensuring(_ => l.map(f).forall(p))

  def subsetContains[T](@induct l1: List[T], l2: List[T]): Unit = {
    require(l1.content.subsetOf(l2.content))

  }.ensuring(_ => l1.forall(l2.contains))
}
