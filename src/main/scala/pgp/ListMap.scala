package pgp

import stainless.lang._
import stainless.collection._
import stainless.annotation._

case class ListMap[A, B](toList: List[(A, B)]) {
  def isEmpty: Boolean = toList.isEmpty

  def head: (A, B) = {
    require(!isEmpty)
    toList.head
  }

  def tail: ListMap[A, B] = {
    require(!isEmpty)
    ListMap(toList.tail)
  }

  def contains(key: A): Boolean = {
    get(key).isDefined
  }

  def get(key: A): Option[B] = {
    toList.find(_._1 == key).map(_._2)
  }

  def apply(key: A): B = {
    require(contains(key))
    get(key).get
  }

  def +(keyValue: (A, B)): ListMap[A, B] = {
    ListMap(keyValue :: toList)
  }

  def ++(keyValues: List[(A, B)]): ListMap[A, B] = {
    decreases(keyValues)
    keyValues match {
      case Nil()                => this
      case Cons(keyValue, rest) => (this + keyValue) ++ rest
    }
  }

  def -(key: A): ListMap[A, B] = {
    if (contains(key)) {
      ListMap(toList.filter(_._1 != key))
    } else {
      this
    }
  }

  def --(keys: List[A]): ListMap[A, B] = keys match {
    case Nil()           => this
    case Cons(key, rest) => (this - key) -- rest
  }

  def forall(p: (A, B) => Boolean): Boolean = {
    toList.forall { case (a, b) => p(a, b) }
  }
}

object ListMap {
  def empty[A, B]: ListMap[A, B] = ListMap(List.empty[(A, B)])

  object lemmas {
    def listFilterValidProp[A](@induct l: List[A], p: A => Boolean, f: A => Boolean): Unit = {
      require(l.forall(p))

    }.ensuring(_ => l.filter(f).forall(p))

    def listAppendValidProp[A](l: List[A], @induct as: List[A], p: A => Boolean): Unit = {
      require(l.forall(p) && as.forall(p))

    }.ensuring(_ => (as ++ l).forall(p))

    @opaque
    def insertAllValidProp[A, B](lm: ListMap[A, B], kvs: List[(A, B)], p: (A, B) => Boolean): Unit = {
      require(lm.forall(p) && kvs.forall { case (a, b) => p(a, b) })
      decreases(kvs)

      if (!kvs.isEmpty)
        insertAllValidProp(lm + kvs.head, kvs.tail, p)

    }.ensuring(_ => (lm ++ kvs).forall(p))

    @opaque
    def getForall[A, B](lm: ListMap[A, B], k: A, p: (A, B) => Boolean): Unit = {
      require(lm.forall(p) && lm.contains(k))
      decreases(lm.toList.size)

      if (!lm.isEmpty && lm.toList.head._1 != k)
        getForall(lm.tail, k, p)

    }.ensuring(_ => p(k, lm(k)))
  }
}

