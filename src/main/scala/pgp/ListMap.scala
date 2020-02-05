package pgp

import stainless.lang._
import stainless.collection._
import stainless.annotation._

case class ListMap[A, B](toList: List[(A, B)]) {
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
    val key = keyValue._1
    if (contains(key)) {
      ListMap(keyValue :: toList.filter(_._1 != key))
    } else {
      ListMap(keyValue :: toList)
    }
  }

  def ++(keyValues: List[(A, B)]): ListMap[A, B] = keyValues match {
    case Nil()                => this
    case Cons(keyValue, rest) => (this + keyValue) ++ rest
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
    def listFilterValidProp[A](@induct l: List[A], p: A => Boolean, filter: A => Boolean): Boolean = {
      require(l.forall(p))
      val result = l.filter(filter)
      result.forall(p)
    }.holds

    def listInsertValidProp[A](l: List[A], a: A, p: A => Boolean): Boolean = {
      require(l.forall(p) && p(a))
      val result = Cons(a, l)
      result.forall(p)
    }.holds

    def listInsertAllValidProp[A](l: List[A], @induct as: List[A], p: A => Boolean): Boolean = {
      require(l.forall(p) && as.forall(p))
      val result = as ++ l
      result.forall(p)
    }.holds

    def insertValidProp[A, B](lm: ListMap[A, B], kv: (A, B), p: (A, B) => Boolean): Boolean = {
      require(lm.forall(p) && p(kv._1, kv._2))
      val result = lm + kv
      result.forall(p)
    }.holds

    def insertAllValidProp[A, B](lm: ListMap[A, B], @induct kvs: List[(A, B)], p: (A, B) => Boolean): Boolean = {
      require(lm.forall(p) && kvs.forall { case (a, b) => p(a, b) })
      val result = lm ++ kvs
      result.forall(p)
    }.holds
  }
}

