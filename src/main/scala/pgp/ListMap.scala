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

  def forall(p: ((A, B)) => Boolean): Boolean = {
    toList.forall(p)
  }
}

object ListMap {
  def empty[A, B]: ListMap[A, B] = ListMap(List.empty[(A, B)])
}

