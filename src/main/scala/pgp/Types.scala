package pgp

import java.util.UUID

import stainless.lang._
import stainless.collection._
import stainless.annotation._

import stainless.util.Random

sealed trait KeyId
case class KeyIdImpl(id: String) extends KeyId

object KeyId {
  @extern
  def random: KeyId = KeyIdImpl(UUID.randomUUID().toString)
}

sealed trait Fingerprint
case class FingerprintImpl(fingerprint: String) extends Fingerprint

object Fingerprint {
  @extern
  def random: Fingerprint = FingerprintImpl(UUID.randomUUID().toString)
}

case class Identity(email: String)

sealed trait Key {
  def keyId: KeyId
  def fingerprint: Fingerprint
  def identities: List[Identity]
  def restrictedTo(ids: List[Identity]): Key = {
    require(ids.content subsetOf identities.content)
    (??? : Key)
  }
}

case class PGPKey(
  keyId: KeyId,
  fingerprint: Fingerprint,
  identities: List[Identity]
) extends Key {
  override def restrictedTo(ids: List[Identity]): Key = {
    require(ids.content subsetOf identities.content)
    PGPKey(keyId, fingerprint, ids)
  }
}

object Key {
  def random(ids: List[Identity]): Key =
    PGPKey(
      keyId = KeyId.random,
      fingerprint = Fingerprint.random,
      identities = ids
    )
}

case class EMail(
  message: String,
  fingerprint: Fingerprint,
  token: Token
)

case class Token(
  @extern @pure
  uuid: UUID
)

object Token {

  @extern
  def unique: Token = Token(UUID.randomUUID)
}

