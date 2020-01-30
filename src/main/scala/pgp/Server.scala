package pgp

import stainless.lang._
import stainless.collection._
import stainless.annotation._

case class Server(
  notify: (Identity, EMail) => Unit,
  var keys      : List[(Fingerprint, Key)]                     = List.empty,
  var uploaded  : List[(Token,       Fingerprint)]             = List.empty,
  var pending   : List[(Token,       (Fingerprint, Identity))] = List.empty,
  var confirmed : List[(Identity,    Fingerprint)]             = List.empty,
  var managed   : List[(Token,       Fingerprint)]             = List.empty,
) {

  /**
   * Consistency invariants on the state space:
   *
   * - A key is valid if its fingerprint is registered in keys
   *
   * - All keys must be registered via the correct fingerprint
   * - Upload tokens must be for valid keys
   *
   * - Pending validations must be for valid keys
   * - Pending validations must be for identity addresses associated for the respective key
   *
   * - Confirmed identity addresses must be for valid keys
   * - Confirmed identity must be valid for the associated key
   *
   * - Management tokens must be for valid keys
   */
  def invariants(): Boolean = {
    true

    // val inv1 = for ((fingerprint, key) <- keys) yield {
    //   key.fingerprint == fingerprint
    // }

    // val inv2 = for ((token, fingerprint) <- uploaded) yield {
    //   keys contains fingerprint
    // }

    // val inv3 = for ((token, (fingerprint, identity)) <- pending) yield {
    //   keys contains fingerprint && {
    //     val key = keys(fingerprint)
    //     assert(key.identities contains identity)
    //   }
    // }

    // val inv4 = for ((identity, fingerprint) <- confirmed) yield {
    //   keys contains fingerprint && {
    //     val key = keys(fingerprint)
    //     key.identities contains identity
    //   }
    // }

    // val inv5 = for ((token, fingerprint) <- managed) yield {
    //   keys contains fingerprint
    // }

    // inv1 && inv2 && inv3 && inv4 && inv5
  }

  /**
   * Look up a key by its (unique) fingerprint.
   *
   */
  def byFingerprint(fingerprint: Fingerprint): Option[Key] = {
    keys.find(_._1 == fingerprint).map(_._2)
  }

  /**
   * Loop up keys by identity.
   *
   * Note that the key identity is not assumed to be unique.
   */
  def byKeyId(keyId: KeyId): List[Key] = {
    for ((fingerprint, key) <- keys if key.keyId == keyId)
      yield key
  }

  /**
   * Yields all identities that belong to a certain key and have been confirmed by email
   */
  private def filtered(key: Key): Key = {
    def confirmedByFingerprint(key: Key) = {
      for ((ident, fingerprint) <- confirmed if key.fingerprint == fingerprint)
        yield ident
    }

    key.restrictedTo(confirmedByFingerprint(key))
  }


  /**
   * Look up the (unique) key associated with an identity address.
   *
   * Note that this key should be in keys, too.
   */
  def byEmail(identity: Identity): Option[Key] = {
    for {
      fingerprint <- confirmed.find(_._1 == identity).map(_._2)
      key = keys.find(_._1 == fingerprint).map(_._2)
    } yield filtered(key.get)
  }

  /**
   * Upload a new key to the server.
   *
   * The returned token must be used to requestVerify,
   * to prevent spamming users with such requests.
   *
   * Note the check for fingerprint collisions.
   */
  // def upload(key: Key): Token = {
  //   val fingerprint = key.fingerprint
  //   if (keys contains fingerprint)
  //     assert(keys(fingerprint) == key)

  //   val token = Token.unique
  //   keys += (fingerprint -> key)
  //   uploaded += (token -> fingerprint)
  //   token
  // }

  /**
   * Request to verify a set of identity addresses, given a token returned by upload.
   *
   * For each identity address that can be verified with this token,
   * create a unique token that can later be passed to verify.
   */
  // def requestVerify(from: Token, identities: Set[Identity]): Unit =  {
  //   if (uploaded contains from) {
  //     val fingerprint = uploaded(from)
  //     val key = keys(fingerprint)
  //     if (identities subsetOf key.identities) {
  //       for (identity <- identities) {
  //         val token = Token.unique
  //         pending += (token -> (fingerprint, identity))
  //         val email = EMail("verify", fingerprint, token)
  //         notify(identity, email)
  //       }
  //     }
  //   }
  // }

  /**
   * Verify an identity address by a token received via identity.
   *
   * Note that we keep the mapping in uploaded to allow further verifications.
   */
  // def verify(token: Token): Unit = {
  //   if (pending contains token) {
  //     val (fingerprint, identity) = pending(token)
  //     pending -= token
  //     confirmed += (identity -> fingerprint)
  //   }
  // }

  /**
   * Request a management token for a given confirmed identity.
   *
   * Note that this should be rate-limited.
   */
  // def requestManage(identity: Identity): Unit = {
  //   if (confirmed contains identity) {
  //     val token = Token.unique
  //     val fingerprint = confirmed(identity)
  //     managed += (token -> fingerprint)
  //     val email = EMail("manage", fingerprint, token)
  //     notify(identity, email)
  //   }
  // }

  /**
   * Revoke confirmation of a set of identities given a management key.
   *
   * Only if all addresses match the respective key, they will be invalidated.
   */
  // def revoke(token: Token, identities: Set[Identity]): Unit = {
  //   if (managed contains token) {
  //     val fingerprint = managed(token)
  //     val key = keys(fingerprint)
  //     if (identities subsetOf key.identities) {
  //       confirmed --= identities
  //     }
  //   }
  // }
}

