package pgp

import stainless.lang._
import stainless.collection._
import stainless.annotation._

import ListMap.lemmas._

case class Server(
  sendNotif     : (Identity, EMail) => Unit,
  var keys      : ListMap[Fingerprint, Key]                     = ListMap.empty,
  var uploaded  : ListMap[Token,       Fingerprint]             = ListMap.empty,
  var pending   : ListMap[Token,       (Fingerprint, Identity)] = ListMap.empty,
  var confirmed : ListMap[Identity,    Fingerprint]             = ListMap.empty,
  var managed   : ListMap[Token,       Fingerprint]             = ListMap.empty,
) {

  /** Invariant:
   *  - A key is valid if its fingerprint is registered in keys
   */
  def inv_keys: Boolean = {
    keys.forall(validKey)
  }

  def validKey(fingerprint: Fingerprint, key: Key): Boolean = {
    key.fingerprint == fingerprint
  }

  /** Invariant:
    * - All keys must be registered via the correct fingerprint
    * - Upload tokens must be for valid keys
    */
  def inv_uploaded: Boolean = {
    uploaded.forall(validUploaded)
  }

  def validUploaded(token: Token, fingerprint: Fingerprint): Boolean = {
    keys.contains(fingerprint)
  }

  /** Invariant:
    * - Pending validations must be for valid keys
    * - Pending validations must be for identity addresses associated for the respective key
    */
  def inv_pending: Boolean = {
    pending.forall(validPending)
  }

  def validPending(token: Token, value: (Fingerprint, Identity)): Boolean = {
    val (fingerprint, identity) = value

    keys.contains(fingerprint) && {
      val key = keys(fingerprint)
      key.identities.contains(identity)
    }
  }

  /** Invariant:
    * - Confirmed identity addresses must be for valid keys
    * - Confirmed identity must be valid for the associated key
    */
  def inv_confirmed: Boolean = {
    confirmed.forall(validConfirmed)
  }

  def validConfirmed(identity: Identity, fingerprint: Fingerprint): Boolean = {
    keys.contains(fingerprint) && {
      val key = keys(fingerprint)
      key.identities.contains(identity)
    }
  }

  /** Invariant:
    * - Management tokens must be for valid keys
    */
  def inv_managed: Boolean = {
    managed.forall(validManaged)
  }

  def validManaged(token: Token, fingerprint: Fingerprint): Boolean = {
    keys.contains(fingerprint)
  }

  /** The whole invariant */
  def invariant: Boolean =
    inv_keys && inv_uploaded && inv_pending && inv_confirmed && inv_managed

  /**
   * Look up a key by its (unique) fingerprint.
   *
   */
  def byFingerprint(fingerprint: Fingerprint): Option[Key] = {
    keys.get(fingerprint)
  }

  /**
   * Loop up keys by identity.
   *
   * Note that the key identity is not assumed to be unique.
   */
  def byKeyId(keyId: KeyId): List[Key] = {
    for ((fingerprint, key) <- keys.toList if key.keyId == keyId)
      yield key
  }

  @extern @pure
  private def notif(identity: Identity, email: EMail): Unit = {
    sendNotif(identity, email)
  }

  /**
   * Yields all identities that belong to a certain key and have been confirmed by email
   */
  private def filtered(key: Key): Key = {
    def confirmedByFingerprint(key: Key) = {
      for ((ident, fingerprint) <- confirmed.toList if key.fingerprint == fingerprint)
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
      fingerprint <- confirmed.get(identity)
      key = keys.get(fingerprint)
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
  def upload(key: Key): Token = {
    val fingerprint = key.fingerprint
    if (keys.contains(fingerprint)) {
      assert(keys(fingerprint) == key)
    }

    val token = Token.unique

    assert(validKey(fingerprint, key))
    keys += (fingerprint -> key)       // Affected invariant: inv_keys

    assert(validUploaded(token, fingerprint))
    uploaded += (token -> fingerprint) // Affected invariant: inv_uploaded

    token
  }

  def requestVerifyLemma1(@induct l: List[Identity], fingerprint: Fingerprint): Unit = {
    require(keys.contains(fingerprint) && l.forall(keys(fingerprint).identities.contains))

  } ensuring { _ =>
    l.map { identity =>
      val token = Token.unique
      (token, EMail("verify", fingerprint, token), identity)
    }.forall {
      case (token, _, identity) =>
        validPending(token, (fingerprint, identity))
    }
  }

  def requestVerifyLemma2(l: List[(Token, EMail, Identity)], fingerprint: Fingerprint): Unit = {
    require(l.forall {
      case (token, _, identity) =>
        validPending(token, (fingerprint, identity))
    })
    decreases(l)

    if (!l.isEmpty) requestVerifyLemma2(l.tail, fingerprint)

  } ensuring { _ =>
    l.map { case (token, _, identity) =>
      token -> (fingerprint, identity)
    }.forall { case (k, v) => validPending(k, v) }
  }

  /**
   * Request to verify a set of identity addresses, given a token returned by upload.
   *
   * For each identity address that can be verified with this token,
   * create a unique token that can later be passed to verify.
   */
  def requestVerify(from: Token, identities: List[Identity]): Unit = {
    require(invariant)
    if (uploaded.contains(from)) {
      val fingerprint = uploaded(from)
      assert(inv_uploaded)
      getForall(uploaded, from, validUploaded)
      val key = keys(fingerprint)
      if (identities.content.subsetOf(key.identities.content)) {

        ListLemmas.subsetContains(identities, key.identities) // gives us:
        assert(identities.forall(key.identities.contains))

        val toTreat = identities.map { identity =>
          val token = Token.unique
          (Token.unique, EMail("verify", fingerprint, token), identity)
        }

        requestVerifyLemma1(identities, fingerprint) // gives us:
        assert(toTreat.forall { case (token, _, identity) =>
          validPending(token, (fingerprint, identity))
        })

        val newPending = toTreat.map { case (token, _, identity) =>
          token -> (fingerprint, identity)
        }

        requestVerifyLemma2(toTreat, fingerprint) // gives us:
        assert(newPending.forall { case (k, v) => validPending(k, v) })

        // This lemma ensures that inv_pending still holds after adding `newPending`

        assert(inv_pending)
        assert(pending.forall(validPending))
        insertAllValidProp(pending, newPending, validPending)
        assert((pending ++ newPending).forall(validPending))
        val oldPending = pending
        pending ++= newPending
        assert(pending == oldPending ++ newPending)
        assert((oldPending ++ newPending).forall(validPending))
        assert(pending.forall(validPending))

        assert(inv_pending)

      //   toAdd.map { case (_, email, identity) =>
      //     notif(identity, email)
      //   }
      }
    }
  }

  /**
   * Verify an identity address by a token received via identity.
   *
   * Note that we keep the mapping in uploaded to allow further verifications.
   */
  def verify(token: Token): Unit = {
    if (pending.contains(token)) {
      val (fingerprint, identity) = pending(token)

      pending -= token // Affected invariant: inv_pending

      assert(validConfirmed(identity, fingerprint))
      confirmed += (identity -> fingerprint) // Affected invariant: inv_confirmed
    }
  }

  // /**
  //  * Request a management token for a given confirmed identity.
  //  *
  //  * Note that this should be rate-limited.
  //  */
  // def requestManage(identity: Identity): Unit = {
  //   if (confirmed.contains(identity)) {
  //     val token = Token.unique

  //     val fingerprint = confirmed(identity)

  //     assert(validManaged(token, fingerprint))
  //     managed += (token -> fingerprint) // Affected invariant: inv_managed

  //     val email = EMail("manage", fingerprint, token)
  //     notif(identity, email)
  //   }
  // }

  // /**
  //  * Revoke confirmation of a set of identities given a management key.
  //  *
  //  * Only if all addresses match the respective key, they will be invalidated.
  //  */
  // def revoke(token: Token, identities: List[Identity]): Unit = {
  //   if (managed.contains(token)) {
  //     val fingerprint = managed(token)
  //     val key = keys(fingerprint)

  //     if (identities.content.subsetOf(key.identities.content)) {
  //       confirmed --= identities // Affected invariant: inv_confirmed
  //     }
  //   }
  // }
}

