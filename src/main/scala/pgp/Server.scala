package pgp

import stainless.lang._
import stainless.collection._
import stainless.annotation._
import stainless.proof._

import ListMap.lemmas._
import ServerLemmas._
import ServerProperties._
import ListUtils._

case class Server(
  sendNotif     : (Identity, EMail) => Unit,
  var keys      : ListMap[Fingerprint, Key]                     = ListMap.empty,
  var uploaded  : ListMap[Token,       Fingerprint]             = ListMap.empty,
  var pending   : ListMap[Token,       (Fingerprint, Identity)] = ListMap.empty,
  var confirmed : ListMap[Identity,    Fingerprint]             = ListMap.empty,
  var managed   : ListMap[Token,       Fingerprint]             = ListMap.empty,
) {

  /** The server's invariant */
  def invariant: Boolean =
    invKeys(keys) &&
    invUploaded(keys, uploaded) &&
    invPending(keys, pending) &&
    invConfirmed(keys, confirmed) &&
    invManaged(keys, managed)

  /**
   * Look up a key by its (unique) fingerprint.
   *
   */
  def byFingerprint(fingerprint: Fingerprint): Option[Key] = {
    require(invariant)
    keys.get(fingerprint)
  }.ensuring(_ => invariant)

  /**
   * Loop up keys by identity.
   *
   * Note that the key identity is not assumed to be unique.
   */
  def byKeyId(keyId: KeyId): List[Key] = {
    require(invariant)
    for ((fingerprint, key) <- keys.toList if key.keyId == keyId)
      yield key
  }.ensuring(_ => invariant)

  @extern @pure
  private def notif(identity: Identity, email: EMail): Unit = {
    sendNotif(identity, email)
  }

  /**
   * Yields all identities that belong to a certain key and have been confirmed by email
   */
  private def filtered(fingerprint: Fingerprint): Key = {
    require(invariant && keys.contains(fingerprint))

    val key = keys(fingerprint)
    val identities = confirmed.keysOf(fingerprint)

    keysOfSound(confirmed, fingerprint) // gives us:
    identities.forall(id => confirmed.get(id) == Some(fingerprint))

    invConfirmedFiltered(keys, confirmed, fingerprint) // gives us:
    assert(identities.forall(identity => validConfirmed(keys)((identity, fingerprint))))

    filteredLemma1(identities, keys, fingerprint) // gives us:
    assert(identities.isEmpty || identities.forall(key.identities.contains))

    if (!identities.isEmpty) {
      forallContainsSubset(identities, key.identities) // gives us:
      check(identities.content subsetOf key.identities.content)
    } else {
      check(identities.content subsetOf key.identities.content)
    }

    key.restrictedTo(identities)
  }.ensuring(_ => invariant)


  /**
   * Look up the (unique) key associated with an identity address.
   *
   * Note that this key should be in keys, too.
   */
  def byEmail(identity: Identity): Option[Key] = {
    require(invariant)
    val fingerprintOpt = confirmed.get(identity)
    getForall(confirmed, validConfirmed(keys), identity)
    assert(fingerprintOpt.forall(fingerprint => validConfirmed(keys)((identity, fingerprint))))
    fingerprintOpt match {
      case None() => None[Key]()
      case Some(fingerprint) => Some[Key](filtered(fingerprint))
    }
  }.ensuring(_ => invariant)

  /**
   * Upload a new key to the server.
   *
   * The returned token must be used to requestVerify,
   * to prevent spamming users with such requests.
   *
   * Note the check for fingerprint collisions.
   */
  def upload(key: Key): Token = {
    require(invariant)

    val fingerprint = key.fingerprint
    if (keys.contains(fingerprint)) {
      Utils.assume(keys(fingerprint) == key)
    }

    val token = Token.unique

    val newKeys = keys + (fingerprint -> key)

    addValidProp(keys, fingerprintMatchKey, fingerprint, key) // gives us:
    assert(invKeys(newKeys))

    moreContainedKeys(keys, uploaded, fingerprint, key) // gives us:
    assert(invUploaded(newKeys, uploaded))

    invPendingMoreKeys(keys, pending, fingerprint, key) // gives us:
    assert(invPending(newKeys, pending))

    invConfirmedMoreKeys(keys, confirmed, fingerprint, key) // gives us:
    assert(invConfirmed(newKeys, confirmed))

    moreContainedKeys(keys, managed, fingerprint, key) // gives us:
    assert(invManaged(newKeys, managed))

    keys = newKeys

    assert(invKeys(keys))
    assert(invUploaded(keys, uploaded))
    assert(invPending(keys, pending))
    assert(invConfirmed(keys, confirmed))
    assert(invManaged(keys, managed))

    val newUploaded = uploaded + (token -> fingerprint)

    assert(uploaded.forall(containedFingerprint(keys)))
    addValidProp(uploaded, containedFingerprint(keys), token, fingerprint) // gives us:
    assert(newUploaded.forall(containedFingerprint(keys)))
    assert(invUploaded(keys, uploaded + (token -> fingerprint)))

    uploaded = newUploaded

    assert(invKeys(keys))
    assert(invUploaded(keys, uploaded))
    assert(invPending(keys, pending))
    assert(invConfirmed(keys, confirmed))
    assert(invManaged(keys, managed))

    token
  }.ensuring(_ => invariant)

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

      applyForall(uploaded, containedFingerprint(keys), from) // gives us:
      val key = keys(fingerprint)

      if (identities.content.subsetOf(key.identities.content)) {

        ListUtils.subsetContains(identities, key.identities) // gives us:
        assert(identities.forall(key.identities.contains))

        val toTreat = identities.map { identity =>
          val token = Token.unique
          (Token.unique, EMail("verify", fingerprint, token), identity)
        }

        requestVerifyLemma1(identities, keys, fingerprint) // gives us:
        assert(toTreat.forall { case (token, _, identity) =>
          validPending(keys)(token, (fingerprint, identity))
        })

        val toAdd = toTreat.map { case (token, _, identity) =>
          token -> (fingerprint, identity)
        }

        requestVerifyLemma2(toTreat, keys, fingerprint) // gives us:
        assert(toAdd.forall(validPending(keys)))

        val newPending = pending ++ toAdd

        insertAllValidProp(pending, toAdd, validPending(keys)) // gives us:
        assert(invPending(keys, newPending))

        pending = newPending

        toTreat.map { case (_, email, identity) =>
          notif(identity, email)
        }

        ()
      }
    }
  }.ensuring(_ => invariant)

  /**
   * Verify an identity address by a token received via identity.
   *
   * Note that we keep the mapping in uploaded to allow further verifications.
   */
  def verify(token: Token): Unit = {
    require(invariant)
    if (pending.contains(token)) {
      val (fingerprint, identity) = pending(token)
      val newPending = pending - token

      applyForall(pending, validPending(keys), token) // gives us:
      assert(validPending(keys)((token, (fingerprint, identity))))

      removeValidProp(pending, validPending(keys), token) // gives us:
      assert(invPending(keys, newPending))

      pending = newPending

      assert(invPending(keys, pending))

      val newConfirmed = confirmed + (identity -> fingerprint)

      assert(validConfirmed(keys)((identity, fingerprint)))

      addValidProp(confirmed, validConfirmed(keys), identity, fingerprint) // gives us:
      assert(invConfirmed(keys, newConfirmed))

      confirmed = newConfirmed

      assert(invConfirmed(keys, confirmed))
    }
  }.ensuring(_ => invariant)

  /**
   * Request a management token for a given confirmed identity.
   *
   * Note that this should be rate-limited.
   */
  def requestManage(identity: Identity): Unit = {
    require(invariant)
    if (confirmed.contains(identity)) {
      val token = Token.unique

      val fingerprint = confirmed(identity)

      applyForall(confirmed, validConfirmed(keys), identity)

      val newManaged = managed + (token -> fingerprint)

      addValidProp(managed, containedFingerprint(keys), token, fingerprint) // gives us:
      assert(invManaged(keys, newManaged))

      managed = newManaged

      val email = EMail("manage", fingerprint, token)
      notif(identity, email)
    }
  }.ensuring(_ => invariant)

  /**
   * Revoke confirmation of a set of identities given a management key.
   *
   * Only if all addresses match the respective key, they will be invalidated.
   */
  def revoke(token: Token, identities: List[Identity]): Unit = {
    require(invariant)
    if (managed.contains(token)) {
      val fingerprint = managed(token)

      applyForall(managed, containedFingerprint(keys), token) // gives us:
      val key = keys(fingerprint)


      if (identities.content.subsetOf(key.identities.content)) {
        val newConfirmed = confirmed -- identities

        removeAllValidProp(confirmed, identities, validConfirmed(keys)) // gives us:
        assert(invConfirmed(keys, newConfirmed))

        confirmed = newConfirmed

        assert(invConfirmed(keys, confirmed))
      }
    }
  }.ensuring(_ => invariant)
}


object ServerProperties {

  /** Invariant:
    *  - A key is valid if its fingerprint is registered in keys
    */
  def fingerprintMatchKey(fk: (Fingerprint, Key)): Boolean = {
    fk._2.fingerprint == fk._1
  }

  def invKeys(keys: ListMap[Fingerprint, Key]) = keys.forall(fingerprintMatchKey)


  /** Invariant:
    * - All keys must be registered via the correct fingerprint
    * - Upload tokens must be for valid keys
    */
  def containedFingerprint(keys: ListMap[Fingerprint, Key])(tf: (Token, Fingerprint)) = {
    keys.contains(tf._2)
  }

  def invUploaded(keys: ListMap[Fingerprint, Key], uploaded: ListMap[Token, Fingerprint]) =
    uploaded.forall(containedFingerprint(keys))


  /** Invariant:
    * - Pending validations must be for valid keys
    * - Pending validations must be for identity addresses associated for the respective key
    */
  def validPending(keys: ListMap[Fingerprint, Key])(tfi: (Token, (Fingerprint, Identity))): Boolean = {
    val (_, (fingerprint, identity)) = tfi
    keys.contains(fingerprint) && {
      val key = keys(fingerprint)
      key.identities.contains(identity)
    }
  }

  def invPending(keys: ListMap[Fingerprint, Key], pending: ListMap[Token, (Fingerprint, Identity)]) =
    pending.forall(validPending(keys))


  /** Invariant:
    * - Confirmed identity addresses must be for valid keys
    * - Confirmed identity must be valid for the associated key
    */
  def validConfirmed(keys: ListMap[Fingerprint, Key])(idf: (Identity, Fingerprint)): Boolean = {
    val (identity, fingerprint) = idf
    keys.contains(fingerprint) && {
      val key = keys(fingerprint)
      key.identities.contains(identity)
    }
  }

  def invConfirmed(keys: ListMap[Fingerprint, Key], confirmed: ListMap[Identity, Fingerprint]) =
    confirmed.forall(validConfirmed(keys))


  /** Invariant:
    * - Management tokens must be for valid keys
    */
  def invManaged(keys: ListMap[Fingerprint, Key], managed: ListMap[Token, Fingerprint]) =
    managed.forall(containedFingerprint(keys))
}

object ServerLemmas {

  def requestVerifyLemma1(@induct l: List[Identity], keys: ListMap[Fingerprint, Key], fingerprint: Fingerprint): Unit = {
    require(keys.contains(fingerprint) && l.forall(keys(fingerprint).identities.contains))

  }.ensuring { _ =>
    l.map { identity =>
      val token = Token.unique
      (token, EMail("verify", fingerprint, token), identity)
    }.forall {
      case (token, _, identity) =>
        validPending(keys)(token, (fingerprint, identity))
    }
  }

  def requestVerifyLemma2(@induct l: List[(Token, EMail, Identity)], keys: ListMap[Fingerprint, Key], fingerprint: Fingerprint): Unit = {
    require(l.forall {
      case (token, _, identity) =>
        validPending(keys)(token, (fingerprint, identity))
    })

  }.ensuring { _ =>
    l.map { case (token, _, identity) =>
      token -> (fingerprint, identity)
    }.forall(validPending(keys))
  }

  def invConfirmedFiltered(keys: ListMap[Fingerprint, Key], confirmed: ListMap[Identity, Fingerprint], fingerprint: Fingerprint): Unit = {
    require(invConfirmed(keys, confirmed))
    decreases(confirmed.toList.size)

    if (!confirmed.isEmpty)
      invConfirmedFiltered(keys, confirmed.tail, fingerprint)

  }.ensuring(_ =>
    confirmed.keysOf(fingerprint).forall(identity => validConfirmed(keys)((identity, fingerprint)))
  )

  def filteredLemma1(identities: List[Identity], keys: ListMap[Fingerprint, Key], fingerprint: Fingerprint): Unit = {
    require(identities.forall(identity => validConfirmed(keys)((identity, fingerprint))))
    decreases(identities.size)

    if (!identities.isEmpty) {
      assert(validConfirmed(keys)((identities.head, fingerprint)))
      check(keys.contains(fingerprint))
      val key = keys(fingerprint)
      filteredLemma1(identities.tail, keys, fingerprint)
    }

  }.ensuring(_ =>
    !identities.isEmpty ==> {
      identities.forall(keys(fingerprint).identities.contains)
    }
  )

  def moreContainedKeys(
    keys: ListMap[Fingerprint, Key], lm: ListMap[Token, Fingerprint],
    fingerprint: Fingerprint, key: Key
  ): Unit = {
    require(lm.forall(containedFingerprint(keys)))
    decreases(lm.toList.size)

    if (!lm.isEmpty) {
      moreContainedKeys(keys, lm.tail, fingerprint, key)
      addStillContains(keys, fingerprint, key, lm.head._2)
    }

  }.ensuring { _ =>
    val newKeys = keys + (fingerprint -> key)
    lm.forall(containedFingerprint(newKeys))
  }

  def invPendingMoreKeys(
    keys: ListMap[Fingerprint, Key], pending: ListMap[Token, (Fingerprint, Identity)],
    fingerprint: Fingerprint, key: Key
  ): Unit = {
    require(
      invPending(keys, pending) &&
      (keys.contains(fingerprint) ==> (keys(fingerprint) == key))
    )
    decreases(pending.toList.size)
    val newKeys = keys + (fingerprint, key)

    if (!pending.isEmpty) {
      val (token, (fingerprint2, identity)) = pending.head
      invPendingMoreKeys(keys, pending.tail, fingerprint, key)

      addStillContains(keys, fingerprint, key, fingerprint2) // gives us:
      assert(newKeys.contains(fingerprint2))
      val key2 = newKeys(fingerprint2)

      assert(keys.contains(fingerprint2))
      if (fingerprint == fingerprint2) {
        assert(key == key2)
        assert(key2.identities.contains(identity))
      } else {
        addApplyDifferent(keys, fingerprint, key, fingerprint2) // gives us:
        assert(key2 == keys(fingerprint2))

        assert(key2.identities.contains(identity))
      }
    }

  }.ensuring { _ =>
    val newKeys = keys + (fingerprint -> key)
    invPending(newKeys, pending)
  }

  def invConfirmedMoreKeys(
    keys: ListMap[Fingerprint, Key], confirmed: ListMap[Identity, Fingerprint],
    fingerprint: Fingerprint, key: Key
  ): Unit = {
    require(
      invConfirmed(keys, confirmed) &&
      (keys.contains(fingerprint) ==> (keys(fingerprint) == key))
    )
    decreases(confirmed.toList.size)
    val newKeys = keys + (fingerprint, key)

    if (!confirmed.isEmpty) {
      val (identity, fingerprint2) = confirmed.head
      invConfirmedMoreKeys(keys, confirmed.tail, fingerprint, key)

      addStillContains(keys, fingerprint, key, fingerprint2) // gives us:
      assert(newKeys.contains(fingerprint2))
      val key2 = newKeys(fingerprint2)

      assert(keys.contains(fingerprint2))
      if (fingerprint == fingerprint2) {
        assert(key == key2)
        assert(key2.identities.contains(identity))
      } else {
        addApplyDifferent(keys, fingerprint, key, fingerprint2) // gives us:
        assert(key2 == keys(fingerprint2))

        assert(key2.identities.contains(identity))
      }
    }

  }.ensuring { _ =>
    val newKeys = keys + (fingerprint -> key)
    invConfirmed(newKeys, confirmed)
  }
}
