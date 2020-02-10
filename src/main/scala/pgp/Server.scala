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
  private def filtered(fingerprint: Fingerprint): Key = {
    require(invariant && keys.contains(fingerprint))

    val key = keys(fingerprint)
    val identities = confirmed.keysOf(fingerprint)

    keysOfSound(confirmed, fingerprint) // gives us:
    identities.forall(id => confirmed.get(id) == Some(fingerprint))

    invConfirmedFiltered(keys, confirmed, fingerprint) // gives us:
    assert(identities.forall(identity => validConfirmed(keys, identity, fingerprint)))

    filteredLemma1(identities, keys, fingerprint) // gives us:
    assert(identities.isEmpty || identities.forall(key.identities.contains))

    if (!identities.isEmpty) {
      forallContainsSubset(identities, key.identities) // gives us:
      check(identities.content subsetOf key.identities.content)
    } else {
      check(identities.content subsetOf key.identities.content)
    }

    key.restrictedTo(identities)
  }


  /**
   * Look up the (unique) key associated with an identity address.
   *
   * Note that this key should be in keys, too.
   */
  def byEmail(identity: Identity): Option[Key] = {
    require(invariant)
    val fingerprintOpt = confirmed.get(identity)
    getForall(confirmed, validConfirmed(keys, _, _), identity)
    assert(fingerprintOpt.forall(fingerprint => validConfirmed(keys, identity, fingerprint)))
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

    assert(validKey(fingerprint, key))

    addValidProp(keys, validKey, fingerprint, key) // gives us:
    assert(invKeys(keys + (fingerprint -> key)))

    moreContainedKeys(keys, uploaded, fingerprint, key) // gives us:
    assert(invUploaded(keys + (fingerprint -> key), uploaded))

    invPendingMoreKeys(keys, pending, fingerprint, key) // gives us:
    assert(invPending(keys + (fingerprint -> key), pending))

    invConfirmedMoreKeys(keys, confirmed, fingerprint, key) // gives us:
    assert(invConfirmed(keys + (fingerprint -> key), confirmed))

    moreContainedKeys(keys, managed, fingerprint, key) // gives us:
    assert(invManaged(keys + (fingerprint -> key), managed))

    keys += (fingerprint -> key)

    assert(invKeys(keys))
    assert(invUploaded(keys, uploaded))
    assert(invPending(keys, pending))
    assert(invConfirmed(keys, confirmed))
    assert(invManaged(keys, managed))

    uploaded += (token -> fingerprint)

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
        validPending(keys, token, fingerprint, identity)
    }
  }

  def requestVerifyLemma2(l: List[(Token, EMail, Identity)], fingerprint: Fingerprint): Unit = {
    require(l.forall {
      case (token, _, identity) =>
        validPending(keys, token, fingerprint, identity)
    })
    decreases(l)

    if (!l.isEmpty) requestVerifyLemma2(l.tail, fingerprint)

  } ensuring { _ =>
    l.map { case (token, _, identity) =>
      token -> (fingerprint, identity)
    }.forall { case (k, v) => validPending(keys, k, v._1, v._2) }
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
      assert(invUploaded(keys, uploaded))
      assert(uploaded.forall { case (_, fingerprint) => keys.contains(fingerprint) })
      applyForall(uploaded, (token: Token, fingerprint: Fingerprint) => keys.contains(fingerprint), from)
      val key = keys(fingerprint)
      if (identities.content.subsetOf(key.identities.content)) {

        ListUtils.subsetContains(identities, key.identities) // gives us:
        assert(identities.forall(key.identities.contains))

        val toTreat = identities.map { identity =>
          val token = Token.unique
          (Token.unique, EMail("verify", fingerprint, token), identity)
        }

        requestVerifyLemma1(identities, fingerprint) // gives us:
        assert(toTreat.forall { case (token, _, identity) =>
          validPending(keys, token, fingerprint, identity)
        })

        val toAdd = toTreat.map { case (token, _, identity) =>
          token -> (fingerprint, identity)
        }

        requestVerifyLemma2(toTreat, fingerprint) // gives us:
        Utils.assume(
          toTreat.map { case (token, _, identity) =>
            token -> (fingerprint, identity)
          }.forall { case (k, (v1, v2)) => validPending(keys, k, v1, v2) }
        )
        assert(toAdd.forall {
          case (token, value) =>
            validPending(keys, token, value._1, value._2)
        })

        // assert(toAdd.forall { case (k, (f, i)) => validPending(keys, k, f, i) })

        val newPending = pending ++ toAdd

        assert(pending.forall(
          (token: Token, value: (Fingerprint, Identity)) =>
            validPending(keys, token, value._1, value._2)))
        insertAllValidProp(pending, toAdd,
          (token: Token, value: (Fingerprint, Identity)) =>
            validPending(keys, token, value._1, value._2)
        ) // gives us:
        assert(invPending(keys, newPending))

        pending = newPending

        toTreat.map { case (_, email, identity) =>
          notif(identity, email)
        }

        ()
      }
    }
  }.ensuring(_ => invariant)

  // /**
  //  * Verify an identity address by a token received via identity.
  //  *
  //  * Note that we keep the mapping in uploaded to allow further verifications.
  //  */
  // def verify(token: Token): Unit = {
  //   if (pending.contains(token)) {
  //     val (fingerprint, identity) = pending(token)

  //     pending -= token // Affected invariant: inv_pending

  //     assert(validConfirmed(keys, identity, fingerprint))
  //     confirmed += (identity -> fingerprint) // Affected invariant: inv_confirmed
  //   }
  // }

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


object ServerProperties {

  /** Invariant:
    *  - A key is valid if its fingerprint is registered in keys
    */
  def validKey(fingerprint: Fingerprint, key: Key): Boolean = {
    key.fingerprint == fingerprint
  }

  def invKeys(keys: ListMap[Fingerprint, Key]) = keys.forall(validKey)

  /** Invariant:
    * - All keys must be registered via the correct fingerprint
    * - Upload tokens must be for valid keys
    */
  def invUploaded(keys: ListMap[Fingerprint, Key], uploaded: ListMap[Token, Fingerprint]) =
    uploaded.forall { case (token, fingerprint) => keys.contains(fingerprint) }

  /** Invariant:
    * - Pending validations must be for valid keys
    * - Pending validations must be for identity addresses associated for the respective key
    */
  def validPending(keys: ListMap[Fingerprint, Key], token: Token, fingerprint: Fingerprint, identity: Identity): Boolean = {
    keys.contains(fingerprint) && {
      val key = keys(fingerprint)
      key.identities.contains(identity)
    }
  }

  def invPending(keys: ListMap[Fingerprint, Key], pending: ListMap[Token, (Fingerprint, Identity)]) =
    pending.forall { case (token, (fingerprint, identity)) =>
      validPending(keys, token, fingerprint, identity)
    }

  /** Invariant:
    * - Confirmed identity addresses must be for valid keys
    * - Confirmed identity must be valid for the associated key
    */
  def validConfirmed(keys: ListMap[Fingerprint, Key], identity: Identity, fingerprint: Fingerprint): Boolean = {
    keys.contains(fingerprint) && {
      val key = keys(fingerprint)
      key.identities.contains(identity)
    }
  }

  def invConfirmed(keys: ListMap[Fingerprint, Key], confirmed: ListMap[Identity, Fingerprint]) =
    confirmed.forall { case (identity, fingerprint) => validConfirmed(keys, identity, fingerprint) }

  /** Invariant:
    * - Management tokens must be for valid keys
    */
  def invManaged(keys: ListMap[Fingerprint, Key], managed: ListMap[Token, Fingerprint]) =
    managed.forall { case (token, fingerprint) => keys.contains(fingerprint) }
}

object ServerLemmas {

  def invConfirmedFiltered(keys: ListMap[Fingerprint, Key], confirmed: ListMap[Identity, Fingerprint], fingerprint: Fingerprint): Unit = {
    require(invConfirmed(keys, confirmed))
    decreases(confirmed.toList.size)

    if (!confirmed.isEmpty)
      invConfirmedFiltered(keys, confirmed.tail, fingerprint)

  }.ensuring(_ =>
    confirmed.keysOf(fingerprint).forall(identity => validConfirmed(keys, identity, fingerprint))
  )

  def filteredLemma1(identities: List[Identity], keys: ListMap[Fingerprint, Key], fingerprint: Fingerprint): Unit = {
    require(identities.forall(identity => validConfirmed(keys, identity, fingerprint)))
    decreases(identities.size)

    if (!identities.isEmpty) {
      assert(validConfirmed(keys, identities.head, fingerprint))
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
    require(lm.forall { case (token, fingerprint) => keys.contains(fingerprint) })
    decreases(lm.toList.size)

    if (!lm.isEmpty) {
      moreContainedKeys(keys, lm.tail, fingerprint, key)
      addStillContains(keys, fingerprint, key, lm.head._2)
    }

  }.ensuring { _ =>
    val newKeys = keys + (fingerprint -> key)
    lm.forall { case (token, fingerprint) => newKeys.contains(fingerprint) }
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

  }.ensuring(_ =>
    invPending(keys + (fingerprint, key), pending)
  )

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

  }.ensuring(_ =>
    invConfirmed(keys + (fingerprint, key), confirmed)
  )

  // @opaque
  // def fingerprintKeyInverse(keys: ListMap[Fingerprint, Key], key: Key): Unit = {
  //   require(keys.contains(key.fingerprint) && invKeys(keys) && uniqueFingeprints)

  //   applyForall(keys, validKey, key.fingerprint)
  //   assert(keys(key.fingerprint).fingerprint == key.fingerprint)

  //   assert(sameFingerprintSameKey((keys(key.fingerprint), key)))

  //   check(keys(key.fingerprint) == key)
  //   ()

  // }.ensuring(_ =>
  //   keys(key.fingerprint) == key
  // )
}
