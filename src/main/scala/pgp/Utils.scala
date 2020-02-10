package pgp

import stainless.annotation._

object Utils {

  // `assume` adds an assumption for the verifier, and is checked at runtime
  // using an `assert`
  @extern
  def assume(b: Boolean): Unit = {
    assert(b)
  }.ensuring(_ => b)
}
