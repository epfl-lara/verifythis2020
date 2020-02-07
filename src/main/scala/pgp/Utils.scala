package pgp

import stainless.annotation._

object Utils {
  @extern
  def assume(b: Boolean): Unit = {
    (??? : Unit)
  }.ensuring(_ => b)
}
