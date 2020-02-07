package pgp

import stainless.lang._
import stainless.annotation._
import stainless.collection._

@ignore
object Main {

  sealed trait LogType
  case object SECURE   extends LogType
  case object INSECURE extends LogType
  case object BOTH     extends LogType

  @ignore
  def log(message: String, logType: LogType = SECURE) = logType match {
    case SECURE   => println(Console.YELLOW  + "[SECURE] "   + message)
    case INSECURE => println(Console.RED     + "[INSECURE] " + message)
    case BOTH     => println(Console.CYAN    + "[INFO] "     + message)
  }

  val addresses = List(
    "ilyaz@comcast.net",
    "erynf@comcast.net",
    "phish@verizon.net",
    "empathy@yahoo.ca",
    "peoplesr@optonline.net",
    "crowl@verizon.net",
    "ranasta@live.com",
    "rupak@mac.com",
    "wonderkid@yahoo.com",
    "eminence@hotmail.com",
    "crusader@sbcglobal.net",
    "tezbo@att.net",
    "mailarc@yahoo.com",
    "majordick@me.com",
    "jaffe@aol.com",
    "mschilli@live.com",
    "whimsy@yahoo.com",
    "boser@yahoo.ca",
    "bulletin@optonline.net",
    "jonas@yahoo.ca",
    "gator@hotmail.com",
    "isotopian@outlook.com",
    "formis@aol.com",
    "hutton@outlook.com",
    "fviegas@outlook.com",
    "dkasak@msn.com",
    "sopwith@live.com",
    "horrocks@me.com",
    "tfinniga@comcast.net",
    "gfxguy@sbcglobal.net",
  )

  def window[A](list: List[A], size: Int): List[List[A]] = {
    if (list.length <= size) List(list)
    else {
      List(list.take(size)) ++ window(list.drop(size), size)
    }
  }

  def main(args: Array[String]): Unit = {
    val identities = addresses.map(Identity(_))

    lazy val server = new Server(validateIdent)

    def validateIdent(identity: Identity, email: EMail): Unit = {
      log(s"> Received validating email. Verifying $identity",SECURE)
      server.verify(email.token)
    }

    log("Initializing both servers with test data...",BOTH)
    log("Generating random keys...",BOTH)

    val keys = window(identities, 3).map(Key.random)

    log(s"Generated ${keys.length} keys with three identities each.",BOTH)
    log("Uploading keys to servers...",BOTH)

    val tokens = keys.map(k => (k, server.upload(k)))
    // val tokensInsecure = keys map (k => (k, insecureServer.upload(k)))

    log("Keys uploaded. Currently there should be 30 identities when querying by fingerprint/keyId",BOTH)

    def optionToList[A](opt: Option[A]): List[A] = {
      opt.map(List(_)).getOrElse(List.empty[A])
    }

    def validatedByFingerprint(s: Server) = keys
      .flatMap(k => optionToList(s.byFingerprint(k.fingerprint)))
      .flatMap(_.identities)

    def validatedByEmail(s: Server) =
        identities
        .flatMap(k => optionToList(s.byEmail(k)))
        .flatMap(_.identities)

    log(s"Validated (Fingerprint/KeyId): ${validatedByFingerprint(server).size}",SECURE)
    // log(s"Validated (Fingerprint/KeyId): ${validatedByFingerprint(insecureServer).size}",INSECURE)


    log("Currently, there should be 0 identities when querying a key by one of its associated identities", BOTH)

    log(s"Validated (Email): ${validatedByEmail(server).size}",SECURE)
    // log(s"Validated (Email): ${validatedByEmail(insecureServer).size}",INSECURE)


    // val token = tokens(0)._2
    // val id = tokens(0)._1.identities.take(1)
    // println("token", token)
    // println("id", id)
    // server.requestVerify(token, id)

    // println("server.pending", server.pending)
    // println(server.confirmed.get(id(0)))
    // println(server.byEmail(id(0)))
    // println(validatedByEmail(server))


    log("Verifying exactly one identity for 5 keys.",BOTH)
    tokens
      // .zip(tokensInsecure)
      .take(5)
      // .foreach { case (sec, insec) =>
      .map { sec =>
        val identSec = sec._1.identities.take(1)
        // val identInsec = insec._1.identities.take(1)
        server.requestVerify(sec._2, identSec)
        // insecureServer.requestVerify(insec._2, identInsec)
      }


    log("There should be 5 validated identities",BOTH)

    log(s"Validated (Email): ${validatedByEmail(server).size}", SECURE)
    // log(s"Validated (Email): ${validatedByEmail(insecureServer).size}", INSECURE)
  }
}
