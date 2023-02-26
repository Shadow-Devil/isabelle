/*  Title:      Pure/System/isabelle_process.scala
    Author:     Makarius

Isabelle process wrapper.
*/

package isabelle


import java.util.{Map => JMap}
import java.io.{File => JFile}


object Isabelle_Process {
  def start(
    store: Sessions.Store,
    options: Options,
    session: Session,
    session_background: Sessions.Background,
    logic: String = "",
    raw_ml_system: Boolean = false,
    use_prelude: List[String] = Nil,
    eval_main: String = "",
    modes: List[String] = Nil,
    cwd: JFile = null,
    env: JMap[String, String] = Isabelle_System.settings()
  ): Isabelle_Process = {
    val channel = System_Channel()
    val process =
      try {
        val ml_options =
          options.
            string.update("system_channel_address", channel.address).
            string.update("system_channel_password", channel.password)
        ML_Process(store, ml_options, session_background,
          logic = logic, raw_ml_system = raw_ml_system,
          use_prelude = use_prelude, eval_main = eval_main,
          modes = modes, cwd = cwd, env = env)
      }
      catch { case exn @ ERROR(_) => channel.shutdown(); throw exn }

    val isabelle_process = new Isabelle_Process(session, process)
    process.stdin.close()
    session.start(receiver => new Prover(receiver, session.cache, channel, process))

    isabelle_process
  }
}

class Isabelle_Process private(session: Session, process: Bash.Process) {
  private val startup = Future.promise[String]
  private val terminated = Future.promise[Process_Result]

  session.phase_changed +=
    Session.Consumer(getClass.getName) {
      case Session.Ready =>
        startup.fulfill("")
      case Session.Terminated(result) =>
        if (!result.ok && !startup.is_finished) {
          val syslog = session.syslog.content()
          val err = "Session startup failed" + if_proper(syslog, ":\n" + syslog)
          startup.fulfill(err)
        }
        terminated.fulfill(result)
      case _ =>
    }

  def await_startup(): Isabelle_Process =
    startup.join match {
      case "" => this
      case err => session.stop(); error(err)
    }

  def await_shutdown(): Process_Result = {
    val result = terminated.join
    session.stop()
    result
  }

  def terminate(): Unit = process.terminate()
}
