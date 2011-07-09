/*  Title:      Pure/System/session.scala
    Author:     Makarius
    Options:    :folding=explicit:collapseFolds=1:

Main Isabelle/Scala session, potentially with running prover process.
*/

package isabelle

import java.lang.System

import scala.actors.TIMEOUT
import scala.actors.Actor
import scala.actors.Actor._


object Session
{
  /* file store */

  abstract class File_Store
  {
    def read(path: Path): String
  }


  /* events */

  //{{{
  case object Global_Settings
  case object Perspective
  case object Assignment
  case class Commands_Changed(set: Set[Command])

  sealed abstract class Phase
  case object Inactive extends Phase
  case object Startup extends Phase  // transient
  case object Failed extends Phase
  case object Ready extends Phase
  case object Shutdown extends Phase  // transient
  //}}}
}


class Session(val file_store: Session.File_Store)
{
  /* real time parameters */  // FIXME properties or settings (!?)

  val input_delay = Time.seconds(0.3)  // user input (e.g. text edits, cursor movement)
  val output_delay = Time.seconds(0.1)  // prover output (markup, common messages)
  val update_delay = Time.seconds(0.5)  // GUI layout updates


  /* pervasive event buses */

  val global_settings = new Event_Bus[Session.Global_Settings.type]
  val perspective = new Event_Bus[Session.Perspective.type]
  val assignments = new Event_Bus[Session.Assignment.type]
  val commands_changed = new Event_Bus[Session.Commands_Changed]
  val phase_changed = new Event_Bus[Session.Phase]
  val raw_messages = new Event_Bus[Isabelle_Process.Message]



  /** buffered command changes (delay_first discipline) **/

  //{{{
  private case object Stop

  private val (_, command_change_buffer) =
    Simple_Thread.actor("command_change_buffer", daemon = true)
  {
    var changed: Set[Command] = Set()
    var flush_time: Option[Long] = None

    def flush_timeout: Long =
      flush_time match {
        case None => 5000L
        case Some(time) => (time - System.currentTimeMillis()) max 0
      }

    def flush()
    {
      if (!changed.isEmpty) commands_changed.event(Session.Commands_Changed(changed))
      changed = Set()
      flush_time = None
    }

    def invoke()
    {
      val now = System.currentTimeMillis()
      flush_time match {
        case None => flush_time = Some(now + output_delay.ms)
        case Some(time) => if (now >= time) flush()
      }
    }

    var finished = false
    while (!finished) {
      receiveWithin(flush_timeout) {
        case command: Command => changed += command; invoke()
        case TIMEOUT => flush()
        case Stop => finished = true; reply(())
        case bad => System.err.println("command_change_buffer: ignoring bad message " + bad)
      }
    }
  }
  //}}}



  /** main protocol actor **/

  /* global state */

  @volatile var verbose: Boolean = false

  @volatile private var loaded_theories: Set[String] = Set()

  @volatile private var syntax = new Outer_Syntax
  def current_syntax(): Outer_Syntax = syntax

  @volatile private var reverse_syslog = List[XML.Elem]()
  def syslog(): String = reverse_syslog.reverse.map(msg => XML.content(msg).mkString).mkString("\n")

  @volatile private var _phase: Session.Phase = Session.Inactive
  private def phase_=(new_phase: Session.Phase)
  {
    _phase = new_phase
    phase_changed.event(new_phase)
  }
  def phase = _phase
  def is_ready: Boolean = phase == Session.Ready

  private val global_state = new Volatile(Document.State.init)
  def current_state(): Document.State = global_state()

  def snapshot(name: String, pending_edits: List[Text.Edit]): Document.Snapshot =
    global_state().snapshot(name, pending_edits)


  /* theory files */

  val thy_load = new Thy_Load
  {
    override def is_loaded(name: String): Boolean =
      loaded_theories.contains(name)

    override def check_thy(dir: Path, name: String): (String, Thy_Header.Header) =
    {
      val file = Isabelle_System.platform_file(dir + Thy_Header.thy_path(name))
      if (!file.exists || !file.isFile) error("No such file: " + quote(file.toString))
      val text = Standard_System.read_file(file)
      val header = Thy_Header.read(text)
      (text, header)
    }
  }

  val thy_info = new Thy_Info(thy_load)


  /* actor messages */

  private case class Start(timeout: Time, args: List[String])
  private case object Interrupt
  private case class Init_Node(name: String, header: Document.Node.Header, text: String)
  private case class Edit_Node(name: String, header: Document.Node.Header, edits: List[Text.Edit])
  private case class Change_Node(
    name: String,
    doc_edits: List[Document.Edit_Command],
    header_edits: List[(String, Thy_Header.Header)],
    previous: Document.Version,
    version: Document.Version)

  private val (_, session_actor) = Simple_Thread.actor("session_actor", daemon = true)
  {
    val this_actor = self
    var prover: Option[Isabelle_Process with Isar_Document] = None


    /* incoming edits */

    def handle_edits(name: String,
        header: Document.Node.Header, edits: List[Option[List[Text.Edit]]])
    //{{{
    {
      val syntax = current_syntax()
      val previous = global_state().history.tip.version
      val doc_edits = edits.map(edit => (name, edit))
      val result = Future.fork {
        Thy_Syntax.text_edits(syntax, previous.join, doc_edits, List((name, header)))
      }
      val change =
        global_state.change_yield(_.extend_history(previous, doc_edits, result.map(_._3)))

      result.map {
        case (doc_edits, header_edits, _) =>
          assignments.await { global_state().is_assigned(previous.get_finished) }
          this_actor !
            Change_Node(name, doc_edits, header_edits, previous.join, change.version.join)
      }
    }
    //}}}


    /* resulting changes */

    def handle_change(change: Change_Node)
    //{{{
    {
      val previous = change.previous
      val version = change.version
      val name = change.name
      val doc_edits = change.doc_edits
      val header_edits = change.header_edits

      var former_assignment = global_state().the_assignment(previous).get_finished
      for {
        (name, Some(cmd_edits)) <- doc_edits
        (prev, None) <- cmd_edits
        removed <- previous.nodes(name).commands.get_after(prev)
      } former_assignment -= removed

      def id_command(command: Command): Document.Command_ID =
      {
        if (global_state().lookup_command(command.id).isEmpty) {
          global_state.change(_.define_command(command))
          prover.get.define_command(command.id, Symbol.encode(command.source))
        }
        command.id
      }
      val id_edits =
        doc_edits map {
          case (name, edits) =>
            val ids =
              edits.map(_.map { case (c1, c2) => (c1.map(id_command), c2.map(id_command)) })
            (name, ids)
        }

      global_state.change(_.define_version(version, former_assignment))
      prover.get.edit_version(previous.id, version.id, id_edits, header_edits)
    }
    //}}}


    /* prover results */

    def handle_result(result: Isabelle_Process.Result)
    //{{{
    {
      def bad_result(result: Isabelle_Process.Result)
      {
        if (verbose)
          System.err.println("Ignoring prover result: " + result.message.toString)
      }

      result.properties match {
        case Position.Id(state_id) =>
          try {
            val st = global_state.change_yield(_.accumulate(state_id, result.message))
            command_change_buffer ! st.command
          }
          catch { case _: Document.State.Fail => bad_result(result) }
        case _ =>
          if (result.is_syslog) {
            reverse_syslog ::= result.message
            if (result.is_ready) {
              // FIXME move to ML side (!?)
              syntax += ("hence", Keyword.PRF_ASM_GOAL, "then have")
              syntax += ("thus", Keyword.PRF_ASM_GOAL, "then show")
              phase = Session.Ready
            }
            else if (result.is_exit && phase == Session.Startup) phase = Session.Failed
            else if (result.is_exit) phase = Session.Inactive
          }
          else if (result.is_stdout) { }
          else if (result.is_status) {
            result.body match {
              case List(Isar_Document.Assign(id, edits)) =>
                try {
                  val cmds: List[Command] = global_state.change_yield(_.assign(id, edits))
                  for (cmd <- cmds) command_change_buffer ! cmd
                  assignments.event(Session.Assignment)
                }
                catch { case _: Document.State.Fail => bad_result(result) }
              case List(Keyword.Command_Decl(name, kind)) => syntax += (name, kind)
              case List(Keyword.Keyword_Decl(name)) => syntax += name
              case List(Thy_Info.Loaded_Theory(name)) => loaded_theories += name
              case _ => bad_result(result)
            }
          }
          else bad_result(result)
        }
    }
    //}}}


    /* main loop */

    //{{{
    var finished = false
    while (!finished) {
      receive {
        case Start(timeout, args) if prover.isEmpty =>
          if (phase == Session.Inactive || phase == Session.Failed) {
            phase = Session.Startup
            prover = Some(new Isabelle_Process(timeout, this_actor, args:_*) with Isar_Document)
          }

        case Stop =>
          if (phase == Session.Ready) {
            global_state.change(_ => Document.State.init)  // FIXME event bus!?
            phase = Session.Shutdown
            prover.get.terminate
            prover = None
            phase = Session.Inactive
          }
          finished = true
          reply(())

        case Interrupt if prover.isDefined =>
          prover.get.interrupt

        case Init_Node(name, header, text) if prover.isDefined =>
          // FIXME compare with existing node
          handle_edits(name, header, List(None, Some(List(Text.Edit.insert(0, text)))))
          reply(())

        case Edit_Node(name, header, text_edits) if prover.isDefined =>
          handle_edits(name, header, List(Some(text_edits)))
          reply(())

        case change: Change_Node if prover.isDefined =>
          handle_change(change)

        case input: Isabelle_Process.Input =>
          raw_messages.event(input)

        case result: Isabelle_Process.Result =>
          handle_result(result)
          raw_messages.event(result)

        case bad => System.err.println("session_actor: ignoring bad message " + bad)
      }
    }
    //}}}
  }


  /* actions */

  def start(timeout: Time, args: List[String]) { session_actor ! Start(timeout, args) }

  def stop() { command_change_buffer !? Stop; session_actor !? Stop }

  def interrupt() { session_actor ! Interrupt }

  def init_node(name: String, header: Document.Node.Header, text: String)
  { session_actor !? Init_Node(name, header, text) }

  def edit_node(name: String, header: Document.Node.Header, edits: List[Text.Edit])
  { session_actor !? Edit_Node(name, header, edits) }
}
