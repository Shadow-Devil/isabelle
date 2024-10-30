(*  Title:      HOL/Tools/Mirabelle/mirabelle_proof_improve.ML
    Author:     Daniel Lipkin, TU Muenchen

Mirabelle action: "proof_improve".
*)

structure Mirabelle_Proof_Improve: MIRABELLE_ACTION =
struct

open Proof_Improve
open Proof_Improve_Changes

val data = Synchronized.var "Mirabelle_Proof_Improve_data" empty_changes

fun get_content spans : string =
  let
    val tokens = List.concat (List.map Command_Span.content spans)
    val non_comment_tokens = List.filter (fn tok => not (Token.is_comment tok)) tokens
    fun concat_tokens (toks, acc) =
      case toks of
        [] => acc
        | tok::rest =>
          let
            val token_str = Token.content_of tok
            val updated_acc =
              if acc = ""
                 orelse String.isSuffix " " acc
                 orelse String.isPrefix " " token_str
                 orelse (String.isSuffix "(" acc andalso token_str <> " ")
                 orelse (token_str = ")" andalso acc <> "" andalso String.isSuffix " " acc)
              then acc ^ token_str
              else acc ^ " " ^ token_str
          in
            concat_tokens (rest, updated_acc)
          end
  in
    concat_tokens (non_comment_tokens, "")
  end;

fun get_thms (st: Proof.state) (st': Toplevel.state): (string * thm list) list =
  let
    val get_facts  = Proof_Context.facts_of o Proof.context_of o Toplevel.proof_of
    val facts = (Proof_Context.facts_of o Proof.context_of) st
    val (factss, facts') = (
      if Toplevel.is_proof st' then
        ([facts], get_facts st')
      else
        let
          val ctxt = Toplevel.context_of st';
          val prev_thys =
            (case Toplevel.previous_theory_of st' of
              SOME thy => [thy]
            | NONE => Theory.parents_of (Proof_Context.theory_of ctxt));
          val factss = map Global_Theory.facts_of prev_thys
          val facts' = Global_Theory.facts_of (Proof_Context.theory_of ctxt)
        in (factss, facts') end)
    in (Facts.dest_static false factss facts') end;



fun make_action ({timeout, ...} : Mirabelle.action_context) =
  let
    fun run ({pre, spans, pos, post, ...} : Mirabelle.command) : (proof_changes -> proof_changes) * string =
      let
        val ctxt = Toplevel.context_of post
        val mode = Proof_Improve_Config_Manager.get_approach ()
        val (thms, get_thms_timing): (thm list * int) = if mode = "original" then ([], 0) else 
          Mirabelle.cpu_time ((maps snd) o these o try (Timeout.apply_physical (Time.fromSeconds 5)
            (get_thms pre))) post
        val proof_text = get_content spans

        val outcome =
          if proof_text = "" then
            Unknown "segment could not be matched\n"
          else if String.isSubstring "induct" proof_text then
            Unknown "skipped induction proof for performance reasons"
          else if mode <> "original" andalso null thms then
            if mode = "combined" then
              proof_improve_original pre proof_text
            else
              Unknown "Thm could not be found\n"
          else if mode = "original" then
            proof_improve_original pre proof_text
          else
            proof_improve proof_text thms ctxt
      in

        (fn current_data => case outcome of
            FoundAlternative (found_proof, _) =>
               add_change (proof_text, found_proof, pos) current_data
            | _ =>
               add_unsuccessful_call current_data, cat_lines [
          if mode = "original" then "" else "Current Thm: " ^ (map (ATP_Util.short_thm_name ctxt) thms |> space_implode " "),
          "Outcome: " ^ string_of_outcome outcome,
          if mode = "original" then "" else "get_thms_timing: " ^ Int.toString get_thms_timing ^ "ms"])
      end

    fun finalize () : string = to_string (Synchronized.value data)
  in
    ("", {run = fn command => (
        case Timeout.apply timeout run command 
        of (f, log) => (Synchronized.change data f; log)), finalize = finalize})
  end

val () = Mirabelle.register_action "proof_improve" make_action
end;