(*  Title:      HOL/Tools/Mirabelle/mirabelle_proof_improve.ML
    Author:     Daniel Lipkin, TU Muenchen

Mirabelle action: "proof_improve".
*)

structure Mirabelle_Proof_Improve: MIRABELLE_ACTION =
struct

open Proof_Improve
open Proof_Improve_Changes

val data = Synchronized.var "Mirabelle_Proof_Improve_data" (create ())

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


fun make_action ({timeout, ...} : Mirabelle.action_context) =
  let
    val generous_timeout = Time.scale 1000.0 timeout

    fun run ({pre, spans, pos, ...} : Mirabelle.command) : string =
      let
        val proof_text = get_content spans
        val outcome =
          if proof_text = "" then
            Unknown "segment could not be matched\n"
          else
            Timeout.apply generous_timeout (proof_improve) pre proof_text
        val current_data = Synchronized.value data
        val updated_data =
          case outcome of
            FoundAlternative (found_proof, _) =>
               add_change (proof_text, found_proof, pos) current_data
            | _ =>
               add_unsuccessful_call current_data
      in
        Synchronized.change data (fn _ => updated_data);
        "Outcome: " ^ string_of_outcome outcome ^ "\n"
      end

    fun finalize () : string = to_string (Synchronized.value data)
      in
        ("", {run = run, finalize = finalize})
      end

    val () = Mirabelle.register_action "proof_improve" make_action
end;