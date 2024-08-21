(*  Title:      HOL/Tools/Proof_Improve/proof_improve.ML
    Author:     Daniel Lipkin, TU Muenchen

This module provides utilities for improving Isabelle proofs.
*)
signature PROOF_IMPROVE =
sig
   datatype outcome = FoundAlternative of  string * string
                    | Unknown of string
                    | ScoreNotLowered of string
                    | NoAlternativeFound of string
                    | GoodEnoughUnderCutoff of string

  val proof_improve : string -> thm list -> Proof.context -> outcome
  val proof_improve_old : Proof.state -> string -> outcome
  val string_of_outcome : outcome -> string
end;

structure Proof_Improve : PROOF_IMPROVE =
struct
open Proof_Improve_Scorer
open Proof_Improve_Dependency_Analyser
open Proof_Improve_Finder

datatype outcome = FoundAlternative of string * string
                 | Unknown of string
                 | ScoreNotLowered of string
                 | NoAlternativeFound of string
                 | GoodEnoughUnderCutoff of string

fun string_of_outcome outcome =
  case outcome of
      FoundAlternative ( _, log) => "Found Alternative\n" ^ log
    | Unknown log => "Unknown\n" ^ log
    | NoAlternativeFound log => "No Alternative Found\n" ^ log
    | ScoreNotLowered log => "Score Not Lowered\n" ^ log
    | GoodEnoughUnderCutoff log => "Good Enough; The Score is under the Cutoff\n" ^ log

fun postprocess_result finder_result initial_log original_score dependency_msg =
    case finder_result of
      NONE =>
        let
          val log_msg = initial_log ^ "\nNo potential rewrite found."
        in
          NoAlternativeFound (log_msg ^ "\n\n")
        end
    | SOME (found_facts, found_by, found_proof_text) =>
      let
        val (found_score, found_log) = score found_facts found_proof_text
        val found_score_msg = "Scorer result (found): " ^ Real.toString found_score ^" \n" ^
                              "Found by: " ^ found_by ^ "\n"
        val combined_log = initial_log ^ "\n" ^ found_log ^ found_score_msg ^ dependency_msg
      in
        if found_score < original_score then
          FoundAlternative (found_proof_text, combined_log ^ "\n\n")
        else if found_score >= original_score then
          ScoreNotLowered (combined_log ^ "\n\n")
        else
          Unknown (combined_log ^ "\n\n")
      end


fun proof_improve_old st proof_text =
  let
    val (original_score, original_log) = score
      (List.length [] (*Proof.the_fact_or_facts st*)) proof_text
    val original_score_msg = "Scorer result (original): " ^ Real.toString original_score
    val initial_log = original_log ^ original_score_msg
  in
    if original_score < 0.0 (*Disabled for testing... 4.5*) then
      GoodEnoughUnderCutoff (initial_log ^ "\n\n")
    else
      postprocess_result (find_old st) initial_log original_score ""
  end;

fun proof_improve proof_text thms ctxt =
  let
    val thm_deps = Proof_Improve_Dependency_Analyser.analyse_dependencies ctxt thms;

    val is_declared_as_simp = is_standard_simp ctxt thms;
    val is_declared_as_classical = is_classical ctxt thms;
    val ctxt' = if is_declared_as_simp then Raw_Simplifier.delsimps (ctxt, thms) else ctxt;
    (*val ctxt'' = if is_declared_as_classical then Classical.delrules (ctxt', thms) else ctxt';*)
    val proof_st = ctxt' |> Proof.theorem NONE (K I) [thms |> map (fn thm =>
                          (Thm.prop_of (Misc_Legacy.freeze_thaw_robust ctxt thm |> #1), []))];

    val (original_score, original_log) = score
      (List.length [] (*Proof.the_fact_or_facts st*)) proof_text
    val original_score_msg = "Scorer result (original): " ^ Real.toString original_score
    val initial_log = original_log ^ original_score_msg
  in
    if original_score < 0.0 (*Disabled for testing... 4.5*) then
      GoodEnoughUnderCutoff (initial_log ^ "\n\n")
    else
      postprocess_result (find proof_st thm_deps) initial_log original_score
        ("Filtered dependencies: " ^ @{make_string} (thm_deps) ^ "\n")
  end;

end