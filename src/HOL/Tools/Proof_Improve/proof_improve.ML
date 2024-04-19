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

  val proof_improve : Proof.state -> string -> string list -> outcome
  val string_of_outcome : outcome -> string
end;

structure Proof_Improve : PROOF_IMPROVE =
struct
open Proof_Improve_Scorer
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


fun proof_improve st proof_text thms =
  let
    val (original_score, original_log) = score
      (List.length (Proof.the_fact_or_facts st)) proof_text
    val original_score_msg = "Scorer result (original): " ^ Real.toString original_score
    (*val find_result = find st*)
    val initial_log = original_log ^ original_score_msg
  in
    if original_score < 4.5 then
      GoodEnoughUnderCutoff (initial_log ^ "\n\n")
    else
      case find st thms of
        NONE =>
          let
            val log_msg = initial_log ^ "\nNo potential rewrite found."
          in
            NoAlternativeFound (log_msg ^ "\n\n")
          end
      | SOME (found_facts, found_proof_text) =>
        let
          val (found_score, found_log) = score found_facts found_proof_text
          val found_score_msg = "Scorer result (found): " ^ Real.toString found_score ^" \n"
          val combined_log = initial_log ^ "\n" ^ found_log ^ found_score_msg
        in
          if found_score < original_score then
            FoundAlternative (found_proof_text, combined_log ^ "\n\n")
          else if found_score >= original_score then
            ScoreNotLowered (combined_log ^ "\n\n")
          else
            Unknown (combined_log ^ "\n\n")
        end
  end;
end