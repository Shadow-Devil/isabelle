(*  Title:      HOL/Tools/Proof_Improve/proof_improve_scorer.ML
    Author:     Daniel Lipkin, TU Muenchen

Scores proofs based on cognitive complexity.
*)

open Proof_Improve_Config_Manager

signature PROOF_IMPROVE_SCORER =
sig
  val score : int -> string -> real * string
  val score_thm :  thm list -> string  -> real * string
  val score_state :  Proof.state -> string -> real * string
end;

fun calculate_length_score st : int = String.size st

fun calculate_entropy_score proof_text : real =
  let
    val total_chars = size proof_text
    fun count_char c = List.foldl (fn (ch, acc) =>
    if ch = c then acc + 1 else acc) 0 (String.explode proof_text)
    fun freq c = (Real.fromInt (count_char c)) / (Real.fromInt total_chars)
    fun entropy c = let val p = freq c in p * Math.ln p / Math.ln 2.0 end

    fun dedup_sorted_list xs =
      case xs of
          [] => []
        | [x] => [x]
        | x::y::ys => if x = y then dedup_sorted_list (y::ys)
        else x :: dedup_sorted_list (y::ys)

    val chars_list = String.explode proof_text
                      |> sort Char.compare
                      |> dedup_sorted_list

  in
    if total_chars = 0 then 0.0
    else ~1.0 * (List.foldl (fn (c, acc) => acc + entropy c) 0.0 chars_list)
  end;

fun calculate_symbol_to_text_ratio proof_text : real =
  let
    val total_chars = size proof_text
    val symbols_count = List.foldl (fn (ch, acc) =>
                      if Char.isAlpha ch orelse ch = #" "
                      then acc else acc + 1) 0 (String.explode proof_text)
  in
    if total_chars = 0 then 0.0
    else (Real.fromInt symbols_count / Real.fromInt total_chars) * 100.0
  end;

fun calculate_used_methods_score proof_text : real option =
    let
        val apply_bys = String.tokens (fn c => c = #" ") proof_text
                        |> List.filter (fn s => s = "apply" orelse s = "by" orelse s = "proof")
        val count_apply_bys = length apply_bys

        fun score_method method =
            if String.isSubstring method proof_text then
                case method of
                    "intro" => 20.0
                  | "elim" => 20.0
                  | "unfold" => 20.0
                  | "simp" => 40.0
                  | "blast" => 60.0
                  | "iprover" => 80.0
                  | "fast" => 80.0
                  | "force" => 80.0
                  | "auto" => 80.0
                  | "arith" => 80.0
                  | "metis" => 100.0
                  | _ => 0.0
            else 0.0

        val methods = ["iprover", "blast", "fast", "intro", "elim", "unfold",
                       "simp", "force", "auto", "arith", "metis"]
        val total_score = fold (fn method => fn acc => acc + score_method method) methods 0.0
    in
        if count_apply_bys = 0 then NONE
        else SOME (total_score / Real.fromInt count_apply_bys)
    end;

fun calculate_depth proof_text =
  let
    val tokens = String.tokens (fn c => c = #" ") proof_text

    fun is_command token =
      List.exists (fn cmd => cmd = token) ["proof", "qed", "done", "apply", "by"]

    fun depth_aux (toks, current_depth, max_depth, continue) =
      case toks of
          [] => max_depth
        | tok::rest =>
            let
              val new_depth =
                case tok of
                   "proof" => current_depth + 1
                 | "qed" => current_depth - 1
                 | "done" => current_depth - 1
                 | "apply" => if continue then current_depth + 1 else current_depth
                 | "by" => if not continue then current_depth - 1 else current_depth
                 | _ => current_depth
            in
              if is_command tok then
                depth_aux (rest, new_depth, Int.max(max_depth, new_depth),
                          case tok of
                             "apply" => not continue
                           | "by" => continue
                           | _ => true)
              else
                depth_aux (rest, current_depth, max_depth, continue)
            end
  in
    depth_aux (tokens, 0, 0, true)
  end;

fun count_applys proof_text =
  let
    val tokens = String.tokens (fn c => c = #" ") proof_text
    fun is_apply_command token = (token = "apply")
    val apply_count = List.foldl (fn (tok, acc) =>
      if is_apply_command tok then acc + 1 else acc) 0 tokens
  in
    apply_count
  end;

fun log_normalize (value: real, max_value: real) : real =
  if value <= 0.0 then 0.0
  else
    let
      val log_value = Math.ln (value + 1.0)
      val log_max_value = Math.ln (max_value + 1.0)
      val result = 100.0 * (log_value / log_max_value)
    in
      if result > 100.0 then 100.0 else result
    end

fun linear_normalize (value: real, max_value: real) : real =
  if value <= 0.0 then 0.0
  else if max_value <= 0.0 then 0.0
  else
    let
      val result = 100.0 * (value /  max_value)
    in
      if result > 100.0 then 100.0 else result
    end;

fun normalize_score_real (mode, value: real, max_value) : real =
  case mode of
      "log" => log_normalize (value, max_value)
    | "linear" => linear_normalize (value, max_value)
    | _ => (tracing ("Error: Invalid normalization mode: " ^ mode); 0.0);

fun normalize_score_int (mode, value: int, max_value) : real =
  case mode of
      "log" => log_normalize (Real.fromInt value, Real.fromInt max_value)
    | "linear" => linear_normalize (Real.fromInt value, Real.fromInt max_value)
    | _ => (tracing ("Error: Invalid normalization mode: " ^ mode); 0.0);

structure Proof_Improve_Scorer : PROOF_IMPROVE_SCORER =
struct
fun score facts proof_text  =
  let
    val normalize_mode = get_normalize_mode ()
    val logging = get_logging ()

    val weight_length = get_weight_length ()
    val weight_lemma = get_weight_lemma ()
    val weight_entropy = get_weight_entropy ()
    val weight_symbol_to_text_ratio = get_weight_symbol_to_text_ratio ()
    val weight_depth = get_weight_depth ()
    val weight_apply = get_weight_apply ()

    val max_length = get_max_length ()
    val max_lemma = get_max_lemma ()
    val max_entropy = get_max_entropy ()
    val max_depth  = get_max_depth ()
    val max_apply = get_max_apply ()

    val length_score = normalize_score_int (normalize_mode, calculate_length_score proof_text,
      max_length)
    val length_report = "Length score: " ^ Real.toString length_score ^ "\n"

    val fact_score = normalize_score_int (normalize_mode, facts, max_lemma)
    val fact_report = "Fact score: " ^ Real.toString fact_score ^ "\n"

    val entropy_score = normalize_score_real (normalize_mode, calculate_entropy_score proof_text,
      max_entropy)
    val entropy_report = "Entropy score: " ^ Real.toString entropy_score ^ "\n"

    val symbol_to_text_ratio_score = calculate_symbol_to_text_ratio proof_text
    val symbol_to_text_ratio_report = "Symbol to text ratio score: " ^
    Real.toString symbol_to_text_ratio_score ^ "\n"

    val depth_score = normalize_score_int (normalize_mode, calculate_depth proof_text, max_depth)
    val depth_report = "Proof depth score: " ^ Real.toString depth_score ^ "\n"

    val apply_score = normalize_score_int (normalize_mode, count_applys proof_text, max_apply)
    val apply_report = "Apply score: " ^ Real.toString apply_score ^ "\n"

    val used_methods_score_opt = calculate_used_methods_score proof_text
    val (used_methods_score, weight_used_methods, used_methods_report) =
         case used_methods_score_opt of
              NONE => (0.0, 0.0, "no by's or proof's found\n")
              | SOME x => (Real.max (x, 100.0), get_weight_used_methods (), "Used methods score: " ^ Real.toString x ^ "\n")

    val weighted_sum = (length_score * weight_length) + (fact_score * weight_lemma) +
                       (entropy_score * weight_entropy) + (depth_score * weight_depth) +
                       (symbol_to_text_ratio_score * weight_symbol_to_text_ratio) +
                       (apply_score * weight_apply) + (used_methods_score * weight_used_methods)

    val total_weight = weight_length + weight_lemma + weight_entropy +
                       weight_symbol_to_text_ratio + weight_depth + weight_apply
                       + weight_used_methods

    val normalized_score = weighted_sum / total_weight

    val logs =
    if logging then
      length_report ^ fact_report ^ entropy_report ^  symbol_to_text_ratio_report
      ^ depth_report ^ apply_report ^ used_methods_report ^ "Proof Text: " ^ proof_text ^ "\n"
    else ""
  in
    (normalized_score, logs)
  end;

  fun score_state st proof_text = score (List.length (Proof.the_facts st)) proof_text
  fun score_thm thms proof_text = score (List.length thms) proof_text
end;
