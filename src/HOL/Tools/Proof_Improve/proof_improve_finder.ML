(*  Title:      HOL/Tools/Proof_Improve/proof_improve_finder.ML
    Author:     Daniel Lipkin, TU Muenchen

Finding proof alternatives using Sledgehammer.
*)

signature PROOF_IMPROVE_FINDER =
sig
  val find: Proof.state -> string list -> (int * string) option
end;

structure Proof_Improve_Finder: PROOF_IMPROVE_FINDER =
struct

fun parse_try0_result (result: string) : string =
  let
    val prefix = "Auto Try0 found a proof: "
    (*val prefix = "Try this: "*)
    val prefix_len = size prefix

    val result_without_prefix =
      if String.isPrefix prefix result then
        String.extract (result, prefix_len, NONE)
      else
        result

    fun rindex_from (s: string, c: char, i: int) =
      if i < 0 then NONE
      else if String.sub (s, i) = c then SOME i
      else rindex_from (s, c, i - 1)

    val result_without_timing =
      case rindex_from (result_without_prefix, #"(", size result_without_prefix - 1) of
        NONE => result_without_prefix
      | SOME i => String.substring (result_without_prefix, 0, i)

  val result_trimmed =
    if String.isSuffix (result_without_timing) " " then
      String.substring (result_without_timing, 0, size result_without_timing - 1)
    else
      result_without_timing
in
  result_trimmed
end;

fun parse_sledgehammer_result (result: string) : string =
  let
    val prefix = "Try this: "
    val prefix_len = size prefix

    val result_without_prefix =
      if String.isPrefix prefix result then
        String.extract (result, prefix_len, NONE)
      else
        result

    fun rindex_from (s: string, c: char, i: int) =
      if i < 0 then NONE
      else if String.sub (s, i) = c then SOME i
      else rindex_from (s, c, i - 1)

    val result_without_timing =
      case rindex_from (result_without_prefix, #"(", size result_without_prefix - 1) of
        NONE => result_without_prefix
      | SOME i => String.substring (result_without_prefix, 0, i)

  val result_trimmed =
    if String.isSuffix (result_without_timing) " " then
      String.substring (result_without_timing, 0, size result_without_timing - 1)
    else
      result_without_timing
in
  result_trimmed
end;


fun find (st: Proof.state) thms =
  let
  (*  val params = Sledgehammer_Commands.default_params \<^theory> []
    val four_seconds = Time.fromSeconds 4

    val timeout_params = {
      debug = #debug params,
      verbose = #verbose params,
      overlord = #overlord params,
      spy = #spy params,
      provers = #provers params,
      abduce = #abduce params,
      falsify = #falsify params,
      type_enc = #type_enc params,
      strict = #strict params,
      lam_trans = #lam_trans params,
      uncurried_aliases = #uncurried_aliases params,
      learn = #learn params,
      fact_filter = #fact_filter params,
      induction_rules = #induction_rules params,
      max_facts = #max_facts params,
      fact_thresholds = #fact_thresholds params,
      max_mono_iters = #max_mono_iters params,
      max_new_mono_instances = #max_new_mono_instances params,
      max_proofs = #max_proofs params,
      isar_proofs = #isar_proofs params,
      compress = #compress params,
      try0 = #try0 params,
      smt_proofs = #smt_proofs params,
      minimize = #minimize params,
      slices = #slices params,
      timeout = four_seconds,
      preplay_timeout = four_seconds,
      expect = #expect params
    }  

    val fact_override = {add = map (fn thm => (Facts.named thm, [])) thms, del = [], only = true}
    val (_, (outcome, try_this)) =  Sledgehammer.run_sledgehammer timeout_params
      Sledgehammer_Prover.Normal NONE 1 fact_override st
  in
    case outcome of
      Sledgehammer.SH_Some (prover_result, _) =>
        (case #outcome prover_result of
           NONE =>
           let
             val facts = #used_facts prover_result
             val result = parse_sledgehammer_result try_this
           in
             if String.isSubstring "failed" result orelse String.isSubstring "apply" result then
               NONE
             else
               SOME (List.length facts, result)
           end
         | SOME _ => NONE)
    | _ => NONE
  end
*)
    val (successful, (name, messages)) = Try0.generic_try0 Try0.Auto_Try NONE (thms, [], [], []) st
  in
    if successful then
      SOME (length thms, parse_try0_result (the_single messages))
    else NONE
end
end;
