(*  Title:      HOL/Tools/Proof_Improve/proof_improve_finder.ML
    Author:     Daniel Lipkin, TU Muenchen

Finding proof alternatives using Sledgehammer and try0.
*)

signature PROOF_IMPROVE_FINDER =
sig
  val find: Proof.state -> Proof_Improve_Dependency_Analyser.outcome -> (int * string * string) option
end;

structure Proof_Improve_Finder: PROOF_IMPROVE_FINDER =
struct

fun parse_try0_result (result: string) : string =
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

fun subsets []: 'a list list = [[]]
  | subsets (x::xs) =
      let
        val rest_subsets = subsets xs
      in
         rest_subsets @ (map (fn subset => subset @ [x]) rest_subsets)
      end;

(* Cartesian product of a list of lists *)
fun cartesian_product (xss: 'a list list): 'a list list = 
let 
  fun helper (xs: 'a list) (acc: 'a list list) = acc |> maps (fn a => 
       (map (fn x => a @ [x]) xs));
in
  fold helper xss [[]]
end;

fun proof_search (st: Proof.state) ({simp, intro, elim, dest} : Try0.try0_params) timeout =
  let
    val simp_sets = if length simp < 10 then subsets (rev simp) else [[], simp];
    val intro_sets = if length intro < 10 then subsets (rev intro) else [[], intro];
    val elim_sets = if length elim < 10 then subsets (rev elim) else [[], elim];
    val dest_sets = if length dest < 10 then subsets (rev dest) else [[], dest];
    fun apply_try0 [simp_set, intro_set, elim_set, dest_set] = 
    let
      val _ = writeln ("try0 (" ^ 
        "simp: " ^ space_implode " " (simp_set) ^ 
        " intro: " ^ space_implode " " (intro_set) ^ 
        " elim: " ^ space_implode " " (elim_set) ^ 
        " dest: " ^ space_implode " " (dest_set) ^ ")");
    in
      case Try0.generic_try0 Try0.Non_Interactive (SOME timeout) {
        simp = simp_set, 
        intro = intro_set,
        elim = elim_set,
        dest = dest_set
      } st of
        (true, (name, [message])) => 
          let 
            val parsed_message = parse_try0_result message;
          in 
            if String.isSubstring "apply" parsed_message then NONE else
            SOME ((name, parsed_message), {simp = simp_set, intro = intro_set, elim = elim_set, dest = dest_set})
          end 
      | _ => NONE
    end |
      apply_try0 _ = NONE
    
  in
    cartesian_product [simp_sets, intro_sets, elim_sets, dest_sets] |> get_first apply_try0
end;


fun find (st: Proof.state) {all_dependencies, classified} =
  let
    val params = Sledgehammer_Commands.default_params \<^theory> []
    val four_seconds = Time.fromSeconds 4

    val sledgehammer_timeout_params = {
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

    val fact_override = {add = map (fn thm => (Facts.named thm, [])) all_dependencies, del = [], only = true}
    val (_, (outcome, try_this)) =  Sledgehammer.run_sledgehammer sledgehammer_timeout_params
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
               SOME (0(*List.length facts*), "Sledgehammer", result)
           end
         | SOME _ => NONE)
    | _ => 
      case proof_search st classified four_seconds of
        SOME ((name, message), {simp, intro, elim, dest}) =>
          SOME (0 (*length simp + length intro + length elim + length dest*), 
                "Try0: " ^ name, message)
        | NONE => NONE
  end
end;
