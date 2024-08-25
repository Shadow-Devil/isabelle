(*  Title:      HOL/Tools/Proof_Improve/proof_improve_finder.ML
    Author:     Daniel Lipkin, TU Muenchen

Finding proof alternatives using Sledgehammer and try0.
*)

signature PROOF_IMPROVE_FINDER =
sig
  val find: Proof.state -> Proof_Improve_Dependency_Analyser.outcome -> 
            string * (int * string) option
  val find_old: Proof.state -> string * (int * string) option
end;

structure Proof_Improve_Finder: PROOF_IMPROVE_FINDER =
struct

fun parse_result (result: string) : string =
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

(* final list is 2^(length xs) long e.g. [[], [1], [2], [3], [1, 2], [1, 3], ...] *)
fun powerset []: 'a list list = [[]]
  | powerset (x::xs) =
      let
        val rest_subsets = powerset xs
      in
         rest_subsets @ (map (fn rest => rest @ [x]) rest_subsets)
      end;

(* final list is length xs long e.g. [[], [1], [1, 2]] *)
fun take_n_subsets xs = 0 upto (length xs) -1 |> map (fn i => take i xs)

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
    fun subsets xs = if length xs < 5 then powerset (rev xs) else 
                     if length xs < 20 then take_n_subsets xs else [[], xs]
    val simp_sets = subsets simp;
    val intro_sets = subsets intro;
    val elim_sets = subsets elim;
    val dest_sets = subsets dest;
    fun apply_try0 [simp_set, intro_set, elim_set, dest_set] = 
      (case Try0.generic_try0 Try0.Non_Interactive (SOME timeout) {
        simp = simp_set,
        intro = intro_set,
        elim = elim_set,
        dest = dest_set
      } st of
        (true, (name, [message])) => 
          let 
            val parsed_message = parse_result message;
          in 
            if String.isSubstring "apply" parsed_message then NONE else
            SOME ((name, parsed_message), {
                simp = simp_set, 
                intro = intro_set, 
                elim = elim_set, 
                dest = dest_set})
          end 
      | _ => NONE)
     | apply_try0 _ = NONE;
     val possible_combinations = cartesian_product [simp_sets, intro_sets, elim_sets, dest_sets];
  in
     (length possible_combinations, possible_combinations |> get_index apply_try0)
end;

fun run_try0 (st: Proof.state) classified = 
  case proof_search st classified (Time.fromSeconds 4) of
    (possible_combinations, SOME (calls_made, ((name, message), {simp, intro, elim, dest}))) =>
      let
        val log = space_implode " " [
          "Found by Try0: " ^ name,
          "with simp:", Int.toString (length simp),
          "intro:", Int.toString (length intro),
          "elim:", Int.toString (length elim),
          "dest:", Int.toString (length dest) ^ ".",
          Int.toString (calls_made + 1) ^ " calls were made",
          "of total:", Int.toString possible_combinations]
      in
        (log ^ "\n", SOME (0 (*length simp + length intro + length elim + length dest*), message))
      end
  | (possible_combinations, NONE) => (
    "Try0 found nothing after " ^ Int.toString possible_combinations ^ " calls\n", NONE)

fun run_sledgehammer (st: Proof.state) all_dependencies = 
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

    val fact_override = {
      add = map (fn thm => (Facts.named thm, [])) all_dependencies, del = [], only = true}
    val (timing, (_, (outcome, try_this))) = Timing.timing (Sledgehammer.run_sledgehammer 
      sledgehammer_timeout_params Sledgehammer_Prover.Normal NONE 1  fact_override) st 
      |> apfst (Time.toMilliseconds o #elapsed)
    val failed_result = ("Sledgehammer failed after " ^ Int.toString timing ^ "ms\n", NONE)
in
  case outcome of
      Sledgehammer.SH_Some (prover_result, _) =>
        (case #outcome prover_result of
           NONE =>
           let
             val facts = #used_facts prover_result
             val result = parse_result try_this
           in
             if String.isSubstring "failed" result orelse String.isSubstring "apply" result then
               failed_result
             else
               ("Sledgehammer found after " ^ Int.toString timing ^ "ms\n", 
                 SOME (0(*List.length facts*), result))
           end
         | SOME _ => failed_result)
    | _ => failed_result
end;

fun find_old (st: Proof.state) = case run_sledgehammer st [] of
    (log, SOME result) => (log, SOME result)
  | (log, NONE) => (log, NONE)

fun find (st: Proof.state) {all_dependencies, classified} =
  case run_try0 st {simp = [], intro = [], elim = [], dest = []} of
    (log1, SOME result) => (log1, SOME result)
  | (log1, _) =>
  case run_sledgehammer st all_dependencies of
    (log2, SOME result) => (log1 ^ log2, SOME result)
  | (log2, _) =>
  case run_try0 st classified of
    (log3, SOME result) => (log1 ^ log2 ^ log3, SOME result)
  | (log3, NONE) => (log1 ^ log2 ^ log3, NONE)
end;
