(*  Title:      HOL/Tools/Proof_Improve/proof_improve.ML
    Author:     Felix Schnabel, TU Muenchen

This module provides utilities for improving Isabelle proofs.
*)
signature PROOF_IMPROVE_DEPENDENCY_ANALYSER =
sig
  type outcome = {all_dependencies: string list, classified: Try0.try0_params}
  val analyse_dependencies : Proof.context -> thm list -> outcome

end;

structure Proof_Improve_Dependency_Analyser: PROOF_IMPROVE_DEPENDENCY_ANALYSER =
struct
type outcome = {all_dependencies: string list, classified: Try0.try0_params};

fun all_xs_not_in_ys (xs: thm list) (ys: thm list) =
  null (inter (fn (x, y) => Thm.eq_thm_prop (x, y)) xs ys);

fun trimr_non_alpha s = s
  |> Substring.full
  |> Substring.dropr (not o Char.isAlpha)
  |> Substring.string;

fun thm_dependencies_internal' (thy: theory) (limit: int option) (thm: thm) =
  let
    fun deps lvl (i, thm_node) = let val thm_id = Proofterm.thm_id (i, thm_node) in
          (case Global_Theory.lookup_thm_id thy thm_id of
            SOME (thm_name, _) => [(lvl, thm_name)]
          | NONE => (if is_some limit andalso lvl > the limit
                    then [] (*Exit early if lvl is reached*)
                    else maps (deps (lvl + 1)) (Proofterm.thm_node_thms thm_node))
      ) end;
  in
      (maps (deps 0) o Thm.thm_deps o Thm.transfer thy) thm
  end;

fun thm_dependencies' thy thms = maps (thm_dependencies_internal' thy (SOME 4)) thms
    |> sort (int_ord o apply2 fst)
    |> map (#2)
    |> distinct (op =);

fun claset_member net xs = exists (fn x => Item_Net.member net (x, (x, []), (x, []))) xs;

fun is_standard_SIs xs claset = claset_member (claset |> #safeIs) xs;
fun is_standard_Is xs claset = claset_member (claset |> #unsafeIs) xs;
fun is_standard_SEs xs claset = claset_member (claset |> #safeEs) xs;
fun is_standard_Es xs claset = claset_member (claset |> #unsafeEs) xs;
fun is_standard_SDs xs claset = xs 
  |> filter (fn x => not (has_fewer_prems 1 x)) 
  |> map Tactic.make_elim
  |> (claset_member (claset |> #safeEs));
fun is_standard_Ds xs claset = xs 
  |> filter (fn x => not (has_fewer_prems 1 x))
  |> map Tactic.make_elim
  |> claset_member (claset |> #unsafeEs);

fun analyse_dependencies (ctxt: Proof.context) thms =
  let
        val thy = Proof_Context.theory_of ctxt;
        val thy_name = Context.theory_base_name thy ^ ".";
        val ctxt_suppressed_warnings = Context_Position.set_visible false ctxt;
        val simps = ctxt |> Raw_Simplifier.simpset_of |> Raw_Simplifier.dest_simps;
        val claset = Classical.get_cs (Context.Proof ctxt) |> Classical.rep_cs;
        val facts = Global_Theory.facts_of thy;

        (* if for all used thm simplifications there is a simplification in the simpset
           then it should remove it (since it is unnecessary) *)
        fun is_simp xs = not (all_xs_not_in_ys xs simps);
        fun exists_in_facts_table name = Facts.lookup (Context.Theory thy) (Global_Theory.facts_of thy) name |> Option.isSome
        fun is_hidden name = Name_Space.extern ctxt (Facts.space_of facts) name |> Long_Name.is_hidden;
        fun is_protect name = (name = "Pure.protectI" orelse name = "Pure.protectD")

        val thm_deps = thm_dependencies' thy thms
                |> filter (fn name => exists_in_facts_table name andalso not (is_hidden name) andalso not (is_protect name))
                |> map (fn name => (if String.isPrefix thy_name name then unprefix thy_name name else name, Global_Theory.get_thms thy name));
        
        val thm_deps_without_standard_simps = thm_deps |> filter (fn (_, thm_deps)  => 
          let
            (* this can be empty which will also filter it out *)
            val thm_deps_as_simps = thm_deps |> maps (Raw_Simplifier.mksimps ctxt);
          in
            not (null thm_deps_as_simps) andalso not (is_simp thm_deps_as_simps)
        end);
        fun is_intro (name, used_thms) = 
            String.isSuffix (trimr_non_alpha "I") name andalso 
            not (is_standard_SIs used_thms claset) andalso 
            not (is_standard_Is used_thms claset) andalso
            can (fn x => Classical.addIs (ctxt_suppressed_warnings, x)) used_thms;

        fun is_elim (name, used_thms) = 
            String.isSuffix (trimr_non_alpha "E") name andalso 
            not (is_standard_SEs used_thms claset) andalso 
            not (is_standard_Es used_thms claset) andalso
            can (fn x => Classical.addEs (ctxt_suppressed_warnings, x)) used_thms;

        fun is_dest (name, used_thms) = 
          String.isSuffix (trimr_non_alpha "D") name andalso 
          not (is_standard_SDs used_thms claset) andalso 
          not (is_standard_Ds used_thms claset) andalso
          can (fn x => Classical.addDs (ctxt_suppressed_warnings, x)) used_thms;


        val intros = thm_deps_without_standard_simps |> filter is_intro;
        val elims = thm_deps_without_standard_simps |> filter is_elim;
        val dest = thm_deps_without_standard_simps |> filter is_dest;

        val thm_deps_without_intro_elim_dest = thm_deps_without_standard_simps |> filter (fn (_, simp_thms) =>
          all_xs_not_in_ys simp_thms (intros |> maps #2) andalso
          all_xs_not_in_ys simp_thms (elims |> maps #2) andalso
          all_xs_not_in_ys simp_thms (dest |> maps #2) andalso
          not (is_standard_SIs simp_thms claset) andalso 
          not (is_standard_Is simp_thms claset) andalso
          not (is_standard_SEs simp_thms claset) andalso 
          not (is_standard_Es simp_thms claset) andalso
          not (is_standard_SDs simp_thms claset) andalso 
          not (is_standard_Ds simp_thms claset)
        );
  in
    {
      all_dependencies = thm_deps_without_standard_simps |> map #1,
      classified = {
        simp = thm_deps_without_intro_elim_dest |> map #1,
        intro = intros |> map #1,
        elim = elims |> map #1,
        dest = dest |> map #1
        }
    }
  end;
end;