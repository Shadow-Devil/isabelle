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

fun get_thms (st: Proof.state) (st': Toplevel.state): (string * thm list) list =
  let
    val get_facts: Toplevel.state -> Facts.T  = Proof_Context.facts_of o Proof.context_of o Toplevel.proof_of
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
    val generous_timeout = Time.scale 1000.0 timeout

    fun run ({pre, spans, pos, post, ...} : Mirabelle.command) : string =
      let
        (* See also: mirabelle_metis.ML *)
        val ctxt = Toplevel.context_of post;
        val thy = Proof_Context.theory_of ctxt;
        val facts = Global_Theory.facts_of thy;
        val ctxt_suppressed_warnings = Context_Position.set_visible false ctxt;
        val simps = ctxt |> Raw_Simplifier.simpset_of |> Raw_Simplifier.dest_simps;

        val claset = Classical.get_cs (Context.Proof @{context}) |> Classical.rep_cs;

        fun claset_member net xs = exists (fn x => Item_Net.member net (x, (x, []), (x, []))) xs;
        
        fun is_standard_SIs xs = claset_member (claset |> #safeIs) xs;
        fun is_standard_Is xs = claset_member (claset |> #unsafeIs) xs;
        fun is_standard_SEs xs = claset_member (claset |> #safeEs) xs;
        fun is_standard_Es xs = claset_member (claset |> #unsafeEs) xs;
        fun is_standard_SDs xs = xs 
          |> filter (fn x => not (has_fewer_prems 1 x)) 
          |> map Tactic.make_elim
          |> (claset_member (claset |> #safeEs));
        fun is_standard_Ds xs =xs 
          |> filter (fn x => not (has_fewer_prems 1 x))
          |> map Tactic.make_elim
          |> claset_member (claset |> #unsafeEs);

        val thms = get_thms pre post |> maps snd

        (* if for all used thm simplifications there is a simplification in the simpset
           then it should remove it (since it is unnecessary) *)
        fun is_simp thm_deps_as_simps = thm_deps_as_simps |> forall (fn x => simps |> exists (fn y => Thm.eq_thm_prop (x, y)));
        fun exists_in_facts_table name = Facts.lookup (Context.Theory thy) (Global_Theory.facts_of thy) name |> Option.isSome
        fun is_hidden name = Name_Space.extern ctxt (Facts.space_of facts) name |> Long_Name.is_hidden;
        fun is_protect name = (name = "Pure.protectI" orelse name = "Pure.protectD")

        val thm_deps = Thm_Deps.thm_deps thy thms |> map (fn x => x |> snd |> fst)
                        |> filter (fn name => exists_in_facts_table name andalso not (is_hidden name) andalso not (is_protect name))
                        |> map (fn name => (name, Global_Theory.get_thms thy name));

        val thm_deps_without_standard_simps = thm_deps |> filter (fn (_, thm_deps)  => 
          let
            val thm_deps_as_simps = thm_deps |> maps (Raw_Simplifier.mksimps ctxt);
          in
            not (is_simp thm_deps_as_simps)
        end);
        fun is_intro (name, used_thms) = 
            String.isSuffix "I" name andalso 
            not (is_standard_SIs used_thms) andalso 
            not (is_standard_Is used_thms) andalso
            can (fn x => Classical.addIs (ctxt_suppressed_warnings, x)) used_thms;

        fun is_elim (name, used_thms) = 
            String.isSuffix "E" name andalso 
            not (is_standard_SEs used_thms) andalso 
            not (is_standard_Es used_thms) andalso
            can (fn x => Classical.addEs (ctxt_suppressed_warnings, x)) used_thms;

        fun is_dest (name, used_thms) = 
          String.isSuffix "D" name andalso 
          not (is_standard_SDs used_thms) andalso 
          not (is_standard_Ds used_thms) andalso
          can (fn x => Classical.addDs (ctxt_suppressed_warnings, x)) used_thms;


        val intros = thm_deps_without_standard_simps |> filter is_intro;
        val elims = thm_deps_without_standard_simps |> filter is_elim;
        val dest = thm_deps_without_standard_simps |> filter is_dest;

        val thm_deps_without_intro_elim_dest = thm_deps_without_standard_simps |> filter (fn (name1, used_thms) =>
          intros |> forall (fn (name2, _) => name1 <> name2) andalso
          elims |> forall (fn (name2, _) => name1 <> name2) andalso
          dest |> forall (fn (name2, _) => name1 <> name2) andalso 
          not (is_standard_SIs used_thms) andalso 
          not (is_standard_Is used_thms) andalso
          not (is_standard_SEs used_thms) andalso 
          not (is_standard_Es used_thms) andalso
          not (is_standard_SDs used_thms) andalso 
          not (is_standard_Ds used_thms)
        );
        val thms_names = Mirabelle.theorems_of_sucessful_proof post |>
                          map Thm.derivation_name;

        val proof_text = get_content spans
        val outcome =
          if proof_text = "" then
            Unknown "segment could not be matched\n"
          else
            Timeout.apply generous_timeout proof_improve pre proof_text {
              simp = thm_deps_without_intro_elim_dest |> map #1,
              intro = intros |> map #1,
              elim = elims |> map #1,
              dest = dest |> map #1
            }
        val current_data = Synchronized.value data
        val updated_data =
          case outcome of
            FoundAlternative (found_proof, _) =>
               add_change (proof_text, found_proof, pos) current_data
            | _ =>
               add_unsuccessful_call current_data
      in
        Synchronized.change data (fn _ => updated_data);
        "Outcome: " ^ string_of_outcome outcome ^ "\n" ^
        "Thms (via Mirabelle function): " ^ @{make_string} thms_names ^ "\n" ^
        "Current Thm: " ^ @{make_string} thms ^ "\n" ^
        "Filtered dependencies: " ^ @{make_string} (thm_deps |> map #1) ^ "\n"
      end

    fun finalize () : string = to_string (Synchronized.value data)
  in
    ("", {run = run, finalize = finalize})
  end

val () = Mirabelle.register_action "proof_improve" make_action
end;