(*  Title:      HOL/Tools/try0.ML
    Author:     Jasmin Blanchette, TU Muenchen

Try a combination of proof methods.
*)

signature TRY0 =
sig
  type try0_params = {
    simp : string list,
    intro : string list,
    elim : string list,
    dest : string list
  }
  val noneN : string
  val silence_methods : bool -> Proof.context -> Proof.context
  val try0 : Time.time option -> string list * string list * string list * string list ->
    Proof.state -> bool
  datatype mode = Auto_Try | Try | Normal | Non_Interactive;
  val generic_try0 : mode -> Time.time option -> try0_params
    -> Proof.state -> bool * (string * string list)
end;

structure Try0 : TRY0 =
struct
type try0_params = {
  simp : string list,
  intro : string list,
  elim : string list,
  dest : string list
}

val empty_params = {
  simp = [],
  intro = [],
  elim = [],
  dest = []
}

val noneN = "none";

datatype mode = Auto_Try | Try | Normal | Non_Interactive;

val default_timeout = seconds 5.0;

fun can_apply timeout_opt pre post tac st =
  let val {goal, ...} = Proof.goal st in
    (case (case timeout_opt of
            SOME timeout => Timeout.apply_physical timeout
          | NONE => fn f => fn x => f x) (Seq.pull o tac) (pre st) of
      SOME (x, _) => (Thm.prems_of goal, Thm.prems_of (post x))
    | NONE => (Thm.prems_of goal, Thm.prems_of goal))
  end;

fun apply_generic timeout_opt name all_goals command pre post apply st =
  let val time_start = Time.now () in
    case try (can_apply timeout_opt pre post apply) st 
      of SOME (previous_goals, new_goals) => 
        if length new_goals = length previous_goals then NONE
        else if length new_goals = 0 then
          SOME (name, command, Time.toMilliseconds (Time.now () - time_start), true)
        else if length new_goals < length previous_goals andalso not all_goals then
          SOME (name, command, Time.toMilliseconds (Time.now () - time_start), false)
        else
          NONE
       | NONE => NONE
  end;

fun parse_method keywords s =
  enclose "(" ")" s
  |> Token.explode keywords Position.start
  |> filter Token.is_proper
  |> Scan.read Token.stopper Method.parse
  |> (fn SOME (Method.Source src, _) => src | _ => raise Fail "expected Source");

fun apply_named_method_on_first_goal ctxt =
  parse_method (Thy_Header.get_keywords' ctxt)
  #> Method.method_cmd ctxt
  #> Method.Basic
  #> (fn m => Method.Combinator (Method.no_combinator_info, Method.Then, [m]))
  #> Proof.refine;

fun add_attr_text (NONE, _) s = s
  | add_attr_text (_, []) s = s
  | add_attr_text (SOME x, fs) s =
    s ^ " " ^ (if x = "" then "" else x ^ ": ") ^ space_implode " " fs;

fun attrs_text (sx, ix, ex, dx) {simp, intro, elim, dest} =
  fold add_attr_text [(sx, simp), (ix, intro), (ex, elim), (dx, dest)] "";

fun apply_named_method (name, ((all_goals, run_if_auto_try), attrs)) mode timeout_opt params st =
  if mode <> Auto_Try orelse run_if_auto_try then
    let val attrs = attrs_text attrs params in
      apply_generic timeout_opt name all_goals
        (name ^ attrs |> attrs <> "" ? enclose "(" ")")
        I (#goal o Proof.goal)
        (apply_named_method_on_first_goal (Proof.context_of st) (name ^ attrs)
          #> Seq.filter_results) st
    end
  else
    NONE;

val full_attrs = (SOME "simp", SOME "intro", SOME "elim", SOME "dest");
val clas_attrs = (NONE, SOME "intro", SOME "elim", SOME "dest");
val simp_attrs = (SOME "add", NONE, NONE, NONE);
val metis_attrs = (SOME "", SOME "", SOME "", SOME "");
val no_attrs = (NONE, NONE, NONE, NONE);

(* name * ((all_goals, run_if_auto_try), (simp, intro, elim, dest) *)
val named_methods =
  [("simp", ((false, true), simp_attrs)),
   ("auto", ((true, true), full_attrs)),
   ("blast", ((false, true), clas_attrs)),
   ("metis", ((false, true), metis_attrs)),
   ("argo", ((false, true), no_attrs)),
   ("linarith", ((false, true), no_attrs)),
   ("presburger", ((false, true), no_attrs)),
   ("algebra", ((false, true), no_attrs)),
   ("fast", ((false, false), clas_attrs)),
   ("fastforce", ((false, false), full_attrs)),
   ("force", ((false, false), full_attrs)),
   ("meson", ((false, false), metis_attrs)),
   ("satx", ((false, false), no_attrs)),
   ("order", ((false, true), no_attrs))];

val apply_methods = map apply_named_method named_methods;

fun time_string ms = string_of_int ms ^ " ms";
fun tool_time_string (s, ms) = s ^ ": " ^ time_string ms;

(* Makes reconstructor tools as silent as possible. The "set_visible" calls suppresses "Unification
   bound exceeded" warnings and the like. *)
fun silence_methods debug =
  Config.put Metis_Tactic.verbose debug
  #> not debug ? (fn ctxt =>
      ctxt
      |> Simplifier_Trace.disable
      |> Context_Position.set_visible false
      |> Config.put Unify.unify_trace false
      |> Config.put Argo_Tactic.trace "none"
      |> Proof_Context.background_theory (fn thy =>
          thy
          |> Context_Position.set_visible_global false
          |> Config.put_global Unify.unify_trace false));

fun generic_try0 mode timeout_opt (params: try0_params) st =
  let
    val st = Proof.map_contexts (silence_methods false) st;
    fun trd (_, _, t, _) = t;
    fun fourth (_, _, _, done) = done;
    fun try_method method = method mode timeout_opt params st;
    fun get_message (_, command, ms, done) = "Found proof: " ^ Active.sendback_markup_command
      ((if done then "by" else "apply") ^ " " ^ command) ^
      " (" ^ time_string ms ^ ")";
    val print_step = Option.map (tap (writeln o get_message));
    val get_results =
      if mode = Normal
      then Par_List.map (try_method #> print_step) #> map_filter I #> 
        sort (rev_order o bool_ord o apply2 fourth ||| int_ord o apply2 trd)
      else Par_List.get_some try_method #> the_list;
  in
    if mode = Normal then
      "Trying " ^ space_implode " " (Try.serial_commas "and" (map (quote o fst) named_methods)) ^
      "..."
      |> writeln
    else
      ();
    (case get_results apply_methods of
      [] =>
      (if mode = Normal then writeln "No proof found" else (); (false, (noneN, [])))
    | xs as (name, command, _, done) :: _ =>
      let
        val xs = xs |> map (fn (name, _, n, _) => (n, name))
                    |> AList.coalesce (op =)
                    |> map (swap o apsnd commas);
        val message =
          (case mode of
             Auto_Try => "Auto Try0 found a proof"
           | Try => "Try0 found a proof"
           | Normal => "Try this"
           | Non_Interactive => "Try this") ^ ": " ^ 
              Active.sendback_markup_command ((if done then "by" else "apply") ^ " " ^ command) ^
              (case xs of
                [(_, ms)] => " (" ^ time_string ms ^ ")"
          | xs => "\n(" ^ space_implode "; " (map tool_time_string xs) ^ ")");
      in
        (true, (name, 
                if mode = Auto_Try orelse mode = Non_Interactive 
                then [message]
                else (writeln message; [])))
      end)
  end;

fun try0 timeout_opt (simp, intro, elim, dest) st = 
  fst (generic_try0 Normal timeout_opt {simp = simp, intro = intro, elim = elim, dest = dest} st);

fun try0_trans (params: try0_params) =
  Toplevel.keep_proof
    (ignore o generic_try0 Normal (SOME default_timeout) params o Toplevel.proof_of);

fun merge_attrs 
  {simp = s1, intro = i1, elim = e1, dest = d1}
  {simp = s2, intro = i2, elim = e2, dest = d2} = {
  simp = s1 @ s2, 
  intro = i1 @ i2, 
  elim = e1 @ e2, 
  dest = d1 @ d2
};

fun string_of_xthm (xref, args) =
  Facts.string_of_ref xref ^
  implode (map (enclose "[" "]" o Pretty.unformatted_string_of o Token.pretty_src \<^context>) args);

val parse_fact_refs =
  Scan.repeat (Scan.unless (Parse.name -- Args.colon) (Parse.thm >> string_of_xthm));

val parse_attr =
  Args.$$$ "simp" |-- Args.colon |-- parse_fact_refs >> (fn ss => {simp = ss, intro = [], elim = [], dest = []})
  || Args.$$$ "intro" |-- Args.colon |-- parse_fact_refs >> (fn is => {simp = [], intro = is, elim = [], dest = []})
  || Args.$$$ "elim" |-- Args.colon |-- parse_fact_refs >> (fn es => {simp = [], intro = [], elim = es, dest = []})
  || Args.$$$ "dest" |-- Args.colon |-- parse_fact_refs >> (fn ds => {simp = [], intro = [], elim = [], dest = ds});

fun parse_attrs x =
  (Args.parens parse_attrs
   || Scan.repeat parse_attr >> (fn params => fold merge_attrs params empty_params)) x;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>try0\<close> "try a combination of proof methods"
    (Scan.optional parse_attrs empty_params #>> try0_trans);

val _ =
  Try.tool_setup
   {name = "try0", weight = 30, auto_option = \<^system_option>\<open>auto_methods\<close>,
    body = fn auto => generic_try0 (if auto then Auto_Try else Try) NONE empty_params};

end;
