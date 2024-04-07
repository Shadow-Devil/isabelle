(*  Title:      HOL/Tools/Proof_Improve/proof_improve_config_manager.ML
    Author:     Daniel Lipkin, TU Muenchen

Contains all configurations of Proof_Improve
*)

signature PROOF_IMPROVE_CONFIG_MANAGER =
sig
  type config
  val default_config : config
  val get_weight_length : unit -> real
  val get_weight_lemma : unit -> real
  val get_weight_entropy : unit -> real
  val get_weight_depth : unit -> real
  val get_weight_symbol_to_text_ratio : unit -> real
  val get_weight_apply : unit -> real
  val get_weight_used_methods : unit -> real
  val get_max_length : unit -> int
  val get_max_lemma : unit -> int
  val get_max_entropy : unit -> real
  val get_max_depth : unit -> int
  val get_max_apply : unit -> int
  val get_normalize_mode : unit -> string
  val get_logging : unit -> bool
end;

structure Proof_Improve_Config_Manager : PROOF_IMPROVE_CONFIG_MANAGER =
struct
datatype config = Config of {
  weight_length : real,
  weight_lemma : real,
  weight_entropy : real,
  weight_symbol_to_text_ratio : real,
  weight_depth : real,
  weight_apply : real,
  weight_used_methods: real,
  max_length : int,
  max_lemma : int,
  max_entropy : real,
  max_depth : int,
  max_apply : int,
  normalize_mode : string,
  logging : bool
}

val default_config = Config {
  weight_length = 0.25,
  weight_lemma = 0.1,
  weight_entropy = 0.05,
  weight_symbol_to_text_ratio = 0.05,
  weight_depth = 0.14,
  weight_apply = 0.4,
  weight_used_methods = 0.01,

  max_length = 1000,
  max_lemma = 10,
  max_entropy = 8.0,
  max_depth = 5,
  max_apply = 6,
  normalize_mode = "linear", (*can be log/linear*)
  logging = true
}

fun get_weight_length () = let val Config cfg = default_config in #weight_length cfg end
fun get_weight_lemma () = let val Config cfg = default_config in #weight_lemma cfg end
fun get_weight_entropy () = let val Config cfg = default_config in #weight_entropy cfg end
fun get_weight_symbol_to_text_ratio () = let val Config cfg = default_config in
  #weight_symbol_to_text_ratio cfg end
fun get_weight_depth () = let val Config cfg = default_config in #weight_depth cfg end
fun get_weight_apply () = let val Config cfg = default_config in #weight_apply cfg end
fun get_weight_used_methods () = let val Config cfg = default_config in #weight_used_methods cfg end
fun get_max_length () = let val Config cfg = default_config in #max_length cfg end
fun get_max_lemma () = let val Config cfg = default_config in #max_lemma cfg end
fun get_max_entropy () = let val Config cfg = default_config in #max_entropy cfg end
fun get_max_depth () = let val Config cfg = default_config in #max_depth cfg end
fun get_max_apply () = let val Config cfg = default_config in #max_apply cfg end
fun get_normalize_mode () = let val Config cfg = default_config in #normalize_mode cfg end
fun get_logging () = let val Config cfg = default_config in #logging cfg end
end;