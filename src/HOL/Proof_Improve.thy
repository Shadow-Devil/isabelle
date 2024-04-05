(*  Title:      HOL/Proof_Improve.thy
    Author:     Daniel Lipkin, TU Muenchen
*)

section \<open>Proof Improve: Semi-Automatic Proof Improvement\<close>

theory Proof_Improve
  imports Sledgehammer
begin


ML_file \<open>Tools/Proof_Improve/proof_improve_changes.ML\<close>
ML_file \<open>Tools/Proof_Improve/proof_improve_config_manager.ML\<close>
ML_file \<open>Tools/Proof_Improve/proof_improve_finder.ML\<close>
ML_file \<open>Tools/Proof_Improve/proof_improve_scorer.ML\<close>
ML_file \<open>Tools/Proof_Improve/proof_improve.ML\<close>

end