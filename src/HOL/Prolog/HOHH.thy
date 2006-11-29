(*  Title:    HOL/Prolog/HOHH.thy
    ID:       $Id$
    Author:   David von Oheimb (based on a lecture on Lambda Prolog by Nadathur)
*)

header {* Higher-order hereditary Harrop formulas *}

theory HOHH
imports HOL
uses "prolog.ML"
begin

method_setup ptac =
  {* Method.thms_args (Method.SIMPLE_METHOD' o Prolog.ptac) *}
  "Basic Lambda Prolog interpreter"

method_setup prolog =
  {* Method.thms_args (Method.SIMPLE_METHOD o Prolog.prolog_tac) *}
  "Lambda Prolog interpreter"

consts

(* D-formulas (programs):  D ::= !x. D | D .. D | D :- G | A            *)
  Dand        :: "[bool, bool] => bool"         (infixr ".." 28)
  Dif        :: "[bool, bool] => bool"         (infixl ":-" 29)

(* G-formulas (goals):     G ::= A | G & G | G | G | ? x. G
                               | True | !x. G | D => G                  *)
(*Dand'         :: "[bool, bool] => bool"         (infixr "," 35)*)
  Dimp          :: "[bool, bool] => bool"         (infixr "=>" 27)

translations

  "D :- G"      =>      "G --> D"
  "D1 .. D2"    =>      "D1 & D2"
(*"G1 , G2"     =>      "G1 & G2"*)
  "D => G"      =>      "D --> G"

end
