(*  Title:      HOL/Tools/Proof_Improve/proof_improve_changes.ML
    Author:     Daniel Lipkin, TU Muenchen

Datatype to track changes by proof_improve
*)

signature PROOF_IMPROVE_CHANGES =
sig
  type proof_changes
  val create : unit -> proof_changes
  val add_change : string * string * Position.T -> proof_changes -> proof_changes
  val add_unsuccessful_call : proof_changes -> proof_changes
  val to_string : proof_changes -> string
end;

structure Proof_Improve_Changes : PROOF_IMPROVE_CHANGES =
struct

  datatype proof_change = ProofChange of { prev_proof: string, changed_proof: string,
    position: Position.T }
  datatype proof_changes = ProofChanges of { changes: proof_change list, total_proofs: int,
    successful_changes: int }

  fun create () = ProofChanges { changes = [], total_proofs = 0, successful_changes = 0 }

  fun add_change (prev_proof, changed_proof, position) (ProofChanges {changes, total_proofs,
      successful_changes}) =
    let
      val new_change = ProofChange {prev_proof = prev_proof, changed_proof = changed_proof,
        position = position}
    in
      ProofChanges { changes = new_change :: changes, total_proofs = total_proofs + 1,
        successful_changes = successful_changes + 1}
    end;

  fun add_unsuccessful_call (ProofChanges {changes, total_proofs, successful_changes}) =
      ProofChanges { changes = changes, total_proofs = total_proofs + 1,
        successful_changes = successful_changes }

  fun proof_change_compare (ProofChange {position = pos1, ...})
  (ProofChange {position = pos2, ...}) =
    case (Position.line_of pos1, Position.line_of pos2) of
      (SOME l1, SOME l2) => Int.compare (l1, l2)
    | (SOME _, NONE) => GREATER
    | (NONE, SOME _) => LESS
    | (NONE, NONE) => EQUAL

  fun insert_sorted (x, []) = [x]
    | insert_sorted (x, y::ys) =
        if proof_change_compare x y = LESS then
          x :: y :: ys
        else
          y :: insert_sorted (x, ys)

  fun sort_proof_changes changes = List.foldl (fn (x, acc) => insert_sorted (x, acc)) [] changes

fun count_lines s =  1 + List.length (List.filter (fn x => x = #"\n") (String.explode s))

fun is_subset (ProofChange {position = pos1, ...})
              (ProofChange {position = pos2, prev_proof = proof2, ...}) =
    case (Position.line_of pos1, Position.line_of pos2) of
        (SOME start_line1, SOME start_line2) =>
            let
                val end_line2 = start_line2 + count_lines proof2
            in
                start_line1 >= start_line2 andalso start_line1 <= end_line2
            end
      | _ => false

fun to_string (ProofChanges {changes, total_proofs, successful_changes}) =
  let
    val sorted_changes = sort_proof_changes changes

    fun is_subset_of_prev [] = []
      | is_subset_of_prev [x] = [x]
      | is_subset_of_prev (x::y::xs) =
          if is_subset y x then
            is_subset_of_prev (x::xs)
          else
            x :: is_subset_of_prev (y::xs)

    val non_subsets = is_subset_of_prev sorted_changes
    val subsets_count = length sorted_changes - length non_subsets
    val non_subsets_count = length non_subsets

    fun proof_change_tostring (ProofChange {prev_proof, changed_proof, position}) =
  let
    val start_line_str = (case Position.line_of position of
                           NONE => "Unknown"
                         | SOME line => Int.toString line)

    val end_line_str = (case Position.line_of position of
                         NONE => ""
                         | SOME line => "-" ^ Int.toString (line + count_lines prev_proof - 1))

    val line_range = "Lines " ^ start_line_str ^ end_line_str
  in
    "(Prev: " ^ prev_proof ^ "\nChanged: " ^ changed_proof ^ "\n " ^ line_range ^ ")\n"
  end;

    val changes_str = map proof_change_tostring non_subsets

    val stats = "Total Proofs: " ^ Int.toString total_proofs ^
                ", Successful Changes: " ^ Int.toString successful_changes ^
                ",\nChanges that would be subproofs of others: " ^ Int.toString subsets_count ^
                ", Effective Changes: " ^ Int.toString non_subsets_count
  in
    String.concatWith "\n" changes_str ^ "\n" ^ stats
  end;
end;