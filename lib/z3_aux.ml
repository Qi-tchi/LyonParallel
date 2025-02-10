(* 
open Z3

(* Function to find a positive linear combination using Z3 *)
let find_positive_combination matrix =
  (* Initialize Z3 context *)
  let cfg = [("model", "true")] in
  let ctx = Z3.mk_context cfg in

  (* Create a Z3 solver *)
  let solver = Z3.Solver.mk_solver ctx None in

  (* Number of rows and columns *)
  let num_rows = List.length matrix in
  let num_cols = match matrix with
    | [] -> 0
    | row :: _ -> List.length row
  in

  (* Create variables c_1, c_2, ..., c_n *)
  let c_vars =
    List.init num_rows (fun i ->
      let name = Printf.sprintf "c_%d" (i + 1) in
      Z3.Arithmetic.Real.mk_const_s ctx name
    )
  in

  (* Add constraints: c_i >= 0 *)
  let non_negative_constraints =
    List.map (fun c ->
      Z3.Boolean.mk_ge ctx (Z3.Arithmetic.Real.mk_numeral_int ctx 0) (c)
    ) c_vars
  in
  Z3.Solver.add solver non_negative_constraints;

  (* Add constraints for each column: sum(c_i * a_ij) >= 0 *)
  List.iter (fun j ->
    let column = List.map (fun row -> List.nth row j) matrix in
    let linear_expr =
      List.fold_left2 (fun acc c a_ij ->
        let term = Z3.Arithmetic.mk_mul ctx [Z3.Arithmetic.Real.of_real ctx (Z3.Arithmetic.Real.mk_numeral_int ctx a_ij); c] in
        Z3.Arithmetic.mk_add ctx [acc; term]
      ) (Z3.Arithmetic.Real.mk_numeral_int ctx 0) c_vars column
    in
    let constraint = Z3.Arithmetic.mk_ge ctx linear_expr (Z3.Arithmetic.Real. mk_numeral_int ctx 0) in
    Z3.Solver.add solver [constraint]
  ) (List.init num_cols (fun i -> i));

  (* Add constraint: at least one v_j > 0 *)
  let positive_constraints =
    List.mapi (fun j _ ->
      let column = List.map (fun row -> List.nth row j) matrix in
      let linear_expr =
        List.fold_left2 (fun acc c a_ij ->
          let term = Z3.Arithmetic.mk_mul ctx [Z3.Arithmetic.Real.of_real ctx (Z3.Arithmetic.Real.mk_numeral_int ctx a_ij); c] in
          Z3.Arithmetic.mk_add ctx [acc; term]
        ) (Z3.Arithmetic.Real.mk_numeral_int ctx 0) c_vars column
      in
      Z3.Boolean.mk_gt ctx linear_expr (Z3.Arithmetic.Real.mk_numeral_int ctx 0)
    ) matrix |> Array.of_list |> Z3.Boolean.mk_or ctx;

  Z3.Solver.add solver [positive_constraints];

  (* Optional: Set an objective, e.g., minimize the sum of c_i *)
  (* Note: Z3 is primarily a satisfiability solver, not an optimizer. *)
  (* For optimization tasks, consider using Z3's Optimize interface *)

  (* Check satisfiability *)
  match Z3.Solver.check solver [] with
  | UNSATISFIABLE ->
      Printf.printf "No feasible combination found.\n";
      None
  | UNKNOWN ->
      Printf.printf "Solver returned UNKNOWN.\n";
      None
  | SATISFIABLE ->
      (* Extract model *)
      let model = Z3.Solver.get_model solver |> Option.get in
      let coefficients =
        List.map (fun c ->
          match Z3.Model.eval model c true with
          | Some value ->
              (match Z3.Arithmetic.Real.to_string value with
              | Some s ->
                  (try
                     Some (float_of_string s)
                   with Failure _ -> None)
              | None -> None)
          | None -> None
        ) c_vars
      in
      Some coefficients

(* Example usage *)
let () =
  let matrix = [
    [1; -2; 3];
    [4; 5; -6];
    [-7; 8; 9]
  ] in
  match find_positive_combination matrix with
  | Some combination ->
      Printf.printf "Found combination:\n";
      List.iteri (fun i c ->
        Printf.printf "c_%d = %f\n" (i + 1) c
      ) combination
  | None ->
      Printf.printf "No feasible combination found.\n" *)
