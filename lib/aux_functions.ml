let pp_int_list sep l =
  let x = List.map string_of_int l in
  let s = String.concat sep x in
  Printf.sprintf "%s" s

(* open Core *)
(* 
(* Generate all combinations of size k *)
let rec combinations k = function
  | [] -> if k = 0 then [[]] else []
  | x :: xs ->
    let with_x = List.map (fun rest -> x :: rest) (combinations (k-1) xs)  in
    let without_x = combinations k xs in
    List.append with_x without_x

(* Generate all permutations of a list *)
let rec permutations = function
  | [] -> [ [] ]
  | x :: xs ->
    let perms = permutations xs in
    perms
    |> List.concat_map (fun perm ->
          List.init (fun i ->
            let left = List.take perm i in
            let right = List.drop perm i in
            left @ (x :: right)
          ) (List.length perm + 1) 
        )


(* Main function to generate k-length arrangements *)
let arrangements k l =
  if k < 1 || k > List.length l then []
  else
    combinations k l
    |> List.concat_map ~f:permutations
  
let inj_maps_from_to l1 l2 =
  let k, n = List.length l1, List.length l2 in
  if k > n then [] 
  else begin
    let arrangs = arrangements k l2 in
    List.map 
      ~f:(fun ar -> 
        List.map2 
          ~f:(fun x y -> (x,y)) 
          l1 
          ar 
      ) 
      arrangs
  end
  
  *)


  (* Helper functions *)
let rec take n = function
| [] -> []
| x::xs when n > 0 -> x :: take (n-1) xs
| _ -> []

let rec drop n = function
| [] -> []
| _::xs when n > 0 -> drop (n-1) xs
| xs -> xs
(* 
let list_init n f =
let rec aux i acc =
  if i < 0 then acc
  else aux (i-1) (f i :: acc)
in
aux (n-1) [] *)

(* Generate all permutations of a list *)
let rec permutations = function
| [] -> [ [] ]
| x::xs ->
  let perms = permutations xs in
  List.concat @@ List.map (fun perm ->
    List.init (List.length perm + 1) (fun i ->
      let left = take i perm in
      let right = drop i perm in
      left @ (x :: right)
    )
  ) perms

(* Generate all combinations of size k *)
let rec combinations k = function
| [] -> if k = 0 then [[]] else []
| x::xs ->
  let with_x = List.map (fun rest -> x :: rest) (combinations (k-1) xs) in
  let without_x = combinations k xs in
  with_x @ without_x

(* Main function to generate k-length arrangements *)
let arrangements k l =
if k < 1 || k > List.length l then []
else
  combinations k l
  |> List.concat_map permutations


let inj_maps_from_to l1 l2 =
  let k, n = List.length l1, List.length l2 in
  if k > n then [] 
  else begin
    let arrangs = arrangements k l2 in
    List.map 
      (fun ar -> 
        List.map2 
          (fun x y -> (x,y)) 
          l1 
          ar 
      ) 
      arrangs
  end