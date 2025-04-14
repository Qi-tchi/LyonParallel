module Homo = GraphHomomorphism
(* module MGraph = struct  *)
  include MGraph
  let iso g g' = 
    let homos = Homo.homSet g g' in
    List.exists Homo.isIso homos
  let propreSubgraphs = propreSubgraphs
(* end *)

let%expect_test "" = 
  let x=MGraph.fromList [1;2;3] [(1,"a",2,1);(2,"a",3,2)] in
  let g = MGraph.fromList [1;2;3] [] in
  let y=MGraph.fromList [4;5;6] [(4,"a",5,7);(5,"a",6,10)] in
  print_endline ( iso x g |> string_of_bool);
  print_endline ( iso g x |> string_of_bool);
  print_endline ( iso y x |> string_of_bool);
  print_endline ( iso x y |> string_of_bool);
  [%expect{|
    false 
    false
    true
    true
  |}]
 