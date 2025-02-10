(* open Base
open AuxilliaryFunctions  *)
module Homo = GraphHomomorphism
module Gls = GraphRelabelingSystem
module Ugraph = UnlabelledDirectedMultGraph
module Mgraph = MGraph
module LabelSet = Homo.LabelSet  
(* def rewriting system *)  
module DPOrule = struct 
  type t = { 
    l : Homo.t;
    r : Homo.t;
  } 
  let fromHomos l r = 
    assert (Homo.isInj l);
    assert (Homo.isSpan l r);
    {l;r};;
  let compare r r' = 
    let res = Homo.compare r.l r'.l in 
    if res <> 0 then res else 
      Homo.compare r.r r'.r
  
  let fromLists kvs kes lvs les rvs res lhv lhe rhv rhe =
    let l = Homo.fromList kvs kes lvs les lhv lhe in
    let r = Homo.fromList kvs kes rvs res rhv rhe in
  fromHomos l r
  let equal r r' = (compare r r' = 0)
  let lhs r = r.l 
  let rhs r = r.r
  let leftGraph r = lhs r |> Homo.codom
  let rightGraph r = rhs r |> Homo.codom
  let interfaceGraph r = lhs r |> Homo.dom
  let labelsRule {l=l;r=r} = 
    Homo.labels l |> LabelSet.union (Homo.labels r)
  let%expect_test "" = 
    (* grs plump 6.9 *)
    let rg = Mgraph.fromList [1;2;3;4] [(1,"s",3,1);(3,"0",3,2); (2,"s",4,3); (4,"0",4,4)] in
    let lg = Mgraph.fromList [1;2;3] [(1,"s",3,1);(3,"0",3,2); (2,"s",3,3)] in
    let kg = Mgraph.fromList [1;2;3] [(1,"s",3,1);(3,"0",3,2)] in
    let grs_ex69_r1_r = Homo.fromGraphsAndMaps 
      kg rg
      ([(1,1);(2,2);(3,3)]  |> List.to_seq |> Homo.NodeMap.of_seq)
      ([(1,1); (2,2)] |> List.to_seq|> Homo.ArrowMap.of_seq) in  
    let grs_ex69_r1_l = Homo.fromGraphsAndMaps 
      kg lg
      ([(1,1);(2,2);(3,3)]|> List.to_seq |> Homo.NodeMap.of_seq)
      ([(1,1); (2,2)]  |> List.to_seq|> Homo.ArrowMap.of_seq) in
    let grs_ex69_r1 = fromHomos grs_ex69_r1_l grs_ex69_r1_r in
    (* grs : bruggink 2014 ex4 *)
    let bruggink_2014_example_4_l = Homo.fromList
      [1;2] [] 
      [1;2;3] [(1,"a",3,1);(3,"a",2,2)]
      [(1,1);(2,2)] [] in
    let bruggink_2014_example_4_r = Homo.fromList
        [1;2] []
        [1;2;3;4] [(1,"a",3,1);(3,"b",4,2);(4,"a",2,3);]
        [(1,1);(2,2)] [] in
    let bruggink_2014_example_4 = fromHomos bruggink_2014_example_4_l bruggink_2014_example_4_r in
    lhs grs_ex69_r1 |> Homo.equal grs_ex69_r1_l |> Printf.printf "left: %b\n";
    rhs grs_ex69_r1 |> Homo.equal grs_ex69_r1_r |> Printf.printf "right: %b\n";
    leftGraph grs_ex69_r1 |> Mgraph.equal lg |> Printf.printf "left graph: %b\n";
    rightGraph grs_ex69_r1 |> Mgraph.equal rg |> Printf.printf "right graph: %b\n";
    interfaceGraph grs_ex69_r1 |> Mgraph.equal kg |> Printf.printf "interface graph: %b\n";
    equal grs_ex69_r1 grs_ex69_r1 |> Printf.printf "eq grs69 grs69: %b\n";
    equal grs_ex69_r1 bruggink_2014_example_4 |> Printf.printf "eq grs69 ex4: %b\n";
    labelsRule grs_ex69_r1 |> LabelSet.equal (LabelSet.of_list ["s";"0"]) |> Printf.printf "labelsRule grs69: %b\n";
    labelsRule bruggink_2014_example_4 |> LabelSet.equal (LabelSet.of_list ["b";"a"]) |> Printf.printf "labelsRule ex4: %b\n";
    ;[%expect{|
      left: true
      right: true
      left graph: true
      right graph: true
      interface graph: true
      eq grs69 grs69: true
      eq grs69 ex4: false
      labelsRule grs69: true
      labelsRule ex4: true
    |}]
    let toStr rl = 
      Printf.sprintf "left:\n%s\nright:\n%s" 
      (lhs rl |> Homo.toStr) (rhs rl |> Homo.toStr) 
    let toStr_left_interface_right rl = 
      Printf.sprintf "left:\n%s\n\nInterface\n%s\n\nright:\n%s" 
      (lhs rl |> Homo.codom |> MGraph.toStr) (lhs rl |> Homo.dom |> MGraph.toStr) (rhs rl |> Homo.codom |> MGraph.toStr) 
    let fromGlsRule ({lhs;rhs}:Gls.Rule.t) =  
      let ug = lhs |> MGraph.unlabelled in 
      if (Ugraph.equal ug (rhs |> MGraph.unlabelled) |> not) then raise (Invalid_argument "left and right graphs should have the same unlabeled graph");
      let ns = ug |> Ugraph.nodes |> MGraph.NodeSet.elements in
      let k = MGraph.fromList ns [] in
      let hv = List.map (fun n -> (n,n)) ns |> MGraph.NodeMap.of_list in
      let he = MGraph.ArrowMap.empty in
      let lhs = Homo.fromGraphsAndMaps k lhs hv he in
      let rhs = Homo.fromGraphsAndMaps k rhs hv he in
      fromHomos lhs rhs
    let%expect_test _ = 
      let r2_gls = GraphRelabelingSystem.Rule.fromLists [1;2] [(1,"a",1,1);(1,"0",2,2);(2,"X",2,3)] [1;2] [(1,"a",1,1);(1,"1",2,2);(2,"A",2,3)] in
      let r2_grs_transf = r2_gls |> fromGlsRule in
      r2_grs_transf |> toStr |> print_endline;
      let r2_grs = fromLists 
        [1;2] [] 
        [1;2] [(1,"a",1,1);(1,"0",2,2);(2,"X",2,3)] 
        [1;2] [(1,"a",1,1);(1,"1",2,2);(2,"A",2,3)] 
        [(1,1);(2,2)] [] 
        [(1,1);(2,2)] [] in
        Printf.printf "translation gls -> grs correct: %b" (equal r2_grs r2_grs_transf)
    ;[%expect{|
    left:
    dom:
    nodes : [ 1;2 ]
    arrows : [  ]
    codom:
    nodes : [ 1;2 ]
    arrows : [ (1,0,2,2);(1,a,1,1);(2,X,2,3) ]
    hv:[(1,1);(2,2)]
    he:[]
    right:
    dom:
    nodes : [ 1;2 ]
    arrows : [  ]
    codom:
    nodes : [ 1;2 ]
    arrows : [ (1,1,2,2);(1,a,1,1);(2,A,2,3) ]
    hv:[(1,1);(2,2)]
    he:[]
    translation gls -> grs correct: true
    |}]
end;;
include DPOrule
module RuleSet = Set.Make(DPOrule)
module RuleMap = Map.Make(DPOrule)



(* begin test 
let%test_unit "ruleFromList" = [%test_eq:string list] 
  (labelsRule
    (ruleFromList 
      ([1;2],[]) (*g*) 
      ([1;2;3;4],[(1,1,"a",3);(2,3,"b",4);(3,4,"a",2)]) (*h*) 
      [(1,1);(2,2)]  (*hv*)
      [] (*he*)
      
      ([1;2],[]) (*g*) 

      ([1;2;3],[(1,1,"a",3);(2,3,"a",2)]) (*h*) 
      [(1,1);(2,2)]  (*hv*)
      [] (*he*)
    )
   ) ["a";"b"]
  end test  *)

(* type grs = RuleSet.t *)

type grs = RuleSet.t
(* aux function begin *)
(* let generate_complete_graph dim labels = 
  let g = ref [] in
  let vs = List.init dim ~f:(fun i -> i) in
  List.iter 
    ~f:(fun i -> 
        List.iter
            ~f:(fun j -> 
              List.iter ~f:(fun l -> g := (i+1,l,j+1) :: !g) labels)
        vs)
    vs;
  !g *)

  let size grs = RuleSet.cardinal grs 
  let rulesl grs = RuleSet.elements grs

  let labels grs = 
    let ls = rulesl grs |> List.map labelsRule in
    List.fold_right 
    (fun s acc -> LabelSet.union s acc) 
    ls LabelSet.empty
     
  let labels_l grs = labels grs |> LabelSet.elements
let fromGls (gls: Gls.t) = 
  List.map DPOrule.fromGlsRule gls.rules |> RuleSet.of_list
