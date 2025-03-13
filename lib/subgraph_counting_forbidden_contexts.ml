module Homo = GraphHomomorphism
module Grs = GraphRewritingSystem
module RuleSet = GraphRewritingSystem.RuleSet
module Rule = GraphRewritingSystem.DPOrule
open Ruler_graph
let (<|) f x = f x 

(*****************************************
          DRX
*****************************************)
let subgraph_of_rk  (rl:Rule.t) rp =
  let im_r_k = rl.r |> Homo.imgOf in
  MGraph.isSubGraphOf rp im_r_k

let%expect_test "" = 
  (* let x = { x=MGraph.fromList [1;2;3] [(1,"a",2,1);(2,"a",3,2)]; fx = None} in *)
  let rho = ConcretGraphRewritingSystems.bruggink_2014_ex_4_rl_1 in
  let subgraphs = rho |> Rule.rightGraph |> MGraph.subGraphs in
  Printf.sprintf "total nb subgraphs : %d " (subgraphs |> List.length) |> print_endline;
  let elim = List.filter (subgraph_of_rk rho) subgraphs in
  Printf.sprintf "elim nb subgraphs : %d " (elim |> List.length) |> print_endline;
  List.iter (fun g -> MGraph.toStr g |> print_endline) elim;
  ;
  [%expect{|
    total nb subgraphs : 34
    elim nb subgraphs : 4
    nodes : [  ]
    arrows : [  ]
    nodes : [ 2 ]
    arrows : [  ]
    nodes : [ 1 ]
    arrows : [  ]
    nodes : [ 1;2 ]
    arrows : [  ]
  |}]
 

let iso_to_x x rp =
  Termination.MGraph.iso rp x
let%expect_test "" = 
  let (x:Ruler_graph.rulerGraph) = { x = MGraph.fromList [1;2;3] [(1,"a",2,1);(2,"a",3,2)]; fx = None} in
  let rho = ConcretGraphRewritingSystems.bruggink_2014_ex_4_rl_1 in
  let subgraphs = rho |> Rule.rightGraph |> MGraph.subGraphs in
  Printf.sprintf "total nb subgraphs : %d " (subgraphs |> List.length) |> print_endline;
  let elim = List.filter (subgraph_of_rk rho) subgraphs in
  Printf.sprintf "nb subgraphs (subgraph of r(K)): %d " (elim |> List.length) |> print_endline;
  let subgraphs = MGraph.GraphSet.diff (subgraphs |>  MGraph.GraphSet.of_list) (elim |> MGraph.GraphSet.of_list) in
   Printf.sprintf "nb subgraphs remained: %d " (subgraphs |> MGraph.GraphSet.cardinal) |> print_endline;
  let elim = MGraph.GraphSet.filter (iso_to_x x.x) subgraphs in
  Printf.sprintf "nb subgraphs that are iso to x: %d " (elim |> MGraph.GraphSet.cardinal) |> print_endline;
  MGraph.GraphSet.iter (fun g -> Printf.sprintf "\n%s\n" (MGraph.toStr g) |> print_string) elim
  ;
  let subgraphs = MGraph.GraphSet.diff (subgraphs) (elim) in
  Printf.sprintf "nb subgraphs remained: %d " (subgraphs |> MGraph.GraphSet.cardinal) |> print_endline;
  [%expect{|
    total nb subgraphs : 34
    nb subgraphs (subgraph of r(K)): 4
    nb subgraphs remained: 30
    nb subgraphs that are iso to x: 0
    nb subgraphs remained: 30
  |}]

let can_construct_pbpo_diagram (x:MGraph.t) h_K'R' r' =
  (* let h_R'R = Homo.inclusion_morph r' (rl |> Rule.rightGraph) in
  let pb,k' = Category_Graph.pullback_cospan_monos ({left=rl.r; right=h_R'R}:Category_Graph.cospan) in *)
  let h_R'Xs = Homo.homSet r' x |> List.filter Homo.isInj in
  (* let h_K'R' = Homo.inclusion_morph k' r' in *)
    (* List.map (fun h_R'X -> 
    MGraph.existPushoutComplementOfInjHomos  *)
    (* if Homo.isComposible (Homo.inclusion_morph k' r') h_R'X |> not then 
      begin
        Printf.sprintf "\nk':\n%s\nr':\n%s\nh_r'x:%s\n" 
          (MGraph.toStr k') (MGraph.toStr r') (Homo.toStr h_R'X) |> print_string
      end else *)
    (* Homo.composition (Homo.inclusion_morph k' r') h_R'X *)
    (* () *)
    (* )  *)
    (* h_R'Xs *)
  let tmp = List.filter_map (Category_Graph.pushoutComplementOfInjHomosWithGraphs h_K'R')
  h_R'Xs in
  (List.is_empty tmp |> not)

let%expect_test "" = 
  let x = { x=MGraph.fromList [1;2;3] [(1,"a",2,1);(2,"a",3,2)]; fx = None} in
  let rho = ConcretGraphRewritingSystems.bruggink_2014_ex_4_rl_1 in
  let subgraphs = rho |> Rule.rightGraph |> MGraph.subGraphs in
  Printf.sprintf "total nb subgraphs : %d " (subgraphs |> List.length) |> print_endline;
  let elim = List.filter (subgraph_of_rk rho) subgraphs in
  Printf.sprintf "nb subgraphs (subgraph of r(K)): %d " (elim |> List.length) |> print_endline;
  let subgraphs = MGraph.GraphSet.diff (subgraphs |>  MGraph.GraphSet.of_list) (elim |> MGraph.GraphSet.of_list) in
   Printf.sprintf "nb subgraphs remained: %d " (subgraphs |> MGraph.GraphSet.cardinal) |> print_endline;
  let elim = MGraph.GraphSet.filter (iso_to_x x.x) subgraphs in
  Printf.sprintf "nb subgraphs that are iso to x: %d " (elim |> MGraph.GraphSet.cardinal) |> print_endline;
  MGraph.GraphSet.iter (fun g -> Printf.sprintf "\n%s\n" (MGraph.toStr g) |> print_string) elim
  ;
  let subgraphs = MGraph.GraphSet.diff (subgraphs) (elim) in
  Printf.sprintf "nb subgraphs remained: %d " (subgraphs |> MGraph.GraphSet.cardinal) |> print_endline;
  let right_graph = rho |> Rule.rightGraph in
  let subgraphs = 
    MGraph.GraphSet.filter 
      (fun rp ->
        let (h_k'r', _) = Category_Graph.pullback_cospan_monos (Homo.inclusion_morph rp right_graph, rho.r ) in
        can_construct_pbpo_diagram x.x h_k'r' rp
        ) 
      subgraphs in
  Printf.sprintf "nb subgraphs remained: %d " (subgraphs |> MGraph.GraphSet.cardinal) |> print_endline;
  MGraph.GraphSet.iter (fun g -> Printf.sprintf "\n%s\n" (MGraph.toStr g) |> print_string) subgraphs
  ;
  [%expect{|
    total nb subgraphs : 34
    nb subgraphs (subgraph of r(K)): 4
    nb subgraphs remained: 30
    nb subgraphs that are iso to x: 0
    nb subgraphs remained: 30
    nb subgraphs remained: 4
 
    nodes : [ 1;2;4 ]
    arrows : [ (1,a,4,1) ]
 
    nodes : [ 1;2;5 ]
    arrows : [ (5,a,2,3) ]
 
    nodes : [ 1;4 ]
    arrows : [ (1,a,4,1) ]
 
    nodes : [ 2;5 ]
    arrows : [ (5,a,2,3) ]
  |}]
let calculateDXR (x:MGraph.t) (rl:Rule.t) : (GraphHomomorphism.t * GraphHomomorphism.t) list = 
  (* assertion : rl injective rule  *)
  assert (Homo.isInj rl.l && Homo.isInj rl.r);
  let rhsGraph = Rule.rightGraph rl in
  (* body *)
  let r's =  
    MGraph.propreSubgraphs rhsGraph 
    (* r' is not a subgraph of r(K) *)
    |> List.filter (fun rp -> subgraph_of_rk rl rp |> not)
       (* (fun r' -> 
          let im_r_k = rl.r |> Homo.imgOf in
          not (MGraph.isSubGraphOf r' im_r_k)) *)
    (* r' is not isomorphic to X *)
    |> List.filter
      (fun rp -> not <| iso_to_x x rp) in
    (* calculate pb *)
    let r's = List.filter_map 
    (fun rp ->
      let (h_k'r', h_k'k) = Category_Graph.pullback_cospan_monos (Homo.inclusion_morph rp (rl |> Rule.rightGraph), rl.r ) in
      if can_construct_pbpo_diagram x h_k'r' rp then Some (h_k'r', h_k'k) 
      else None
      ) 
    r's
    (* pbpo diagram *)
    (* |> List.filter 
        (fun _, rp -> 
        let h_R'R = Homo.inclusion_morph rp (rl |> Rule.rightGraph) in
        let pb,k' = Category_Graph.pullback_cospan_monos ({left=rl.r; right=h_R'R}:Category_Graph.cospan) in 
         can_construct_pbpo_diagram x rl) *)
        in
    r's 

 
let%expect_test "" = 
  let x = { x=MGraph.fromList [1;2;3] [(1,"a",2,1);(2,"a",3,2)]; fx = None} in
  let rho = ConcretGraphRewritingSystems.bruggink_2014_ex_4_rl_1 in
  calculateDXR x.x rho 
  |>
  List.iter (fun (h_k'r', _) -> let g = Homo.codom h_k'r' in Printf.sprintf "\n%s\n" (MGraph.toStr g) |> print_string);
  [%expect{|
    nodes : [ 2;5 ]
    arrows : [ (5,a,2,3) ]

    nodes : [ 1;4 ]
    arrows : [ (1,a,4,1) ]

    nodes : [ 1;2;5 ]
    arrows : [ (5,a,2,3) ]

    nodes : [ 1;2;4 ]
    arrows : [ (1,a,4,1) ]
  |}]




  (*****************************************
          $X$- non increasing rule under phi
*****************************************)
(* condition 1 *)
let double_pullback_diagram_holds rho (phi:Homo.t Homo.GraphHomoMap.t) (h_k'r', h_k'k) =
    (* let r' = Homo.codom h_k'r' in *)
    let h_r'l = 
      match Homo.GraphHomoMap.find_opt h_k'r' phi with
      |None -> assert false 
      |Some h_r'l -> h_r'l 
    in
    Homo.isCommutative [h_k'r'; h_r'l] [h_k'k; rho |> Rule.lhs]
    (* let r = (rho |> Rule.rightGraph) in *)
    (* assert (MGraph.isSubGraphOf r' r);
    let cospan1 =
      let h_r'r = Homo.inclusion_morph r' r in
      Category_Graph.mk_cospan_with_monos h_r'r rho.r in
    let cospan2 =  
      Category_Graph.mk_cospan_with_monos h_r'l rho.l in
    let _, pb_obj1 = Category_Graph.pullback_cospan_monos cospan1 in
    let _, pb_obj2 = Category_Graph.pullback_cospan_monos cospan2 in
    MGraph.equal pb_obj1 pb_obj2 *)

let%expect_test "" = 
  let x = { x=MGraph.fromList [1;2;3] [(1,"a",2,1);(2,"a",3,2)]; fx = None} in
  let rho = ConcretGraphRewritingSystems.bruggink_2014_ex_4_rl_1 in
  let drx = calculateDXR x.x rho in
  let (h_k'r', h_k'k) = List.nth drx 0 in
  (* let r' = Homo.codom h_k'r' in *)
  Printf.sprintf "r'\n%s" (Homo.codom h_k'r'|>MGraph.toStr) |> print_endline ;
  let h_r'l =  Homo.fromList 
                [ 2;5 ]
                [ (5,"a",2,3) ]
                [1;2;3] [(1,"a",3,1);(3,"a",2,2)]
                [(5,3);(2,2)] [(3,2)] in
    (* ignore h_r'l; *)
  let phi = Homo.GraphHomoMap.add h_k'r' h_r'l Homo.GraphHomoMap.empty in
  double_pullback_diagram_holds rho phi (h_k'r', h_k'k) |> Printf.sprintf "double pullback : %b" |> print_endline;
  let h_r'l2 =  Homo.fromList 
  [ 2;5 ]
  [ (5,"a",2,3) ]
  [1;2;3] [(1,"a",3,1);(3,"a",2,2)]
  [(5,1);(2,3)] [(3,1)] in
  (* ignore h_r'l; *)
  let phi2 = Homo.GraphHomoMap.add h_k'r' h_r'l2 Homo.GraphHomoMap.empty in
  double_pullback_diagram_holds rho phi2 (h_k'r', h_k'k) |> Printf.sprintf "double pullback : %b" |> print_endline;
  [%expect{|
    r'
    nodes : [ 2;5 ]
    arrows : [ (5,a,2,3) ]
    double pullback : true
    double pullback : false
  |}]

(* condition 2 *)
let non_clapsing (rho :GraphRewritingSystem.DPOrule.t) drx phi =
  List.for_all (fun (h_k'r', _) ->
    let r' = Homo.codom h_k'r' in
    let h_r'l = Homo.GraphHomoMap.find h_k'r' phi in
    let lk = Homo.imgOf rho.l in
    let im_r = Homo.imgOf rho.r in
    (* assert (MGraph.isSubGraphOf r' (rho.r |> Homo.codom));
    assert (MGraph.isSubGraphOf im_r (rho.r |> Homo.codom)); *)
     (* non clapsing on nodes *)
     let non_clapsing_nodes = (MGraph.NodeSet.for_all
      (fun v ->      
        if MGraph.isNodeOf im_r v then true
        else begin
          Homo.app_hv ~h:h_r'l v |> MGraph.isNodeOf lk |> not
        end)
      (MGraph.nodes r')) in
      (* (Printf.sprintf "non_clapsing_nodes : %b" non_clapsing_nodes) |> print_endline; *)
      (* non clapsing on arrows *)
      let non_clapsing_edges = 
        (MGraph.ArrowSet.for_all
        (fun v ->      
          if MGraph.isArrowOf im_r v then true
          else begin
            Homo.app_he ~h:h_r'l v |> MGraph.isArrowOf lk |> not
          end)
        (MGraph.arrows r')) in
        (* (Printf.sprintf "non_clapsing_edges : %b" non_clapsing_edges) |> print_endline; *)
        non_clapsing_edges && non_clapsing_nodes
  ) 
  drx


  (* condition 3 : edge injective *) 
  let edge_injective drx phi =
    List.for_all2 (fun (h_k'r', _) (h_k'r'2, _) ->
      let r', r'' = Homo.codom h_k'r', Homo.codom h_k'r'2 in
      let h_r'l = Homo.GraphHomoMap.find h_k'r' phi in
      let h_r''l = Homo.GraphHomoMap.find h_k'r'2 phi in
      (* let rk = Homo.imgOf rho.r in *)
        (List.for_all2
        (fun x y ->      
            if MGraph.Arrow.equal x y then true
            else begin
              let x', y' = Homo.app_he ~h:h_r'l x, Homo.app_he ~h:h_r''l x in
              MGraph.Arrow.equal x' y' |> not
            end
        )
        (MGraph.arrows r' |> MGraph.ArrowSet.to_list)
        (MGraph.arrows r'' |> MGraph.ArrowSet.to_list)
        )
    ) 
    drx
    drx

let node_injective_if_isolated_nodes (x:MGraph.t) drx phi =
  if x |> MGraph.isConnected then true 
  else
  List.for_all2 (fun (h_k'r', _) (h_k'r'2, _) ->
    let r', r'' = Homo.codom h_k'r', Homo.codom h_k'r'2 in
    let h_r'l = Homo.GraphHomoMap.find h_k'r' phi in
    let h_r''l = Homo.GraphHomoMap.find h_k'r'2 phi in
      (List.for_all2
      (fun x y ->      
          if MGraph.Node.equal x y then true
          else begin
            let x', y' = Homo.app_hv ~h:h_r'l x, Homo.app_hv ~h:h_r''l x in
            MGraph.Node.equal x' y' |> not
          end
      )
      (MGraph.nodes r' |> MGraph.NodeSet.to_list)
      (MGraph.nodes r'' |> MGraph.NodeSet.to_list)
      )
  ) 
  drx
  drx




let generate_all_phiX (x:MGraph.t) rho : (Homo.t Homo.GraphHomoMap.t) list = 
  let open Base in
  let cartesian_product lists =
    Core.List.fold lists ~init:[[]] 
      ~f:(fun acc list ->
        List.concat_map acc ~f:(fun existing ->
          List.map list ~f:(fun elem -> existing @ [elem])
        )
      ) 
      in
  let generate_combinations pairs =
    let choices = List.map pairs 
        ~f:(fun (x, s) ->
          List.map s ~f:(fun y -> (x, y))
        ) 
    in
    cartesian_product choices
  in
  let drx = calculateDXR x rho in
  let pairs = 
    let left_graph = rho |> Rule.leftGraph in
    List.map 
      ~f:(fun (h_k'r', h_k'k) -> 
          let rp = Homo.codom h_k'r' in
          let h_rpls = Homo.homSet rp left_graph 
            |> List.filter ~f:Homo.isInj
            |> List.filter 
                ~f:(fun h_rpl -> 
                  Homo.isCommutative [h_k'r'; h_rpl] [h_k'k; rho |> Rule.lhs]
                ) in
          h_k'r', h_rpls
          (* rp, h_rpls *)
      )
      drx
  in
  let combinations = generate_combinations pairs in
   List.map 
   ~f:( fun l ->
    Homo.GraphHomoMap.of_list l
   ) combinations 
 
let%expect_test "" = 
  let x = { x=MGraph.fromList [1;2;3] [(1,"a",2,1);(2,"a",3,2)]; fx = None} in
  let rho = ConcretGraphRewritingSystems.bruggink_2014_ex_4_rl_1 in
  let phis = generate_all_phiX x.x rho in
  List.iteri (fun i phiX ->
    print_endline <| Printf.sprintf "phi %d: " i;
    List.iteri (fun j (rp,h_rpl) -> 
      Printf.sprintf "phi i%d j%d:\nr':\n%s\nh_r'l:\n%s" i j 
      ( MGraph.toStr (rp|>Homo.codom)) (Homo.toStr h_rpl) |> print_endline
    )
    (phiX |> Homo.GraphHomoMap.bindings)
  )
  phis;
  [%expect{|
    phi 0:
    phi i0 j0:
    r':
    nodes : [ 1;4 ]
    arrows : [ (1,a,4,1) ]
    h_r'l:
    dom:
    nodes : [ 1;4 ]
    arrows : [ (1,a,4,1) ]
    codom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,a,2,2) ]
    hv:[(1,1);(4,3)]
    he:[(1,1)]
    phi i0 j1:
    r':
    nodes : [ 1;2;4 ]
    arrows : [ (1,a,4,1) ]
    h_r'l:
    dom:
    nodes : [ 1;2;4 ]
    arrows : [ (1,a,4,1) ]
    codom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,a,2,2) ]
    hv:[(1,1);(2,2);(4,3)]
    he:[(1,1)]
    phi i0 j2:
    r':
    nodes : [ 1;2;5 ]
    arrows : [ (5,a,2,3) ]
    h_r'l:
    dom:
    nodes : [ 1;2;5 ]
    arrows : [ (5,a,2,3) ]
    codom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,a,2,2) ]
    hv:[(1,1);(2,2);(5,3)]
    he:[(3,2)]
    phi i0 j3:
    r':
    nodes : [ 2;5 ]
    arrows : [ (5,a,2,3) ]
    h_r'l:
    dom:
    nodes : [ 2;5 ]
    arrows : [ (5,a,2,3) ]
    codom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,a,2,2) ]
    hv:[(2,2);(5,3)]
    he:[(3,2)]
  |}]


let is_x_non_increasing_rule (x:MGraph.t) rho (phiX :Homo.t Homo.GraphHomoMap.t) =
  let drx = calculateDXR x rho in
  (* condition 1 *)
  let cond1 = List.for_all (fun (h_k'r', h_k'k) ->
    double_pullback_diagram_holds rho phiX (h_k'r', h_k'k))
  drx in
  (* (Printf.sprintf "condition1 : %b" cond1) |> print_endline; *)
  (* condition 2 *)
  let cond2 = non_clapsing rho drx phiX in
  (* (Printf.sprintf "condition2 : %b" cond2) |> print_endline; *)
  (* condition 3 *)
  let cond3 = edge_injective drx phiX in
  (* (Printf.sprintf "condition3 : %b" cond3) |> print_endline; *)
  (* condition 4 *)
  let cond4 = node_injective_if_isolated_nodes x drx phiX in
  (* (Printf.sprintf "condition4 : %b" cond3) |> print_endline; *)
  cond1 && cond2 && cond3 && cond4
    
let is_x_non_increasing_rule_forSomePhi x rho =
  (* let drx = calculateDXR x.x rho in *)
  let phis = generate_all_phiX x.x rho in
  List.exists (is_x_non_increasing_rule x.x rho) phis

let%expect_test "" = 
  let x = { x=MGraph.fromList [1;2;3] [(1,"a",2,1);(2,"a",3,2)]; fx = None} in
  let rho = ConcretGraphRewritingSystems.bruggink_2014_ex_4_rl_1 in
  (* let drx = calculateDXR x.x rho in *)
  let phis = generate_all_phiX x.x rho in
  is_x_non_increasing_rule x.x rho (List.nth phis 0) |> Printf.sprintf "is x non increasing : %b" |> print_endline; 
  [%expect{|
    is x non increasing : true
  |}]


(****************************************
           Predictable
*******************************************)
(* predictable : condition 1 *)
(** [generate_occs_with_forbidden_contexts x g] = [(occs_x,occs_x_forbiddened, occs_x_not_forbiddened)] *)
let generate_occs_with_forbidden_contexts x g =
  let occs_contexts = 
    match x.fx with
    | None -> []
    | Some h_x_f -> Homo.occs (h_x_f |> Homo.codom) g
  in
  let occs_x = Homo.occs x.x g in
  let occs_x_forbiddened, occs_x_not_forbiddened = List.partition (fun occ_x -> 
    List.exists 
    (fun occ_f -> 
        Homo.isCommutative [x.fx |> Option.get; occ_f] [occ_x]
      (* MGraph.isSubGraphOf (x |> Homo.imgOf) (f |> Homo.imgOf) *)
      )
    occs_contexts
  ) occs_x in
  occs_x, occs_x_forbiddened, occs_x_not_forbiddened
(* let predictable_condition1 (x:rulerGraph) rho =
  let forbidden_contexts = x.fx |> List.map Homo.codom in
  let occs_forbidden_contexts = 
    List.fold_right 
    (fun f acc ->
      List.append acc 

    )
    forbidden_contexts
    [] *)
(* Condition 2 *)
(* Condition 3 *)
(* Condition 4 *)

let%expect_test "" = 
  let x = {x = MGraph.fromList [1;2;3] [(1,"a",3,1);(3,"a",2,2)]; 
          fx = Some (Homo.fromList [1;2;3] [(1,"a",3,1);(3,"a",2,2)]
          [1;2;3] [(1,"a",3,1);(3,"c",3,3);(3,"a",2,2)]
          [(1,1);(2,2);(3,3)] [(1,1);(2,2)]) } in
  let g = MGraph.fromList [1;2;3;4;7;6] 
    [(1,"a",3,1);(3,"c",3,3);(3,"a",2,2);
        (7,"a",1,4);(2,"a",6,5)
    ]in
  let _,occs_x_forbiddened, occs_x_not_forbiddened = generate_occs_with_forbidden_contexts x g in
  Printf.sprintf "%d occs not forbiddened" (List.length occs_x_not_forbiddened) |> print_endline;
  List.iter (fun o -> Printf.sprintf "%s" (MGraph.toStr (o |> Homo.imgOf)) |> print_endline) occs_x_not_forbiddened;
  Printf.sprintf "%d occs forbiddened" (List.length occs_x_forbiddened) |> print_endline;
  List.iter (fun o -> Printf.sprintf "%s" (MGraph.toStr (o|> Homo.imgOf)) |> print_endline) occs_x_forbiddened
  ;[%expect {|
    2 occs not forbiddened
    nodes : [ 2;3;6 ]
    arrows : [ (2,a,6,5);(3,a,2,2) ]
    nodes : [ 1;3;7 ]
    arrows : [ (1,a,3,1);(7,a,1,4) ]
    1 occs forbiddened
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,a,2,2) ]
  |}];; 
 

let%expect_test "" = 
  let x = MGraph.fromList [1;2] [(1,"node",1,1);(2,"node",2,2)] in
  let h_x_f = Homo.fromList 
    [1;2] [(1,"node",1,1);(2,"node",2,2)]
    [1;3] [(1,"node",1,1);(3,"node",3,2);(1,"edge",3,3);]
    [(1,1);(2,3)] [(1,1);(2,2)]  in
  let x = {x; fx = Some h_x_f} in
  let g = ConcretGraphRewritingSystems.endrullis_2024_exd3_r1l |> Homo.codom in
  let occs,occs_x_forbiddened, occs_x_not_forbiddened = generate_occs_with_forbidden_contexts x g in
  Printf.sprintf "%d occs" (List.length occs) |> print_endline;
  List.iteri (fun i o -> Printf.sprintf "occ %d : %s" i (MGraph.toStr (o |> Homo.imgOf)) |> print_endline) occs;
  print_endline "";

  let occs_context = (Homo.occs (Homo.codom h_x_f) g) in
  Printf.sprintf "%d occs of the context" (List.length occs_context) |> print_endline;
  List.iteri (fun i o -> Printf.sprintf "occ %d : %s" i (MGraph.toStr (o |> Homo.imgOf)) |> print_endline) occs_context;
  print_endline "";

  Printf.sprintf "%d occs not forbiddened" (List.length occs_x_not_forbiddened) |> print_endline;
  List.iteri (fun i o -> Printf.sprintf "occ %d : %s" i (MGraph.toStr (o |> Homo.imgOf)) |> print_endline) occs_x_not_forbiddened;
  Printf.sprintf "%d occs forbiddened" (List.length occs_x_forbiddened) |> print_endline;

  List.iteri (fun i o -> Printf.sprintf "occ %d : %s\n" i (MGraph.toStr (o|> Homo.imgOf)) |> print_endline) occs_x_forbiddened
  ;[%expect {|
    2 occs
    occ 0 : nodes : [ 1;2 ]
    arrows : [ (1,node,1,1);(2,node,2,2) ]
    occ 1 : nodes : [ 1;2 ]
    arrows : [ (1,node,1,1);(2,node,2,2) ]
 
    0 occs of the context
 
    2 occs not forbiddened
    occ 0 : nodes : [ 1;2 ]
    arrows : [ (1,node,1,1);(2,node,2,2) ]
    occ 1 : nodes : [ 1;2 ]
    arrows : [ (1,node,1,1);(2,node,2,2) ]
    0 occs forbiddened
  |}];; 


let%expect_test "" = 
  let x = MGraph.fromList [1;2] [(1,"node",1,1);(2,"node",2,2)] in
  let h_x_f = Homo.fromList 
    [1;2] [(1,"node",1,1);(2,"node",2,2)]
    [1;3] [(1,"node",1,1);(3,"node",3,2);(1,"edge",3,3);]
    [(1,1);(2,3)] [(1,1);(2,2)]  in
  let x = {x; fx = Some h_x_f} in
  let g = ConcretGraphRewritingSystems.endrullis_2024_exd3_r1r |> Homo.codom in
  let occs,occs_x_forbiddened, occs_x_not_forbiddened = generate_occs_with_forbidden_contexts x g in
  Printf.sprintf "%d occs" (List.length occs) |> print_endline;
  List.iteri (fun i o -> Printf.sprintf "occ %d : %s" i (MGraph.toStr (o |> Homo.imgOf)) |> print_endline) occs;
  print_endline "";

  let occs_context = (Homo.occs (Homo.codom h_x_f) g) in
  Printf.sprintf "%d occs of the context" (List.length occs_context) |> print_endline;
  List.iteri (fun i o -> Printf.sprintf "occ %d : %s" i (MGraph.toStr (o |> Homo.imgOf)) |> print_endline) occs_context;
  print_endline "";

  Printf.sprintf "%d occs not forbiddened" (List.length occs_x_not_forbiddened) |> print_endline;
  List.iteri (fun i o -> Printf.sprintf "occ %d : %s" i (MGraph.toStr (o |> Homo.imgOf)) |> print_endline) occs_x_not_forbiddened;
  Printf.sprintf "%d occs forbiddened" (List.length occs_x_forbiddened) |> print_endline;

  List.iteri (fun i o -> Printf.sprintf "occ %d : %s\n" i (MGraph.toStr (o|> Homo.imgOf)) |> print_endline) occs_x_forbiddened
  ;[%expect {|
    2 occs
    occ 0 : nodes : [ 1;3 ]
    arrows : [ (1,node,1,1);(3,node,3,2) ]
    occ 1 : nodes : [ 1;3 ]
    arrows : [ (1,node,1,1);(3,node,3,2) ]
    
    1 occs of the context
    occ 0 : nodes : [ 1;3 ]
    arrows : [ (1,edge,3,3);(1,node,1,1);(3,node,3,2) ]
    
    1 occs not forbiddened
    occ 0 : nodes : [ 1;3 ]
    arrows : [ (1,node,1,1);(3,node,3,2) ]
    1 occs forbiddened
    occ 0 : nodes : [ 1;3 ]
    arrows : [ (1,node,1,1);(3,node,3,2) ]
  |}];; 

let predictable_cond1 x (rho : Rule.t) (mx:Homo.t Homo.GraphHomoMap.t) =
  let lhs, rhs = rho.l, rho.r in
  let l,r = rho |> Rule.leftGraph, rho |> Rule.rightGraph in
  let mono_x_l_forbidden = 
    match generate_occs_with_forbidden_contexts x l with _,occs_x_forbiddened,_ -> occs_x_forbiddened 
    |> Homo.GraphHomoSet.of_list
  in
  let mono_x_r_forbidden = 
      match generate_occs_with_forbidden_contexts x r with _,occs_x_forbiddened,_ -> occs_x_forbiddened 
      |> Homo.GraphHomoSet.of_list
    in
  (* assertion : mx is well defined . can be eliminated after debugging *)
  assert (
  (let dom_mx = Homo.GraphHomoMap.bindings mx |> List.map fst 
      |> Homo.GraphHomoSet.of_list in
   (Homo.GraphHomoSet.subset dom_mx mono_x_l_forbidden) &&
   (Homo.GraphHomoSet.subset mono_x_l_forbidden dom_mx) 
   ) &&
   (let codom_mx = Homo.GraphHomoMap.bindings mx |> List.map snd 
   |> Homo.GraphHomoSet.of_list in
   Homo.GraphHomoSet.subset codom_mx mono_x_r_forbidden)
  );
  (* body *) 
  Homo.GraphHomoSet.for_all 
  (
    fun h_x_l -> 
      (* find ok because of the condition above *)
      let h_x_r = Homo.GraphHomoMap.find h_x_l mx in
      let (_, h_k'_k_left) = Category_Graph.pullback_cospan_monos (h_x_l, lhs) in
      let (_, h_k'_k_right) = Category_Graph.pullback_cospan_monos (h_x_r, rhs) in
      let img1 = h_k'_k_left |> Homo.imgOf in
      let img2 = h_k'_k_right |> Homo.imgOf in
      MGraph.equal img1 img2
  )
  mono_x_l_forbidden
   
let generate_mxs x (rho:Rule.t) =
  (* let lhs, rhs = rho.l, rho.r in *)
  let l,r = rho |> Rule.leftGraph, rho |> Rule.rightGraph in
  let mono_x_l_forbidden = 
    match generate_occs_with_forbidden_contexts x l with _,occs_x_forbiddened,_ -> occs_x_forbiddened 
  in
  let mono_x_r_forbidden = 
      match generate_occs_with_forbidden_contexts x r with _,occs_x_forbiddened,_ -> occs_x_forbiddened 
  in
  let mxs = Aux_functions.inj_maps_from_to mono_x_l_forbidden mono_x_r_forbidden in 
  List.map Homo.GraphHomoMap.of_list mxs

let%expect_test "" = 
  let rho =  ConcretGraphRewritingSystems.bruggink_2014_ex1_rl in
  let x = {x = MGraph.fromList [1;2;3] [(1,"a",3,1);(3,"a",2,2)]; 
          fx = Some (Homo.fromList 
          [1;2;3] [(1,"a",3,1);(3,"a",2,2)]
          [1;2;3] [(1,"a",3,1);(3,"c",3,3);(3,"a",2,2)]
          [(1,1);(2,2);(3,3)] [(1,1);(2,2)]) } in
  let mxs = generate_mxs x rho in
  let (tmp:string list) = List.map Homo.toStr_GraphHomoMap mxs in 
   String.concat "next mx\n" tmp
   |> print_endline
   (* there is no forbiddened X-occurrences *)
  ;[%expect {|
  |}];; 


let%expect_test "" = 
  let l1 = Homo.fromList
    [1;2] [] 
    [1;2;3] [(1,"a",3,1);(3,"c",3,3);(3,"a",2,2)]
    [(1,1);(2,2)] [] in
  let r1 =  Homo.fromList
    [1;2] [] 
    [1;2;3] [(1,"a",3,1);(3,"c",3,3);(3,"a",2,2)]
    [(1,1);(2,2)] [] in 
  let rho = Grs.fromHomos l1 r1 in
  let x = {x = MGraph.fromList [1;2;3] [(1,"a",3,1);(3,"a",2,2)]; 
          fx = Some (Homo.fromList 
          [1;2;3] [(1,"a",3,1);(3,"a",2,2)]
          [1;2;3] [(1,"a",3,1);(3,"c",3,3);(3,"a",2,2)]
          [(1,1);(2,2);(3,3)] [(1,1);(2,2)])} in
  let mxs = generate_mxs x rho in
  Printf.sprintf "|mxs| = %d\n" (List.length mxs) |> print_endline;
  let (tmp:string list) = List.map Homo.toStr_GraphHomoMap mxs in 
   String.concat "next mx\n" tmp
   |> print_endline;
  let mxs_filtered = List.filter (predictable_cond1 x rho) mxs in
    Printf.sprintf "|mxs_filtered| = %d\n" (List.length mxs_filtered) |> print_endline;
  let (tmp:string list) = List.map Homo.toStr_GraphHomoMap mxs_filtered in 
    String.concat "next mx\n" tmp
    |> print_endline;
  ;[%expect {|
  |mxs| = 1

  dom:
  nodes : [ 1;2;3 ]
  arrows : [ (1,a,3,1);(3,a,2,2) ]
  codom:
  nodes : [ 1;2;3 ]
  arrows : [ (1,a,3,1);(3,c,3,3);(3,a,2,2) ]
  hv:[(1,1);(2,2);(3,3)]
  he:[(1,1);(2,2)]
  dom:
  nodes : [ 1;2;3 ]
  arrows : [ (1,a,3,1);(3,a,2,2) ]
  codom:
  nodes : [ 1;2;3 ]
  arrows : [ (1,a,3,1);(3,c,3,3);(3,a,2,2) ]
  hv:[(1,1);(2,2);(3,3)]
  he:[(1,1);(2,2)]

  |mxs_filtered| = 1

  dom:
  nodes : [ 1;2;3 ]
  arrows : [ (1,a,3,1);(3,a,2,2) ]
  codom:
  nodes : [ 1;2;3 ]
  arrows : [ (1,a,3,1);(3,c,3,3);(3,a,2,2) ]
  hv:[(1,1);(2,2);(3,3)]
  he:[(1,1);(2,2)]
  dom:
  nodes : [ 1;2;3 ]
  arrows : [ (1,a,3,1);(3,a,2,2) ]
  codom:
  nodes : [ 1;2;3 ]
  arrows : [ (1,a,3,1);(3,c,3,3);(3,a,2,2) ]
  hv:[(1,1);(2,2);(3,3)]
  he:[(1,1);(2,2)]
  |}];; 

  (* predictable :  condition 2
    for all x->F in Fx ...
  *)

let predictable_cond2 (x:rulerGraph) (rho : Rule.t) mx (mf:Homo.t Homo.GraphHomoMap.t) =
  assert (x.fx |> Option.is_some);
  let h_x_f = x.fx |> Option.get in
  let f = Homo.codom (x.fx |> Option.get) in
  let lhs, rhs = rho.l, rho.r in
  let l,r = rho |> Rule.leftGraph, rho |> Rule.rightGraph in
  let mono_f_l  = Homo.occs f l |> Homo.GraphHomoSet.of_list in
  let mono_f_r  = Homo.occs f r |> Homo.GraphHomoSet.of_list in
  (* assertion : mx is well defined . can be eliminated after debugging *)
  assert (
  (let dom_mf = Homo.GraphHomoMap.bindings mf |> List.map fst 
      |> Homo.GraphHomoSet.of_list in
   (Homo.GraphHomoSet.subset dom_mf mono_f_l) &&
   (Homo.GraphHomoSet.subset mono_f_l dom_mf) 
   ) &&
   (let codom_mx = Homo.GraphHomoMap.bindings mf |> List.map snd 
   |> Homo.GraphHomoSet.of_list in
   Homo.GraphHomoSet.subset codom_mx mono_f_r)
  );
  (* body *) 
  Homo.GraphHomoSet.for_all 
  (
    fun h_f_l -> 
      (* find ok because of the condition above *)
      let h_f_r = Homo.GraphHomoMap.find h_f_l mf in
      (* double pullback *)
      (
        let (_, h_k'_k_left) = Category_Graph.pullback_cospan_monos (h_f_l, lhs) in
        let (_, h_k'_k_right) = Category_Graph.pullback_cospan_monos (h_f_r, rhs) in
        let img1 = h_k'_k_left |> Homo.imgOf in
        let img2 = h_k'_k_right |> Homo.imgOf in
        MGraph.equal img1 img2) &&
      (* condition 2.2 *)
      (
        let occs_x_l_forbiddened =  
          match generate_occs_with_forbidden_contexts x l with _,occs_x_forbiddened,_ -> occs_x_forbiddened in
        List.for_all 
          ( fun h_x_l ->
            assert (Homo.GraphHomoMap.mem h_x_l mx);
            let h_x_r = Homo.GraphHomoMap.find h_x_l mx in
            match Homo.isCommutative [h_x_l] [h_x_f; h_f_l] with
            | false -> true
            | true -> Homo.isCommutative [h_x_r] [h_x_f; h_f_r]
          )
          occs_x_l_forbiddened
      )
  )
  mono_f_l
   
let generate_mfs h_x_f (rho:Rule.t) =
  let f = Homo.codom h_x_f in
  let l,r = rho |> Rule.leftGraph, rho |> Rule.rightGraph in
  let mono_f_l  = Homo.occs f l   in
  let mono_f_r  = Homo.occs f r  in
  let mxs = Aux_functions.inj_maps_from_to mono_f_l mono_f_r in 
  List.map Homo.GraphHomoMap.of_list mxs

let%expect_test "" = 
  let h_x_f = Homo.fromList 
  [1;2;3] [(1,"a",3,1);(3,"a",2,2)]
  [1;2;3] [(1,"a",3,1);(3,"c",3,3);(3,"a",2,2)]
  [(1,1);(2,2);(3,3)] [(1,1);(2,2)]  in
  let rho =  ConcretGraphRewritingSystems.bruggink_2014_ex1_rl in
  let mfs = generate_mfs h_x_f rho in
  let (tmp:string list) = List.map Homo.toStr_GraphHomoMap mfs in 
   String.concat "next mx\n" tmp
   |> print_endline
  ;[%expect {|
  |}];; 

let%expect_test "" = 
  let l1 = Homo.fromList
  [1;2] [] 
  [1;2;3] [(1,"a",3,1);(3,"c",3,3);(3,"a",2,2)]
  [(1,1);(2,2)] [] in
  let r1 =  Homo.fromList
  [1;2] [] 
  [1;2;3] [(1,"a",3,1);(3,"c",3,3);(3,"a",2,2)]
  [(1,1);(2,2)] [] in 
  let rho = Grs.fromHomos l1 r1 in
  let h_x_f = Homo.fromList 
  [1;2;3] [(1,"a",3,1);(3,"a",2,2)]
  [1;2;3] [(1,"a",3,1);(3,"c",3,3);(3,"a",2,2)]
  [(1,1);(2,2);(3,3)] [(1,1);(2,2)]  in
  let mfs = generate_mfs h_x_f rho in
  let (tmp:string list) = List.map Homo.toStr_GraphHomoMap mfs in 
   String.concat "next mx\n" tmp
   |> print_endline
  ;[%expect {|
    dom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,c,3,3);(3,a,2,2) ]
    codom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,c,3,3);(3,a,2,2) ]
    hv:[(1,1);(2,2);(3,3)]
    he:[(1,1);(2,2);(3,3)]
    dom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,c,3,3);(3,a,2,2) ]
    codom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,c,3,3);(3,a,2,2) ]
    hv:[(1,1);(2,2);(3,3)]
    he:[(1,1);(2,2);(3,3)]
  |}];; 

let%expect_test "" = 
  let l1 = Homo.fromList
    [1;2] [] 
    [1;2;3] [(1,"a",3,1);(3,"c",3,3);(3,"a",2,2)]
    [(1,1);(2,2)] [] in
  let r1 =  Homo.fromList
    [1;2] [] 
    [1;2;3] [(1,"a",3,1);(3,"c",3,3);(3,"a",2,2)]
    [(1,1);(2,2)] [] in 
  let rho = Grs.fromHomos l1 r1 in
  let h_x_f = Homo.fromList 
    [1;2;3] [(1,"a",3,1);(3,"a",2,2)]
    [1;2;3] [(1,"a",3,1);(3,"c",3,3);(3,"a",2,2)]
    [(1,1);(2,2);(3,3)] [(1,1);(2,2)]  in
  let mfs = generate_mfs h_x_f rho in
  Printf.sprintf "|mfs| = %d\n" (List.length mfs) |> print_endline;
  let (tmp:string list) = List.map Homo.toStr_GraphHomoMap mfs in 
   String.concat "next mf\n" tmp
   |> print_endline;
  let x = {x = MGraph.fromList [1;2;3] [(1,"a",3,1);(3,"a",2,2)]; 
   fx = Some h_x_f } in
  let mxs = generate_mxs x rho in
  let mx = List.hd mxs in
  let mfs_filtered = List.filter (predictable_cond2 x rho mx) mfs in
    Printf.sprintf "|mfs_filtered| = %d\n" (List.length mfs_filtered) |> print_endline;
  let (tmp:string list) = List.map Homo.toStr_GraphHomoMap mfs_filtered in 
    String.concat "next mf\n" tmp
    |> print_endline;
  ;[%expect {|
    |mfs| = 1

    dom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,c,3,3);(3,a,2,2) ]
    codom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,c,3,3);(3,a,2,2) ]
    hv:[(1,1);(2,2);(3,3)]
    he:[(1,1);(2,2);(3,3)]
    dom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,c,3,3);(3,a,2,2) ]
    codom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,c,3,3);(3,a,2,2) ]
    hv:[(1,1);(2,2);(3,3)]
    he:[(1,1);(2,2);(3,3)]

    |mfs_filtered| = 1

    dom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,c,3,3);(3,a,2,2) ]
    codom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,c,3,3);(3,a,2,2) ]
    hv:[(1,1);(2,2);(3,3)]
    he:[(1,1);(2,2);(3,3)]
    dom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,c,3,3);(3,a,2,2) ]
    codom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,c,3,3);(3,a,2,2) ]
    hv:[(1,1);(2,2);(3,3)]
    he:[(1,1);(2,2);(3,3)]
  |}];;


(* predictable : Condition 3 *)
let inverse_rule (rho: Rule.t) = 
  Rule.fromHomos rho.r rho.l 
let predictable_cond3 x rho  = 
  is_x_non_increasing_rule_forSomePhi x rho &&
  is_x_non_increasing_rule_forSomePhi x (rho |> inverse_rule)

(* predictable : Condition 5 *)
let predictable_cond5 x rho mx (phi:Homo.t Homo.GraphHomoMap.t) = 
  let h_x_f = assert (x.fx |> Option.is_some); x.fx |> Option.get in
  let x = x.x in
  let l = rho |> Rule.leftGraph in
  let f =h_x_f |> Homo.codom in
  let d_l_f = calculateDXR f (inverse_rule rho) in
  List.for_all
    (fun (h_kp_lp,_) ->
      let lp = Homo.codom h_kp_lp in
      let h_x_lp_list = Homo.occs x lp in
      List.for_all 
        (fun h_x_lp ->
          let h_lp_l = Homo.inclusion_morph lp l in
          let h_x_l = Homo.composition h_x_lp h_lp_l in
          let left = Homo.GraphHomoMap.find h_x_l mx in
          let h_lp_r = Homo.GraphHomoMap.find h_kp_lp phi in
          let right = Homo.composition h_x_lp h_lp_r in
          Homo.isCommutative [left] [right]
        )
        h_x_lp_list
    )
    d_l_f
let generate_mfs x (rho:Rule.t) =
  assert (x.fx |> Option.is_some);
  let h_x_f = x.fx |> Option.get in
  let l,r = rho |> Rule.leftGraph, rho |> Rule.rightGraph in
  let f = (h_x_f |> Homo.codom) in
  let mono_f_l = Homo.occs f l in
  let mono_f_r = Homo.occs f r in
  let mfs = Aux_functions.inj_maps_from_to mono_f_l mono_f_r in 
  List.map Homo.GraphHomoMap.of_list mfs

let isPredictable_mx_mf_phi (x:rulerGraph) (rho:Rule.t) (mx:Homo.t Homo.GraphHomoMap.t) mf (phi: Homo.t Homo.GraphHomoMap.t) =
  (* all feasible mx for condition 1 *)
  
  (* all possible mfs for condition 2 *)
  (* let h_x_f = x.fx |> Option.get  in *)
  (* let mfs = generate_mfs h_x_f rho in *)
    (* |> Homo.GraphHomoMap.of_list in *)
    (* let predictable_cond2 x h_x_f (rho : Rule.t) mx (mf:Homo.t Homo.GraphHomoMap.t)  *)
  (* condition 1 *)
  (let cond1 = predictable_cond1 x rho mx in 
  (* Printf.sprintf "cond1 -> %b\n" cond1 |> print_endline;  *)
  cond1)
  &&
  (* condition 2 *)
  (let cond = predictable_cond2 x rho mx mf in 
  (* Printf.sprintf "cond2 -> %b\n" cond |> print_endline; *)
  cond)
   && 
  (* Condition 3 *)
  (let cond = predictable_cond3 x rho in 
  (* Printf.sprintf "cond3 -> %b\n" cond |> print_endline;  *)
  cond)
   &&
  (* Condition 4 *)
  (
    assert (x.fx |> Option.is_some);
    let f = x.fx |> Option.get |> Homo.codom in
    let cond = is_x_non_increasing_rule f (inverse_rule rho) phi in 
    (* Printf.sprintf "cond4 -> %b\n" cond |> print_endline; *)
     cond)
  &&
  (* Condition 5 *)
  (let cond = predictable_cond5 x rho mx phi in 
  (* Printf.sprintf "cond5 -> %b\n" cond |> print_endline;  *)
  cond)

let isPredictable x rho = 
  (* print_endline "isPredictable x rho"; *)
  (* mxs *)
  let mxs = generate_mxs x rho in 
  (* Printf.sprintf "mxs cardinal : %d" (List.length mxs)|> print_endline; *)
  (* mfs *)
  let mfs = generate_mfs x rho in
  (* Printf.sprintf "mfs cardinal : %d" (List.length mfs)|> print_endline; *)
  (* phis *)
  assert (x.fx |> Option.is_some);
  let f = x.fx |> Option.get |> Homo.codom in
  let phis = generate_all_phiX f (inverse_rule rho) in
  (* Printf.sprintf "phis cardinal : %d" (List.length phis)|> print_endline; *)
  let mx_mf_s = Core.List.cartesian_product mxs mfs in
  let mx_mf_phi_s = Core.List.cartesian_product mx_mf_s phis in
  (* Printf.sprintf "mx_mf_phi_s cardinal : %d" (List.length mx_mf_phi_s)|> print_endline; *)
  List.exists 
    (fun ((mx,mf),phi) -> isPredictable_mx_mf_phi x rho mx mf phi)
    mx_mf_phi_s


let%expect_test "" = 
  let rho = ConcretGraphRewritingSystems.bruggink_2014_ex1_rl in
  let h_x_f = Homo.fromList 
    [1;2;3] [(1,"a",3,1);(3,"a",2,2)]
    [1;2;3] [(1,"a",3,1);(3,"c",3,3);(3,"a",2,2)]
    [(1,1);(2,2);(3,3)] [(1,1);(2,2)]  in
  let x = {x = MGraph.fromList [1;2;3] [(1,"a",3,1);(3,"a",2,2)]; 
    fx = Some h_x_f } in
  let predictable = isPredictable x rho in
  (* print_endline "main func test"; *)
  Printf.sprintf "%b" predictable 
  |> print_endline
  ;[%expect {|
    true
  |}];;

let%expect_test "" = 
  let rho = ConcretGraphRewritingSystems.endrullis_2024_exd3_r1 in
  let x = aa_not_in_aca in
  let predictable = isPredictable x rho in
  (* print_endline "main func test";  *)
  Printf.sprintf "endrullis_2024_exd3_r1\n predictable : %b" predictable 
  |> print_endline
  ;[%expect {|
    endrullis_2024_exd3_r1
     predictable : true
  |}];;
  
let occs_graph_with_forbidden_context_strictly_decreasing x rho =
  let l, r = rho |> Rule.leftGraph, rho |> Rule.rightGraph in
  (* Printf.sprintf "left graph: %s \n" ( l |> MGraph.toStr) |> print_endline;
  Printf.sprintf "right graph: %s \n" ( r |> MGraph.toStr) |> print_endline; *)
  let occs_x_l_not_forbidden = 
    match generate_occs_with_forbidden_contexts x l with _,_,occs_not_forbidden -> occs_not_forbidden in
  (* begin 
    Printf.sprintf "left %d \n" (List.length occs_x_l_not_forbidden) |> print_endline;

    let occs,occs_x_forbiddened, occs_x_not_forbiddened = generate_occs_with_forbidden_contexts x l in
    Printf.sprintf "%d occs" (List.length occs) |> print_endline;
    List.iteri (fun i o -> Printf.sprintf "occ %d : %s" i (MGraph.toStr (o |> Homo.imgOf)) |> print_endline) occs;
    print_endline "";

    Printf.sprintf "%d occs not forbiddened" (List.length occs_x_not_forbiddened) |> print_endline;
    List.iteri (fun i o -> Printf.sprintf "occ %d : %s" i (MGraph.toStr (o |> Homo.imgOf)) |> print_endline) occs_x_not_forbiddened;
    Printf.sprintf "%d occs forbiddened" (List.length occs_x_forbiddened) |> print_endline;
    List.iteri (fun i o -> Printf.sprintf "occ %d : %s\n" i (MGraph.toStr (o|> Homo.imgOf)) |> print_endline) occs_x_forbiddened;
  end;
  begin 
    Printf.sprintf "ldfjls;djfds;lfjds;lf ==9((( s \n right %d \n" (List.length occs_x_l_not_forbidden) |> print_endline;

    let occs,occs_x_forbiddened, occs_x_not_forbiddened = generate_occs_with_forbidden_contexts x r in
    Printf.sprintf "%d occs" (List.length occs) |> print_endline;
    List.iteri (fun i o -> Printf.sprintf "occ %d : %s" i (MGraph.toStr (o |> Homo.imgOf)) |> print_endline) occs;
    print_endline "";

    Printf.sprintf "%d occs not forbiddened" (List.length occs_x_not_forbiddened) |> print_endline;
    List.iteri (fun i o -> Printf.sprintf "occ %d : %s" i (MGraph.toStr (o |> Homo.imgOf)) |> print_endline) occs_x_not_forbiddened;
    Printf.sprintf "%d occs forbiddened" (List.length occs_x_forbiddened) |> print_endline;
    List.iteri (fun i o -> Printf.sprintf "occ %d : %s\n" i (MGraph.toStr (o|> Homo.imgOf)) |> print_endline) occs_x_forbiddened;
  end; *)
  let occs_x_r_not_forbidden = 
    match generate_occs_with_forbidden_contexts x r with _,_,occs_not_forbidden -> occs_not_forbidden in
    Printf.sprintf "right %d \n" (List.length occs_x_r_not_forbidden) |> print_endline;
  occs_x_l_not_forbidden, occs_x_r_not_forbidden


let%expect_test "" = 
  (* let x = MGraph.fromList [1;2] [(1,"node",1,1);(2,"node",2,2)] in
  let h_x_f = Homo.fromList 
    [1;2] [(1,"node",1,1);(2,"node",2,2)]
    [1;3] [(1,"node",1,1);(3,"node",3,2);(1,"edge",3,3);]
    [(1,1);(2,3)] [(1,1);(2,2)]  in *)
  let x = Ruler_graph.nn_not_in_nen in
  let rho = ConcretGraphRewritingSystems.endrullis_2024_exd3.grs |> List.hd in
  let l, r = rho |> Rule.leftGraph, rho |> Rule.rightGraph in
  let g = l in
  let occs,occs_x_forbiddened, occs_x_not_forbiddened = generate_occs_with_forbidden_contexts x g in
  Printf.sprintf "%d occs" (List.length occs) |> print_endline;
  List.iteri (fun i o -> Printf.sprintf "occ %d : %s" i (MGraph.toStr (o |> Homo.imgOf)) |> print_endline) occs;
  print_endline "";

  let occs_context = (Homo.occs (Homo.codom (x.fx|>Option.get)) g) in
  Printf.sprintf "%d occs of the context" (List.length occs_context) |> print_endline;
  List.iteri (fun i o -> Printf.sprintf "occ %d : %s" i (MGraph.toStr (o |> Homo.imgOf)) |> print_endline) occs_context;
  print_endline "";

  Printf.sprintf "%d occs not forbiddened" (List.length occs_x_not_forbiddened) |> print_endline;
  List.iteri (fun i o -> Printf.sprintf "occ %d : %s" i (MGraph.toStr (o |> Homo.imgOf)) |> print_endline) occs_x_not_forbiddened;
  Printf.sprintf "%d occs forbiddened" (List.length occs_x_forbiddened) |> print_endline;

  List.iteri (fun i o -> Printf.sprintf "occ %d : %s\n" i (MGraph.toStr (o|> Homo.imgOf)) |> print_endline) occs_x_forbiddened;
  print_endline "\nRight\n";
  let g = r in
  let occs,occs_x_forbiddened, occs_x_not_forbiddened = generate_occs_with_forbidden_contexts x g in
  Printf.sprintf "%d occs" (List.length occs) |> print_endline;
  List.iteri (fun i o -> Printf.sprintf "occ %d : %s" i (MGraph.toStr (o |> Homo.imgOf)) |> print_endline) occs;
  print_endline "";

  let occs_context = (Homo.occs (Homo.codom (x.fx|>Option.get)) g) in
  Printf.sprintf "%d occs of the context" (List.length occs_context) |> print_endline;
  List.iteri (fun i o -> Printf.sprintf "occ %d : %s" i (MGraph.toStr (o |> Homo.imgOf)) |> print_endline) occs_context;
  print_endline "";

  Printf.sprintf "%d occs not forbiddened" (List.length occs_x_not_forbiddened) |> print_endline;
  List.iteri (fun i o -> Printf.sprintf "occ %d : %s" i (MGraph.toStr (o |> Homo.imgOf)) |> print_endline) occs_x_not_forbiddened;
  Printf.sprintf "%d occs forbiddened" (List.length occs_x_forbiddened) |> print_endline;

  List.iteri (fun i o -> Printf.sprintf "occ %d : %s\n" i (MGraph.toStr (o|> Homo.imgOf)) |> print_endline) occs_x_forbiddened
  ;[%expect {|
    2 occs
    occ 0 : nodes : [ 1;2 ]
    arrows : [ (1,node,1,1);(2,node,2,2) ]
    occ 1 : nodes : [ 1;2 ]
    arrows : [ (1,node,1,1);(2,node,2,2) ]
    
    0 occs of the context
    
    2 occs not forbiddened
    occ 0 : nodes : [ 1;2 ]
    arrows : [ (1,node,1,1);(2,node,2,2) ]
    occ 1 : nodes : [ 1;2 ]
    arrows : [ (1,node,1,1);(2,node,2,2) ]
    0 occs forbiddened
    
    Right
    
    2 occs
    occ 0 : nodes : [ 1;3 ]
    arrows : [ (1,node,1,1);(3,node,3,2) ]
    occ 1 : nodes : [ 1;3 ]
    arrows : [ (1,node,1,1);(3,node,3,2) ]
    
    1 occs of the context
    occ 0 : nodes : [ 1;3 ]
    arrows : [ (1,edge,3,3);(1,node,1,1);(3,node,3,2) ]
    
    1 occs not forbiddened
    occ 0 : nodes : [ 1;3 ]
    arrows : [ (1,node,1,1);(3,node,3,2) ]
    1 occs forbiddened
    occ 0 : nodes : [ 1;3 ]
    arrows : [ (1,node,1,1);(3,node,3,2) ]
  |}];; 


let terminating_counting_subgraph_with_forbidden_context (x:Ruler_graph.rulerGraph) (grs:ConcretGraphRewritingSystems.named_grs) = 
  let terminating = ref true in
  let report = ref "" in
  List.iteri 
    (fun i rho ->
      let predictable = isPredictable x rho in
      let (occs_x_l, occs_x_r) = occs_graph_with_forbidden_context_strictly_decreasing x rho in
      let nb_l, nb_r = (List.length occs_x_l, List.length occs_x_r) in
      terminating := !terminating && predictable && (nb_l > nb_r);
      report := !report ^ Printf.sprintf "rule %d\nX-occurrences not forbiddened predictable : %b\nstrictly decreasing X-occurrences : %b (%d => %d)\n\n" i predictable (nb_l > nb_r) nb_l nb_r
    )
    grs.grs;
  !terminating, !report

let%expect_test "" = 
  let x = nn_not_in_nen in
  let terminating, report = terminating_counting_subgraph_with_forbidden_context x ConcretGraphRewritingSystems.endrullis_2024_exd3 in
  (* print_endline "main func test";  *)
  Printf.sprintf "endrullis_2024_exd3\nterminating : %b\n%s" terminating report 
  |> print_endline
  ;[%expect {|
    left graph: nodes : [ 1;2 ]
    arrows : [ (1,node,1,1);(2,node,2,2) ]

    right graph: nodes : [ 1;3 ]
    arrows : [ (1,edge,3,3);(1,node,1,1);(3,node,3,2) ]

    right 1

    endrullis_2024_exd3
    terminating : true
    rule 0
    X-occurrences not forbiddened predictable : true
    strictly decreasing X-occurrences : true (2 => 1)
  |}];;
