module Homo = GraphHomomorphism
module Grs = GraphRewritingSystem
module RuleSet = GraphRewritingSystem.RuleSet
module Rule = GraphRewritingSystem.DPOrule
type rulerGraph = {x : MGraph.t; fx : Homo.t list}
let (<|) f x = f x

(*****************************************
          DRX
*****************************************)
let subgraph_of_rk  (rl:Rule.t) rp =
  let im_r_k = rl.r |> Homo.imgOf in
  MGraph.isSubGraphOf rp im_r_k

let%expect_test "" = 
  (* let x = { x=MGraph.fromList [1;2;3] [(1,"a",2,1);(2,"a",3,2)]; fx = []} in *)
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
  Termination.MGraph.iso rp x.x
let%expect_test "" = 
  let x = { x=MGraph.fromList [1;2;3] [(1,"a",2,1);(2,"a",3,2)]; fx = []} in
  let rho = ConcretGraphRewritingSystems.bruggink_2014_ex_4_rl_1 in
  let subgraphs = rho |> Rule.rightGraph |> MGraph.subGraphs in
  Printf.sprintf "total nb subgraphs : %d " (subgraphs |> List.length) |> print_endline;
  let elim = List.filter (subgraph_of_rk rho) subgraphs in
  Printf.sprintf "nb subgraphs (subgraph of r(K)): %d " (elim |> List.length) |> print_endline;
  let subgraphs = MGraph.GraphSet.diff (subgraphs |>  MGraph.GraphSet.of_list) (elim |> MGraph.GraphSet.of_list) in
   Printf.sprintf "nb subgraphs remained: %d " (subgraphs |> MGraph.GraphSet.cardinal) |> print_endline;
  let elim = MGraph.GraphSet.filter (iso_to_x x) subgraphs in
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

let can_construct_pbpo_diagram x h_K'R' r' =
  (* let h_R'R = Homo.inclusion_morph r' (rl |> Rule.rightGraph) in
  let pb,k' = Category_Graph.pullback_cospan_monos ({left=rl.r; right=h_R'R}:Category_Graph.cospan) in *)
  let h_R'Xs = Homo.homSet r' x.x |> List.filter Homo.isInj in
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
  let x = { x=MGraph.fromList [1;2;3] [(1,"a",2,1);(2,"a",3,2)]; fx = []} in
  let rho = ConcretGraphRewritingSystems.bruggink_2014_ex_4_rl_1 in
  let subgraphs = rho |> Rule.rightGraph |> MGraph.subGraphs in
  Printf.sprintf "total nb subgraphs : %d " (subgraphs |> List.length) |> print_endline;
  let elim = List.filter (subgraph_of_rk rho) subgraphs in
  Printf.sprintf "nb subgraphs (subgraph of r(K)): %d " (elim |> List.length) |> print_endline;
  let subgraphs = MGraph.GraphSet.diff (subgraphs |>  MGraph.GraphSet.of_list) (elim |> MGraph.GraphSet.of_list) in
   Printf.sprintf "nb subgraphs remained: %d " (subgraphs |> MGraph.GraphSet.cardinal) |> print_endline;
  let elim = MGraph.GraphSet.filter (iso_to_x x) subgraphs in
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
        can_construct_pbpo_diagram x h_k'r' rp
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
    
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1) ]

    nodes : [ 1;2;4 ]
    arrows : [ (4,a,2,3) ]

    nodes : [ 1;3 ]
    arrows : [ (1,a,3,1) ]

    nodes : [ 2;4 ]
    arrows : [ (4,a,2,3) ]
  |}]

let calculateDXR (x:rulerGraph) (rl:Rule.t) = 
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
  let x = { x=MGraph.fromList [1;2;3] [(1,"a",2,1);(2,"a",3,2)]; fx = []} in
  let rho = ConcretGraphRewritingSystems.bruggink_2014_ex_4_rl_1 in
  calculateDXR x rho 
  |>
  List.iter (fun (h_k'r', _) -> let g = Homo.codom h_k'r' in Printf.sprintf "\n%s\n" (MGraph.toStr g) |> print_string);
  [%expect{|
    nodes : [ 2;4 ]
    arrows : [ (4,a,2,3) ]
    
    nodes : [ 1;3 ]
    arrows : [ (1,a,3,1) ]
    
    nodes : [ 1;2;4 ]
    arrows : [ (4,a,2,3) ]
    
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1) ]
  |}]

  (*****************************************
          $X$- non increasing rule under phi
*****************************************)
(* condition 1 *)
let double_pullback_diagram_holds rho (phi:Homo.t MGraph.GraphMap.t) (h_k'r', h_k'k) =
    let r' = Homo.codom h_k'r' in
    let h_r'l = 
      match MGraph.GraphMap.find_opt r' phi with
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
  let x = { x=MGraph.fromList [1;2;3] [(1,"a",2,1);(2,"a",3,2)]; fx = []} in
  let rho = ConcretGraphRewritingSystems.bruggink_2014_ex_4_rl_1 in
  let drx = calculateDXR x rho in
  let (h_k'r', h_k'k) = List.nth drx 0 in
  let r' = Homo.codom h_k'r' in
  Printf.sprintf "r'\n%s" (Homo.codom h_k'r'|>MGraph.toStr) |> print_endline ;
  let h_r'l =  Homo.fromList 
                [2;4] [ (4,"a",2,3) ]
                [1;2;3] [(1,"a",3,1);(3,"a",2,2)]
                [(4,3);(2,2)] [(3,2)] in
    (* ignore h_r'l; *)
  let phi = MGraph.GraphMap.add r' h_r'l MGraph.GraphMap.empty in
  double_pullback_diagram_holds rho phi (h_k'r', h_k'k) |> Printf.sprintf "double pullback : %b" |> print_endline;
  let h_r'l2 =  Homo.fromList 
  [2;4] [ (4,"a",2,3) ]
  [1;2;3] [(1,"a",3,1);(3,"a",2,2)]
  [(4,1);(2,3)] [(3,1)] in
  (* ignore h_r'l; *)
  let phi2 = MGraph.GraphMap.add r' h_r'l2 MGraph.GraphMap.empty in
  double_pullback_diagram_holds rho phi2 (h_k'r', h_k'k) |> Printf.sprintf "double pullback : %b" |> print_endline;
  [%expect{|
      r'
      nodes : [ 2;4 ]
      arrows : [ (4,a,2,3) ]
      double pullback : true
      double pullback : false
  |}]

(* condition 2 *)
let non_clapsing (rho :GraphRewritingSystem.DPOrule.t) drx phi =
  List.for_all (fun (h_k'r', _) ->
    let r' = Homo.codom h_k'r' in
    let h_r'l = MGraph.GraphMap.find r' phi in
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
      let h_r'l = MGraph.GraphMap.find r' phi in
      let h_r''l = MGraph.GraphMap.find r'' phi in
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
        (MGraph.arrows r' |> MGraph.ArrowSet.to_list)
        )
    ) 
    drx
    drx

let node_injective_if_isolated_nodes x drx phi =
  if x.x |> MGraph.isConnected then true 
  else
  List.for_all2 (fun (h_k'r', _) (h_k'r'2, _) ->
    let r', r'' = Homo.codom h_k'r', Homo.codom h_k'r'2 in
    let h_r'l = MGraph.GraphMap.find r' phi in
    let h_r''l = MGraph.GraphMap.find r'' phi in
      (List.for_all2
      (fun x y ->      
          if MGraph.Node.equal x y then true
          else begin
            let x', y' = Homo.app_hv ~h:h_r'l x, Homo.app_hv ~h:h_r''l x in
            MGraph.Node.equal x' y' |> not
          end
      )
      (MGraph.nodes r' |> MGraph.NodeSet.to_list)
      (MGraph.nodes r' |> MGraph.NodeSet.to_list)
      )
  ) 
  drx
  drx



let generate_phis drx rho = 
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
          rp, h_rpls
      )
      drx
  in
  let combinations = generate_combinations pairs in
   List.map 
   ~f:( fun l ->
    MGraph.GraphMap.of_list l
   ) combinations

let%expect_test "" = 
  let x = { x=MGraph.fromList [1;2;3] [(1,"a",2,1);(2,"a",3,2)]; fx = []} in
  let rho = ConcretGraphRewritingSystems.bruggink_2014_ex_4_rl_1 in
  let drx = calculateDXR x rho in
  let phis = generate_phis drx rho in
  List.iteri (fun i phi ->
    print_endline <| Printf.sprintf "phi %d: " i;
    List.iteri (fun j (rp,h_rpl) -> 
      Printf.sprintf "phi i%d j%d:\nr':\n%sh_r'l:\n%s" i j 
      ( MGraph.toStr rp) (Homo.toStr h_rpl) |> print_endline
    )
    (phi |> MGraph.GraphMap.bindings)
  )
  phis;
  [%expect{|
    phi 0:
    phi i0 j0:
    r':
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1) ]h_r'l:
    dom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1) ]
    codom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,a,2,2) ]
    hv:[(1,1);(2,2);(3,3)]
    he:[(1,1)]
    phi i0 j1:
    r':
    nodes : [ 1;2;4 ]
    arrows : [ (4,a,2,3) ]h_r'l:
    dom:
    nodes : [ 1;2;4 ]
    arrows : [ (4,a,2,3) ]
    codom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,a,2,2) ]
    hv:[(1,1);(2,2);(4,3)]
    he:[(3,2)]
    phi i0 j2:
    r':
    nodes : [ 1;3 ]
    arrows : [ (1,a,3,1) ]h_r'l:
    dom:
    nodes : [ 1;3 ]
    arrows : [ (1,a,3,1) ]
    codom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,a,2,2) ]
    hv:[(1,1);(3,3)]
    he:[(1,1)]
    phi i0 j3:
    r':
    nodes : [ 2;4 ]
    arrows : [ (4,a,2,3) ]h_r'l:
    dom:
    nodes : [ 2;4 ]
    arrows : [ (4,a,2,3) ]
    codom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,a,2,2) ]
    hv:[(2,2);(4,3)]
    he:[(3,2)]
  |}]



let is_x_non_increasing_rule x rho phi =
  let drx = calculateDXR x rho in
  (* condition 1 *)
  let cond1 = List.for_all (fun (h_k'r', h_k'k) ->
    double_pullback_diagram_holds rho phi (h_k'r', h_k'k))
  drx in
  (Printf.sprintf "condition1 : %b" cond1) |> print_endline;
  (* condition 2 *)
  let cond2 = non_clapsing rho drx phi in
  (Printf.sprintf "condition2 : %b" cond2) |> print_endline;
  (* condition 3 *)
  let cond3 = edge_injective drx phi in
  (Printf.sprintf "condition3 : %b" cond3) |> print_endline;
  (* condition 4 *)
  let cond4 = node_injective_if_isolated_nodes x drx phi in
  (Printf.sprintf "condition4 : %b" cond3) |> print_endline;
  cond1 && cond2 && cond3 && cond4
    
let%expect_test "" = 
  let x = { x=MGraph.fromList [1;2;3] [(1,"a",2,1);(2,"a",3,2)]; fx = []} in
  let rho = ConcretGraphRewritingSystems.bruggink_2014_ex_4_rl_1 in
  let drx = calculateDXR x rho in
  let phis = generate_phis drx rho in
  List.iteri (fun i phi ->
    print_endline <| Printf.sprintf "phi %d: " i;
    List.iteri (fun j (rp,h_rpl) -> 
      Printf.sprintf "phi i%d j%d:\nr':\n%sh_r'l:\n%s" i j 
      ( MGraph.toStr rp) (Homo.toStr h_rpl) |> print_endline
    )
    (phi |> MGraph.GraphMap.bindings)
  )
  phis;
  (* let (h_k'r', _) = List.nth drx 0 in
  let r' = Homo.codom h_k'r' in
  Printf.sprintf "r'\n%s" (r' |>MGraph.toStr) |> print_endline ;
  Printf.sprintf "Im r : \n%s" ((Homo.imgOf rho.r) |>MGraph.toStr) |> print_endline ;
  Printf.sprintf "Im l : \n%s" ((Homo.imgOf rho.l) |>MGraph.toStr) |> print_endline ;
  let h_r'l =  Homo.fromList 
                [2;4] [ (4,"a",2,3) ]
                [1;2;3] [(1,"a",3,1);(3,"a",2,2)]
                [(4,3);(2,2)] [(3,2)] in
    (* ignore h_r'l; *)
  let phi = MGraph.GraphMap.add r' h_r'l MGraph.GraphMap.empty in
  is_x_non_increasing_rule x rho [drx |> List.hd] phi |> Printf.sprintf "is x non increasing : %b" |> print_endline;
  let h_r'l2 =  Homo.fromList 
  [2;4] [ (4,"a",2,3) ]
  [1;2;3] [(1,"a",3,1);(3,"a",2,2)]
  [(4,1);(2,3)] [(3,1)] in
  (* ignore h_r'l; *)
  let phi2 = MGraph.GraphMap.add r' h_r'l2 MGraph.GraphMap.empty in
  is_x_non_increasing_rule x rho [drx |> List.hd] phi2 |> Printf.sprintf "is x non increasing : %b" |> print_endline; *)
  is_x_non_increasing_rule x rho (List.nth phis 0) |> Printf.sprintf "is x non increasing : %b" |> print_endline; 
  [%expect{|
    phi 0:
    phi i0 j0:
    r':
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1) ]h_r'l:
    dom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1) ]
    codom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,a,2,2) ]
    hv:[(1,1);(2,2);(3,3)]
    he:[(1,1)]
    phi i0 j1:
    r':
    nodes : [ 1;2;4 ]
    arrows : [ (4,a,2,3) ]h_r'l:
    dom:
    nodes : [ 1;2;4 ]
    arrows : [ (4,a,2,3) ]
    codom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,a,2,2) ]
    hv:[(1,1);(2,2);(4,3)]
    he:[(3,2)]
    phi i0 j2:
    r':
    nodes : [ 1;3 ]
    arrows : [ (1,a,3,1) ]h_r'l:
    dom:
    nodes : [ 1;3 ]
    arrows : [ (1,a,3,1) ]
    codom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,a,2,2) ]
    hv:[(1,1);(3,3)]
    he:[(1,1)]
    phi i0 j3:
    r':
    nodes : [ 2;4 ]
    arrows : [ (4,a,2,3) ]h_r'l:
    dom:
    nodes : [ 2;4 ]
    arrows : [ (4,a,2,3) ]
    codom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,a,2,2) ]
    hv:[(2,2);(4,3)]
    he:[(3,2)]
    condition1 : true
    condition2 : true
    condition3 : true
    condition4 : true
    is x non increasing : true
  |}]


(****************************************
           Predictable
*******************************************)
(* Condition 1 *)
(** [generate_occs_with_forbidden_contexts x g] = [(occs_x,occs_x_forbiddened, occs_x_not_forbiddened)] *)
let generate_occs_with_forbidden_contexts x g =
  let forbidden_contexts = x.fx |> List.map Homo.codom in
  let occs_forbidden_contexts = 
    List.fold_right 
    (fun f acc ->
      List.append acc 
      (Homo.occs f g)
    ) 
    forbidden_contexts 
    [] 
  in
  let occs_x = Homo.occs x.x g in
  let occs_x_forbiddened, occs_x_not_forbiddened = List.partition (fun x -> 
    List.for_all 
    (fun f -> MGraph.isSubGraphOf (x |> Homo.imgOf) (f |> Homo.imgOf))
    occs_forbidden_contexts
  ) occs_x in
  occs_x,occs_x_forbiddened, occs_x_not_forbiddened
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
          fx = [Homo.fromList [1;2;3] [(1,"a",3,1);(3,"a",2,2)]
          [1;2;3] [(1,"a",3,1);(3,"c",3,3);(3,"a",2,2)]
          [(1,1);(2,2);(3,3)] [(1,1);(2,2)] ] } in
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

let predictable_cond1 x (rho : Rule.t) (mx:Homo.t Homo.GraphHomoMap.t) =
  let lhs, rhs = rho.l, rho.r in
  let l,r = rho |> Rule.leftGraph, rho |> Rule.rightGraph in
  let mono_x_l_forbidden = 
    match generate_occs_with_forbidden_contexts x l with _,_,occs -> occs 
    |> Homo.GraphHomoSet.of_list
  in
  let mono_x_r_forbidden = 
      match generate_occs_with_forbidden_contexts x r with _,_,occs -> occs 
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
