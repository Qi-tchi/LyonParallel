module Homo = GraphHomomorphism
module Grs = GraphRewritingSystem
(* module B = Batteries  *)
(* module type BigM = Cs.BigM *)
module Example = ConcretGraphRewritingSystems
(* module Bat = Batteries *)
module MapInt = Map.Make(Int)
module RuleMap = Grs.RuleMap
module GraphHomoSet = Homo.GraphHomoSet
module GraphHomoMap = Homo.GraphHomoMap

module type Parm = sig
  val grs : ConcretGraphRewritingSystems.named_grs
  val size : int
  val integer : bool
  val ub : int
  (* val monic_matching : bool *)
  val opt : bool 
  val semiring : Semiring.semiring_t
  val file_name : string
end
let file_name semiring size ub integer = Printf.sprintf "%s_size%d_maxW%d_%s" (Semiring.string_of_semiring_t semiring) size ub (if integer then "int" else "float")
module Make (P:Parm) = struct  
  (* let delta = 0.000001 *)
  let rules_l = P.grs.grs  
  let labels_s = (GraphRewritingSystem.RuleSet.of_list P.grs.grs) |> Grs.labels
  let labels_l = (GraphRewritingSystem.RuleSet.of_list P.grs.grs) |> Grs.labels_l 
  let integer = P.integer
  let size = P.size
  let ub = P.ub
  let file_name = file_name P.semiring P.size P.ub P.integer
  let oc = open_out (Printf.sprintf "tmp/%s.smt2" file_name)
  (* let oc_tropical = open_out (Printf.sprintf "tmp/%s_tropical.smt2" file_name)
  let oc_arctic = open_out (Printf.sprintf "tmp/%s_arctic.smt2" file_name)
  let oc_arithmetic = open_out (Printf.sprintf "tmp/%s_arithmetic.smt2" file_name) *)
  let ctx = Z3.mk_context []
  let typeGraph =
    let nodeIDs = List.init size (fun i -> i) in 
    let g = List.fold_left (fun acc id -> MGraph.addNode acc id) MGraph.empty nodeIDs in
    MGraph.completeToSimpleCompleteGraph g labels_s
  let measuringMorphismToTypeGraph_l = 
    let arrows = labels_l |> List.map (fun l -> (0,l,1,1)) in 
    let singleton_Graphs_l = arrows 
      |> List.map (fun ar -> MGraph.fromList [0;1] [ar]) in
      singleton_Graphs_l 
      (* all morphisms from singleton graphs to type graph *)
      (* |> List.map (fun dom -> GraphHomoFromTo.homSet dom typeGraph) *)
      (* homset modified: to debug *)
      |> List.map (fun dom -> GraphHomoFromTo.homSet_fast_with_y_acompletesimplegraph dom typeGraph labels_l)

      |> List.flatten 
      (* no dup *)
      |> GraphHomoSet.of_list |> GraphHomoSet.elements 
  
  (* let isMeasuringMorphismToTypeGraph e = 
    List.mem e measuringMorphismToTypeGraph_l *)

  let measuringMorphism_to_str e =
    (* assert(isMeasuringMorphismToTypeGraph e); *)
    (* let dom = Homo.dom e in
    let codom = Homo.codom e in
    let ar = MGraph.arrows dom |> MGraph.ArrowSet.choose in
    let e = Homo.heX (Homo.he e) ar in
    let id_str = e |> MGraph.Arrow.id |> string_of_int in
    let src_dst_str = e |> MGraph.arrowToStrNoID ~g:codom in
    Printf.sprintf "%s_%s" id_str src_dst_str *)
    let dom = Homo.dom e in
    let codom = Homo.codom e in
    let ar = MGraph.arrows dom |> MGraph.ArrowSet.choose in
    let ar' = Homo.heX (Homo.he e) ar in
    let l = MGraph.labelOf codom ar' in
    let d = MGraph.dstOf codom ar' in
    let s = MGraph.srcOf codom ar' in
    (* Printf.sprintf "s%d->t%d_%s" s d l  *)
    Printf.sprintf "E%d_%d_%s" s d l 

  let vars = ref [];;
  let nbVars = ref 0
  let map_x = 
    measuringMorphismToTypeGraph_l
    |> List.map 
      (fun e -> 
          (* let name= Printf.sprintf "x_localId{%d}_arrow{%s}_globalId{%d}" i (measuringMorphism_to_str e) !nbVars in  *)
          let name= 
           "x_" ^ (string_of_int !nbVars) ^"_"^(measuringMorphism_to_str e)
          (* Printf.sprintf "x_%d_e{%s}" i (measuringMorphism_to_str e)  *)
        in 
          let bool_sort = Z3.Boolean.mk_sort ctx in
          let v = Z3.Expr.mk_const_s ctx name bool_sort in
          vars := !vars @ [(v,name)];
          nbVars := !nbVars |> succ; 
          
          Printf.fprintf oc "(declare-const %s Bool)\n" name;
          (* if P.semiring = Tropical then Printf.fprintf oc_tropical "(declare-const %s Bool)\n" name;
          if P.semiring = Arctic then Printf.fprintf oc_arctic "(declare-const %s Bool)\n" name;
          if P.semiring = Arithmetic then Printf.fprintf oc_arithmetic "(declare-const %s Bool)\n" name; *)
          (e, v)
      ) 
      |> List.to_seq |> GraphHomoMap.of_seq
  let x e = 
    assert(GraphHomoMap.mem e map_x );
    GraphHomoMap.find e map_x 
  let map_y = measuringMorphismToTypeGraph_l
    |> List.map
      (fun e -> 
        (* let name = Printf.sprintf "y_localId{%d}_arrow{%s}_globalId{%d}" i (measuringMorphism_to_str e) !nbVars in  *)
        let name =
          "y_"^ string_of_int (!nbVars) ^ "_" ^ (measuringMorphism_to_str e)
           (* Printf.sprintf "y_%d_e{%s}" i (measuringMorphism_to_str e)  *)
          in 
        let sort = if integer then Z3.Arithmetic.Integer.mk_sort ctx else Z3.Arithmetic.Real.mk_sort ctx in
        let sort_flag = if integer then "Int" else "Real" in
        let v = Z3.Expr.mk_const_s ctx name sort in
        vars := !vars @ [(v,name)];
        nbVars := !nbVars |> succ;

        Printf.fprintf oc "(declare-const %s %s)\n" name sort_flag;
        (* if P.semiring = Tropical then Printf.fprintf oc_tropical "(declare-const %s %s)\n" name sort_flag;
        if P.semiring = Arctic then Printf.fprintf oc_arctic "(declare-const %s %s)\n" name  sort_flag;
        if P.semiring = Arithmetic then Printf.fprintf oc_arithmetic "(declare-const %s %s)\n" name  sort_flag; *)
        (e,v))
      |> List.to_seq |> GraphHomoMap.of_seq

  let y a = 
    (* assert(isMeasuringMorphismToTypeGraph a); *)
    assert(GraphHomoMap.mem a map_y);
    GraphHomoMap.find a map_y;;
    
  let map_z = rules_l |> List.mapi 
  (fun i rl -> 
      let name =
        "z_" ^ (string_of_int !nbVars) ^ "_rl_" ^ (string_of_int i)
      in 
      let bool_sort = Z3.Boolean.mk_sort ctx in
      let v = Z3.Expr.mk_const_s ctx name bool_sort in
      vars := !vars @ [(v,name)];
      nbVars := !nbVars |> succ;   
      
      Printf.fprintf oc "(declare-const %s Bool)\n" name;
      (* if P.semiring = Tropical then Printf.fprintf oc_tropical "(declare-const %s Bool)\n" name;
      if P.semiring = Arctic then Printf.fprintf oc_arctic "(declare-const %s Bool)\n" name;
      if P.semiring = Arithmetic then Printf.fprintf oc_arithmetic "(declare-const %s Bool)\n" name; *)
      (rl, v)
  ) |> List.to_seq |>  RuleMap.of_seq

  let z rl = 
    assert( RuleMap.mem rl map_z);
    RuleMap.find rl map_z 

  
  let homotoStr_nodes h = 
    let dom = Homo.dom h in
    let nodes = MGraph.nodes dom |> MGraph.NodeSet.elements in
    let hv = Homo.hv h in
    let s = List.map 
      (fun n -> let t = Homo.hvX hv n in
       Printf.sprintf "%d/%d" n t)  nodes in
    let s = s |> String.concat "_" in
    s
  let homotoStr_edges h = 
    let dom = Homo.dom h in
    let codom = Homo.codom h in
    let arrows = MGraph.arrows dom |> MGraph.ArrowSet.elements in
    let he = Homo.he h in
    let s = List.map 
      (fun n -> 
        let n' = Homo.heX he n in
        let s,t = MGraph.srcDstOf codom n' in
        let l = MGraph.labelOf codom n' in
        let id = MGraph.Arrow.id n' in
        Printf.sprintf "E%d_%d_%s_id%d" s t l id
        )  arrows |> String.concat "_" in
    s
  let homotoStr h = 
    Printf.sprintf "nodes_%s_arrows_%s" (homotoStr_nodes h) (homotoStr_edges h)

  let map_h = 
    let graphs = List.map (fun rl -> [Grs.leftGraph rl; Grs.rightGraph rl]) rules_l
      |> List.flatten
        (* no dupli *)
      |> MGraph.GraphSet.of_list
      |> MGraph.GraphSet.elements in
    let homos = 
      (* List.map (fun g -> GraphHomoFromTo.homSet g typeGraph) graphs *)
    (* no dupli *)
    (* homset to fast homset : to debug*)
    List.map (fun g -> GraphHomoFromTo.homSet_fast_with_y_acompletesimplegraph g typeGraph labels_l) graphs
      |> List.flatten
      |> GraphHomoSet.of_list 
      |> GraphHomoSet.elements in
    List.map
      (fun h -> 
        let name =       
          (* "h_" ^ (string_of_int !nbVars) *)
          Printf.sprintf "h_%d_%s" !nbVars (homotoStr h) 
        in
        let bool_sort = Z3.Boolean.mk_sort ctx in
        let v = Z3.Expr.mk_const_s ctx name bool_sort in
        vars := !vars @ [(v,name)];
        nbVars := !nbVars |> succ;

        Printf.fprintf oc "(declare-const %s Bool)\n" name;
        (* if P.semiring = Tropical then Printf.fprintf oc_tropical "(declare-const %s Bool)\n" name;
        if P.semiring = Arctic then Printf.fprintf oc_arctic "(declare-const %s Bool)\n" name;
        if P.semiring = Arithmetic then Printf.fprintf oc_arithmetic "(declare-const %s Bool)\n" name; *)
        (h,v)) homos
      |>List.to_seq |> GraphHomoMap.of_seq 
  
  let h x = assert(GraphHomoMap.mem x map_h);
   GraphHomoMap.find x map_h




let complete_lK_ToSimpleCompleteGraph labels l  = 
  let g = Homo.codom l in
  let lk = Homo.imgOf l in
  let nodes_lk = MGraph.nodes lk in
  (* let nodes_g = MGraph.nodes g in *)
  MGraph.NodeSet.fold 
    (fun u acc -> MGraph.NodeSet.fold 
      (fun v acc' -> MGraph.LabelSet.fold 
        (fun l acc'' -> 
          if MGraph.arrowsFromToLabeledBy acc'' u v l |> MGraph.ArrowSet.is_empty
          then MGraph.addNewArrowNoID acc'' ~ar:(u,l,v)
          else acc'')
        labels 
        acc'
      ) 
    nodes_lk
    acc
    ) 
  nodes_lk
  g

let restricted_to_lK_and_complete_ToSimpleCompleteGraph labels l  = 
  (* complete *)
  (* let g = Homo.codom l in *)
  let lk = Homo.imgOf l in
  let nodes_lk = MGraph.nodes lk in
  (* let nodes_g = MGraph.nodes g in *)
  (* let g' = MGraph.NodeSet.fold (fun v acc -> if MGraph.isNodeOf lk v then acc else MGraph.deleteNodeOfId acc ~n:(MGraph.Node.id v)) nodes_g g in *)
  MGraph.NodeSet.fold 
    (fun u acc -> MGraph.NodeSet.fold 
      (fun v acc' -> MGraph.LabelSet.fold 
        (fun l acc'' -> 
          if MGraph.arrowsFromToLabeledBy acc'' u v l |> MGraph.ArrowSet.is_empty
          then MGraph.addNewArrowNoID acc'' ~ar:(u,l,v)
          else acc'')
        labels 
        acc'
      ) 
    nodes_lk
    acc
    ) 
  nodes_lk
  lk

let generate_homos_injOnNodes_from_l_ofOneRule rl =
  let l = Grs.lhs rl in
  let leftGraph = Homo.codom l in
  let leftGraph' = restricted_to_lK_and_complete_ToSimpleCompleteGraph labels_s l in
  let cs_node_inj = GraphHomoFromTo.homSet_fast_with_y_acompletesimplegraph leftGraph' typeGraph labels_l
  |> Homo.GraphHomoSet.of_list
  |> Homo.GraphHomoSet.filter (Homo.isInjOnNodes) 
  |> Homo.GraphHomoSet.elements in
  let l' = 
    Homo.fromGraphsAndMaps (Homo.dom l) leftGraph' (Homo.hv l) (Homo.he l) in
  let is = GraphHomoFromTo.homSet_fast_with_y_acompletesimplegraph leftGraph leftGraph' labels_l in
  let is_legal =  List.filter (fun i -> Homo.isCommutative [l; i] [l']) is in
  (* 2. for tk = K -l-> L -i-> L' -c-> T *) 
  let prod_card = Batteries.List.cartesian_product is_legal cs_node_inj in
  let context_closures = List.map (fun (i,c) -> Homo.compositionList [i;c]) prod_card in
  context_closures
  (* to do debug *)
let generate_homos_injOnNodes_from_l's_to_typegraph rules = 
  let lhss = List.map Grs.lhs rules in
  (* let lg's = List.map (fun g -> MGraph.generate_completeSimpleGraph_of_order (Homo.imgOf g |> MGraph.nodes |> MGraph.NodeSet.cardinal) labels_l ) lhss in 
  *)
  (* let ls = List.map Grs.lhs rules in generate_homos_injOnNodes_from_l_ofOneRule *)
  (* let leftGraphs = List.map Homo.codom ls in *)
  (* to do begin repetition . def in  *)
  let leftGraph's = List.map (restricted_to_lK_and_complete_ToSimpleCompleteGraph labels_s) lhss in
  let hs = List.map (fun leftGraph' -> GraphHomoFromTo.homSet_fast_with_y_acompletesimplegraph leftGraph' typeGraph labels_l) leftGraph's 
  |> List.flatten
  |> Homo.GraphHomoSet.of_list
  |> Homo.GraphHomoSet.filter (Homo.isInjOnNodes) 
  |> Homo.GraphHomoSet.elements in
  hs
  (* to do end repetition *)
  (* let context_closures = List.map generate_homos_injOnNodes_from_l_ofOneRule rules 
  |> List.flatten in
  List.append context_closures hs
  |> Homo.GraphHomoSet.of_list
  |> Homo.GraphHomoSet.elements *)

  let map_c = 
    let hs = 
      if P.grs.monic_matching then generate_homos_injOnNodes_from_l's_to_typegraph rules_l 
      else begin
          let gs = [MGraph.generate_completeSimpleGraph_of_order 1 labels_l] in
          let hs = List.fold_left (fun acc g ->  GraphHomoFromTo.homSet_fast_with_y_acompletesimplegraph g typeGraph labels_l @ acc) [] gs in hs
        end 
      in
    List.map 
      (fun h -> 
        (* let name = Printf.sprintf "c_%d_%s" i (name_homo h "" "") in *)
        let name = 
          (* "c_" ^ (string_of_int !nbVars) in *)
          Printf.sprintf "c_%d_%s" !nbVars (homotoStr h)  in
        let bool_sort = Z3.Boolean.mk_sort ctx in
        let v = Z3.Expr.mk_const_s ctx name bool_sort in
        vars := !vars @ [(v,name)];
        nbVars := !nbVars |> succ;

        Printf.fprintf oc "(declare-const %s Bool)\n" name;
        (* if P.semiring = Tropical then Printf.fprintf oc_tropical "(declare-const %s Bool)\n" name;
        if P.semiring = Arctic then Printf.fprintf oc_arctic "(declare-const %s Bool)\n" name;
        if P.semiring = Arithmetic then Printf.fprintf oc_arithmetic "(declare-const %s Bool)\n" name; *)
        (h,v)
    )
    hs
   |> List.to_seq |> GraphHomoMap.of_seq
   
  let c x = assert(GraphHomoMap.mem x map_c); GraphHomoMap.find x map_c

  let map_h' =
    let graphs = List.map (fun rl -> [Grs.leftGraph rl; Grs.rightGraph rl]) rules_l 
    |> List.flatten
      (* no dupli *)
    |> MGraph.GraphSet.of_list
    |> MGraph.GraphSet.elements in
      let homos = List.map 
        (* (fun g -> GraphHomoFromTo.homSet g typeGraph)  *)
        (* homset to fast homset : to debug*)
        (fun g -> GraphHomoFromTo.homSet_fast_with_y_acompletesimplegraph g typeGraph labels_l) 
        graphs
    (* no dupli *)
    |> List.flatten
    |> GraphHomoSet.of_list 
    |> GraphHomoSet.elements
    in
    List.map
      (fun h -> 
        let name = 
        (* "hp_" ^ (string_of_int !nbVars) *)
          Printf.sprintf "hp_%d_%s" !nbVars (homotoStr h) 
        in
        let sort = if integer then Z3.Arithmetic.Integer.mk_sort ctx else Z3.Arithmetic.Real.mk_sort ctx in
        let sort_flag = if integer then "Int" else "Real" in
        let v = Z3.Expr.mk_const_s ctx name sort in
        vars := !vars @ [(v,name)];
        nbVars := !nbVars |> succ;

        Printf.fprintf oc "(declare-const %s %s)\n" name  sort_flag;
        (* if P.semiring = Tropical then Printf.fprintf oc_tropical "(declare-const %s %s)\n" name  sort_flag;
        if P.semiring = Arctic then Printf.fprintf oc_arctic "(declare-const %s %s)\n" name  sort_flag;
        if P.semiring = Arithmetic then Printf.fprintf oc_arithmetic "(declare-const %s %s)\n" name  sort_flag;  *)
        (h,v)
      )
      homos
      |>List.to_seq |>  GraphHomoMap.of_seq

  let h' h = assert (GraphHomoMap.mem h map_h');
    GraphHomoMap.find h map_h'

  module HomoHomo = struct
    type t = Homo.t * Homo.t
    let compare (x,y) (x',y') = 
      let r = Homo.compare x x' in
      if r <> 0 then r else
        Homo.compare y y'
  end
  module Set_HomoHomo_mipvar = Set.Make(HomoHomo)
  module Map_HomoHomo_mipvar = Map.Make(HomoHomo)

  let map_k = 
    let aux rl = 
      let k = Grs.interfaceGraph rl in 
      let tks = GraphHomoFromTo.homSet_fast_with_y_acompletesimplegraph k typeGraph labels_l in
      List.map (fun tk -> [(tk, Grs.lhs rl); (tk, Grs.rhs rl)]) tks
      |> List.flatten
    in
    let tmp = List.map aux rules_l |> List.flatten 
      |> Set_HomoHomo_mipvar.of_list
      |> Set_HomoHomo_mipvar.elements
    in
    let map_k = List.map
      (fun (tk,f) ->
        let name = 
          (* "k_" ^ (string_of_int !nbVars) *)
          Printf.sprintf "k_%d_tk_%s_f_%s" !nbVars (homotoStr tk) (homotoStr f) 
          in
          (* Printf.sprintf "k_%d_tk_%s_f_%s" i (name_homo tk "" "") (Homo.toStr f) in *)
        let bool_sort = Z3.Boolean.mk_sort ctx in
        let v = Z3.Expr.mk_const_s ctx name bool_sort in
        vars := !vars @ [(v,name)];
        nbVars := !nbVars |> succ;

        Printf.fprintf oc  "(declare-const %s Bool)\n" name;
        (* if P.semiring = Tropical then Printf.fprintf oc_tropical 
        "(declare-const %s Bool)\n" name;
        if P.semiring = Arctic then Printf.fprintf oc_arctic 
        "(declare-const %s Bool)\n" name;
        if P.semiring = Arithmetic then Printf.fprintf oc_arithmetic 
        "(declare-const %s Bool)\n" name; *)
        ((tk,f),v)
      )
      tmp
    |> List.to_seq |> Map_HomoHomo_mipvar.of_seq in
    map_k 


  let map_k' = 
    let left rl = 
      let k = Grs.interfaceGraph rl in 
      (* let tks = GraphHomoFromTo.homSet k typeGraph in *)
      (*homset to fast homset to debug *)
      let tks = GraphHomoFromTo.homSet_fast_with_y_acompletesimplegraph k typeGraph labels_l in

      List.map (fun tk -> (tk, Grs.lhs rl)) tks in
    let right rl = 
      let k = Grs.interfaceGraph rl in 
      (* let tks = GraphHomoFromTo.homSet k typeGraph in *)
      let tks = GraphHomoFromTo.homSet_fast_with_y_acompletesimplegraph k typeGraph labels_l in
            (*homset to fast homset to debug *)
      List.map (fun tk -> (tk, Grs.rhs rl)) tks
    in
    let tmp_left = List.map left rules_l |> List.flatten in
    let tmp_right = List.map right rules_l |> List.flatten in
    let tmp = tmp_right @ tmp_left in
    let tmp = tmp |> Set_HomoHomo_mipvar.of_list
      |> Set_HomoHomo_mipvar.elements
    in
    let map_k' = List.map
    (fun (tk,f)   ->
      let name =
        (* "kp_" ^ (string_of_int !nbVars)  *)
        Printf.sprintf "kp_%d_tk_%s_f_%s" !nbVars (homotoStr tk) (homotoStr f) 
      in
        let sort = if integer then Z3.Arithmetic.Integer.mk_sort ctx else Z3.Arithmetic.Real.mk_sort ctx in
        let sort_flag = if integer then "Int" else "Real" in
        let v = Z3.Expr.mk_const_s ctx name sort in
        vars := !vars @ [(v,name)];
        nbVars := !nbVars |> succ;

        Printf.fprintf oc "(declare-const %s %s)\n" name  sort_flag;
        (* if P.semiring = Tropical then Printf.fprintf oc_tropical 
        "(declare-const %s %s)\n" name  sort_flag;
        if P.semiring = Arctic then Printf.fprintf oc_arctic 
        "(declare-const %s %s)\n" name  sort_flag;
        if P.semiring = Arithmetic then Printf.fprintf oc_arithmetic 
        "(declare-const %s %s)\n" name  sort_flag; *)
      ((tk,f),v)
    )
    tmp
    |> List.to_seq |> Map_HomoHomo_mipvar.of_seq in
    map_k'
  
  let k tk f = assert (Map_HomoHomo_mipvar.mem (tk,f) map_k);
    Map_HomoHomo_mipvar.find (tk,f) map_k
  let k' tk f = assert (Map_HomoHomo_mipvar.mem (tk,f) map_k);
    Map_HomoHomo_mipvar.find (tk,f) map_k'


    

let v_to_name v = assert(List.mem_assoc v !vars); List.assoc v !vars

(* cst on y *)
let _ =
  GraphHomoMap.iter (fun a xa ->
      let ya = y a in
      assert(List.mem_assoc xa !vars && List.mem_assoc ya !vars);
      (* variable range *)
      let s = if integer then
        Printf.sprintf
        "(assert 
                  (and (>= %s 0) 
                       (<= %s %d)
                  )
        )\n"
       (List.assoc ya !vars) (List.assoc ya !vars) ub  
      else
        Printf.sprintf
        (* "(assert 
        (>= %s 0.0) 
      )\n"
      (List.assoc ya !vars) *)
      "(assert 
      (and (>= %s 0.0) 
          (<= %s %d.0)
      )
    )\n" 
      (List.assoc ya !vars) (List.assoc ya !vars) ub
      in 
      if P.semiring = Tropical then output_string oc s;
      if P.semiring = Arctic then output_string oc s; 
      (*arithmetic *)
      if P.semiring = Arithmetic then begin
        let s = if integer then 
          Printf.sprintf
          (* "(assert (>= %s 1))\n"
          (List.assoc ya !vars)   *)
          "(assert 
          (and (>= %s 1) 
               (<= %s %d)
          )
          )\n"
          (List.assoc ya !vars) (List.assoc ya !vars) ub  
          (* Printf.sprintf
          "(assert 
                    (and (>= %s 1) 
                        (<= %s %d)
                    )
          )\n"
          (List.assoc ya !vars) (List.assoc ya !vars) ub *)
          else
          (* Printf.sprintf
          "(assert 
          (and (>= %s 1.0) 
              (<= %s 2.0)
          )
          )\n"
          (List.assoc ya !vars) 
          (List.assoc ya !vars) *)
          Printf.sprintf
          "(assert (>= %s 1.0))\n"
            (List.assoc ya !vars) 
        in 
        output_string oc s;
      end
  ) 
  map_y

    (* try begin
      let name = if not cst_name then "" else "\n\n[Cst_Y_>>>_" ^ xa.name ^ "_eq_1_"^ ya.name ^ "_geq_0" ^ "<<<]\n" in
      Lp_grb.add_gen_constr_Indicator ~env ~model ~name ~binvar:xa.ind ~binval:1 ~nvars:1 ~varinds ~varvals ~sense:Lp_grb.Cs.GT ~rhs:0.
      ;    Lp_grb.update_model env model ;      
      let name = if not cst_name then "" else  "\n[Cst_Y_>>>_" ^ xa.name ^ "_eq_1_"^ ya.name ^ "_leq_1" ^ "<<<]\n" in
      Lp_grb.add_gen_constr_Indicator ~env ~model ~name ~binvar:xa.ind ~binval:1 ~nvars:1 ~varinds ~varvals ~sense:Lp_grb.Cs.LT ~rhs:ub
      ;    Lp_grb.update_model env model ;
      let name = if not cst_name then "" else  "\n[Cst_Y_>>>_" ^  xa.name ^ "_eq_0_"^ ya.name ^ "_eq_M" ^ "<<<]\n" in
      Lp_grb.add_gen_constr_Indicator ~env ~model ~name ~binvar:xa.ind ~binval:0 ~nvars:1 ~varinds ~varvals ~sense:Lp_grb.Cs.EQ ~rhs:bigM
      ;     Lp_grb.update_model env model
    end
    with _ -> failwith (Printf.sprintf "x : %s \n ya.ind=%d \n xa.ind=%d" (measuringMorphism_to_str a) ya.ind xa.ind ) *)

  (* add cst on z *)
  let _ = 
    let vars = map_z |> RuleMap.bindings |> List.map snd in
    let names = vars |> List.map v_to_name in 
    let s = String.concat " " names in
    let s = 
    Printf.sprintf 
        "(assert (or %s)
    )\n" s in

    output_string oc s
    (* if P.semiring = Tropical then output_string oc_tropical s;
    if P.semiring = Arctic then output_string oc_arctic s;
    if P.semiring = Arithmetic then output_string oc_arithmetic s *)

  let onWhichDepend_ExistenceOfMorphismToTypeGraph h =
    let img_h =  Homo.imgOf h in
    let dependsOn = List.filter (fun e -> let img_e = Homo.imgOf e in MGraph.isSubGraphOf img_e img_h) measuringMorphismToTypeGraph_l in
    dependsOn 

(*
  module RuleHomo = struct
    type t = Grs.t * Homo.GraphHomo.t
    let compare (r,x) (r',x') =
      let r1 = Grs.compare r r' in 
      if r1 <> 0 then r1 else
       Homo.compare x x' 
  end

  let name_homo h prefix postfix = 
    let hv, he = Homo.hv h, Homo.he h in
    let hv_str, he_str = (
      (* (Homo.hvToStr ~sep:"_" hv |> ignore; ""), *)
      (Homo.hvToStr ~sep:";" hv),
       (Homo.heToStr he ~sep:";") 
       (* (Homo.heToStr he ~sep:"_" |> ignore; "") *)
       ) in
    Printf.sprintf 
    "%s_hv{%s}_he{%s}_%s" prefix hv_str he_str postfix

  module MapRuleHomo = Map.Make(RuleHomo)

let calculate_l' rl =
  let limg = Grs.lhs rl |> Homo.imgOf in 
  let lgraph = Grs.leftGraph rl in 
  let idstart = MGraph.arrows lgraph |> MGraph.ArrowSet.elements|> List.map MGraph.Arrow.id |> List.sort Int.compare |> List.rev |> List.hd in
  let l' = MGraph.completeToSimpleCompleteGraphWithIDStartFrom limg labels_s idstart in
  let l' = MGraph.unionOfSubGraphs l' lgraph in
  l'

let calculate_l'_2 rl =
  let limg = Grs.lhs rl |> Homo.imgOf in 
  let lgraph = Grs.leftGraph rl in 
  let idstart = MGraph.arrows lgraph |> MGraph.ArrowSet.elements|> List.map MGraph.Arrow.id |> List.sort Int.compare |> List.rev |> List.hd in
  let ns = MGraph.NodeSet.diff (MGraph.nodes lgraph) (MGraph.nodes limg) in
  let ars = MGraph.ArrowSet.diff (MGraph.arrows lgraph) (MGraph.arrows limg) in
  let c = MGraph.completeToSimpleCompleteGraphWithIDStartFrom limg labels_s idstart in
  let l' = MGraph.unionOfSubGraphs c lgraph in
  l', c, (ns,ars, (l' |> MGraph.src), (l' |> MGraph.dst), l' |> MGraph.labelFuncOf)
*)



(*  cst on h *)
(* 
  let add_cst_on_hs ~env ~model = 
    GraphHomoMap.iter 
    (fun homo hv ->
      let varinds = List.map (fun v -> v.ind) @@ onWhichDepend_ExistenceOfMorphismToTypeGraph homo in 
      let nvars = List.length varinds in
      Lp_grb.add_gen_constr_And ~env ~model 
        ~name:
        (if not cst_name then "" else  Printf.sprintf  "\n[Cst_H_>>>_%s_<<<]\n" @@ name_homo homo """") 
        ~resvar:hv.ind ~nvars ~varinds;
      Lp_grb.update_model env model;
    )
    map_h *)

 (* cst on h *)
 let _ = 
    GraphHomoMap.iter 
    (fun h v ->
      let xs = onWhichDepend_ExistenceOfMorphismToTypeGraph h |> List.map x in 
      let s = List.map v_to_name xs 
                       |> String.concat " " in
      let s = Printf.sprintf  
        "(assert (= %s 
                    (and true %s)
                  )
          )\n" (v_to_name v) s in

      output_string oc s;
      (* if P.semiring = Tropical then output_string oc_tropical s;
      if P.semiring = Arctic then output_string oc_arctic s;
      if P.semiring = Arithmetic then output_string oc_arithmetic s  *)
    )
    map_h
  (* cst on c *)
  let _ = 
    GraphHomoMap.iter 
    (fun c v ->
      let xs = onWhichDepend_ExistenceOfMorphismToTypeGraph c |> List.map x  in 
      let vars_names = List.map (fun e -> List.assoc e !vars) xs in
      let s = String.concat " " vars_names in
      let s = Printf.sprintf 
        "(assert (= %s 
                    (and true %s)
                  )
          )\n" (v_to_name v) s in

      output_string oc s;
      (* if P.semiring = Tropical then output_string oc_tropical s;
      if P.semiring = Arctic then output_string oc_arctic s;
      if P.semiring = Arithmetic then output_string oc_arithmetic s  *)
    )
    map_c
(*
  let weightOfMorphRelativeTo_lp h e = 
    (* G-h-> T <-e- X *)
    let gs = Homo.factorsOfThrought e h in
    gs |> List.length 

  let weightOfMorph h  =  
    measuringMorphismToTypeGraph_l
    |> List.fold_left 
      (fun (inds,vals) e -> 
        let y = y e in 
        let c = weightOfMorphRelativeTo_lp h e in
        (* let inds, vals = if c <> 0 then (y.ind :: inds), ((float_of_int c):: vals) else inds, vals in
         inds, vals *)
         ((y.ind :: inds), ((float_of_int c):: vals))
         )
      ([],[])

  let add_cst_on_h's ~env ~model ~v_to_ind = 
    let graphs = List.map (fun rl -> [Grs.leftGraph rl; Grs.rightGraph rl]) rules_l 
    |> List.flatten
      (* no dupli *)
    |> MGraph.GraphSet.of_list
    |> MGraph.GraphSet.elements in
     let homos = List.map 
        (fun g -> GraphHomoFromTo.homSet g typeGraph) 
        graphs
    (* no dupli *)
    |> List.flatten
    |> GraphHomoSet.of_list 
    |> GraphHomoSet.elements
    in
    List.iter 
    (fun homo -> 
      let hv'ind = h' homo |> v_to_ind in
      let hvind = h homo |> v_to_ind in
      (* Cst : H(h) = 0  --> H'(h) = M  *)
      Lp_grb.add_gen_constr_Indicator ~env ~model ~name:
      (if not cst_name then "" else  (Printf.sprintf"\n[Cst_H'_>>>_%s_h_eq_0_eq_M_<<<]\n" @@ name_homo homo """")) 
      ~binvar:hvind ~binval:0 ~nvars:1 ~varinds:[hv'ind] ~varvals:[1.] ~sense:Lp_grb.Cs.EQ ~rhs:bigM
      ;Lp_grb.update_model env model;
      
      (* Cst : H(h) = 1  --> H'(h) = ...   *)
      let varinds, varvals = weightOfMorph homo in
      let nvars = List.length varinds + 1 in
      Lp_grb.add_gen_constr_Indicator ~env ~model 
      ~name:
      (if not cst_name then "" else   Printf.sprintf "\n[Cst_H'_>>>_%s_h_eq_1_eq_M_<<<]\n" @@ name_homo homo """") 
      ~binvar:hvind ~binval:1 ~nvars
      ~varinds:(hv'ind::varinds) ~varvals:((-1.)::varvals) 
      ~sense:Lp_grb.Cs.EQ ~rhs:0.;
      ;Lp_grb.update_model env model
    )
    homos
*)
(* let weightOfMorphRelativeTo_lp h e = 
  (* G-h-> T <-e- X *)
  let gs = Homo.factorsOfThrought e h in
  gs |> List.length  *)

let weightOfMorph h  =  
  (** h is a morphism to T *)
  List.fold_left 
    (fun (ys,vals) e -> 
      let v_name = y e |> v_to_name in 
      let c = Homo.factorsOfThrought e h |> List.length in
      (* let inds, vals = if c <> 0 then (y.ind :: inds), ((float_of_int c):: vals) else inds, vals in
       inds, vals *)
       if c <> 0 then ((v_name :: ys), (c:: vals))
       else ys,vals
       )
    ([],[])
    measuringMorphismToTypeGraph_l

  let rec ppp l s = 
    if List.length l == 0 then Printf.sprintf "(+ 0 %s)" s else
    (ppp (List.tl l) 
          (Printf.sprintf "%s
                           %s" (List.nth l 0) s))
  let rec ppm l s = 
  if List.length l == 0 then Printf.sprintf "(* 1 %s)" s else
  (ppm (List.tl l) 
        (Printf.sprintf "%s
                          %s" (List.nth l 0) s))
  (* cst on h' *)
  let _ = 
    GraphHomoMap.iter 
    (fun h' v ->
      let y_name_s,cs = weightOfMorph h' in 
      (* tropical , arctic *)
      let exps = List.map2 (fun y_name c -> 
          if integer then Printf.sprintf "(* %s %d)" y_name c
          else Printf.sprintf "(* %s %d.0)" y_name c) 
          y_name_s cs in
      let exp_tropical_arctic = ppp exps "" in
      let s_tropical_arctic =
      Printf.sprintf 
        "(assert (= %s 
                    %s ) )\n" (v_to_name v) exp_tropical_arctic
      in
      if P.semiring = Tropical ||  P.semiring = Arctic then output_string oc s_tropical_arctic;
      (* arithmetic *)
      let exps_arith = List.map2 (fun y_name c -> 
        List.init c (fun _ -> y_name) 
        )
        y_name_s cs in
      let s_arith = (exps_arith |> List.flatten |> ppm) "" 
                    |> Printf.sprintf "(assert (= %s %s))\n" (v_to_name v)  in
      if P.semiring = Arithmetic then output_string oc s_arith;
    )
    map_h' 

  let tk_eq_f_star_something_value tk f = 
    assert(Homo.isSpan tk f);
    (* let gs = GraphHomoFromTo.homSet (Homo.codom f) (Homo.codom tk) in *)
    let gs = GraphHomoFromTo.homSet_fast_with_y_acompletesimplegraph (Homo.codom f) typeGraph labels_l in
    (* to debug homset to fast homset  !!!! tk should be a homo to Type graph *)
    List.filter (fun g -> Homo.isCommutative [f;g] [tk]) gs

  (* cst on k *)
  let _ =
    Map_HomoHomo_mipvar.iter  
    (fun (tk,f) v ->
      let v = v_to_name v in
      let xs = tk_eq_f_star_something_value tk f  in 
      (* tropical, arctic, arithmetic *)
      let ys = xs |> List.map h |> List.map v_to_name in
      let s = String.concat " " ys in
      let s_tropical_arctic_arithmetic = Printf.sprintf  
        "(assert (= %s 
                    (or false %s)
                  )
          )\n" v s in

      output_string oc s_tropical_arctic_arithmetic;
      (* if P.semiring = Tropical then output_string 
        oc_tropical   s_tropical_arctic_arithmetic;
      if P.semiring = Arctic then output_string 
        oc_arctic     s_tropical_arctic_arithmetic;
      if P.semiring = Arithmetic then output_string
        oc_arithmetic s_tropical_arctic_arithmetic *)
    ) 
    map_k 

  (* cst on k' *)
  let _ =
    Map_HomoHomo_mipvar.iter  
    (fun (tk,f) v ->
      let v = v_to_name v in
      let xs = tk_eq_f_star_something_value tk f  in 
      (* tropical *)
      let leqs = xs |>
        List.map (fun x -> 
          let h = h x |> v_to_name in
          let h' = h' x |> v_to_name in
          Printf.sprintf "(=> %s 
                              (<= %s %s)
                          )" 
                            h 
                            v h'
        )
        |> String.concat " "
        in
      let eqs = xs |>
        List.map (fun x -> 
          let h = h x |> v_to_name in
          let h' = h' x |> v_to_name in
          Printf.sprintf "(ite %s 
                               (= %s %s) 
                               false
                          )" 
                            h 
                            v h'
        ) |> String.concat " "
      in
      if P.semiring = Tropical then Printf.fprintf oc
        "(assert (=> %s
                      (and 
                        (and true %s)
                        (or false %s)
                      )
                  )
          )\n" (k tk f |> v_to_name) leqs eqs;
      (* arctic *)
      let geqs = xs |>
        List.map (fun x -> 
          let h = h x |> v_to_name in
          let h' = h' x |> v_to_name in
          Printf.sprintf "(=> %s
                              (>= %s %s)
                          )\n" 
                            h 
                            v h'
        )
        |> String.concat " "
      in
      if P.semiring = Arctic then Printf.fprintf oc
        "(assert (=> %s
                      (and 
                        (and true %s)
                        (or false %s)
                      )
                  )
          )\n" (k tk f |> v_to_name) geqs eqs;
      (** arithmetic *)
      if P.semiring = Arithmetic then begin
        let term_sum = xs |>
          List.map (fun x -> 
            let h = h x |> v_to_name in
            let h' = h' x |> v_to_name in
            Printf.sprintf 
            "(ite %s %s %s)" 
              h h' (if integer then "0" else "0.0")
          )
          |> String.concat " " in
        Printf.fprintf oc
        "(assert (=> %s (= %s (+ 0 %s)
                        )
                  )
          )\n" (k tk f |> v_to_name) v term_sum;
      end 
    ) 
    map_k' 

  (****************************
  (* cst all rules decreasing *)
  *****************************)
  (****************************
  (* cst some rules strictly decreasing *)
  *****************************)
  (* tropical and arctic *)
  let _ = 
    List.iter 
    (fun rl -> 
      let tks = GraphHomoFromTo.homSet_fast_with_y_acompletesimplegraph (Grs.interfaceGraph rl) typeGraph labels_l in 
      (* to debug : fast homset *)
      (* let tks = GraphHomoFromTo.homSet (Grs.interfaceGraph rl) typeGraph in  *)
      let l,r = Grs.lhs rl, Grs.rhs rl in
      List.iter 
      (
          fun tk ->
            (* tropical : cst if {- * l = tk} <> {} then {- * r = tk} <> {} *)
            if P.semiring = Tropical then begin
              Printf.fprintf oc 
              "(assert (=>  %s
                          (and %s
                              (>= %s %s)
                          )
                        )
                )\n\n" (v_to_name @@ k tk l)
                      (v_to_name @@ k tk r) 
                      (v_to_name @@ k' tk l) (v_to_name @@ k' tk r);
              (* tropical uniformly decreasing *)
              Printf.fprintf oc
                "(assert  (=> %s 
                              (and (=> %s %s)
                                  (> %s %s)
                              )
                          )
                  )\n\n" 
                    (v_to_name @@ z rl) 
                    (v_to_name @@ k tk l) (v_to_name @@ k tk r)
                    (v_to_name @@ k' tk l) (v_to_name @@ k' tk r)
                    ;
            end;
            (* arctic : cst if {- * r = tk} <> {} then {- * l = tk} <> {} *)
            if P.semiring = Arctic then begin
              Printf.fprintf oc
              "(assert (=> %s
                          (and %s
                                (>= %s %s)
                          )
                        )
                )\n\n" 
                (v_to_name @@ k tk r)
                (v_to_name @@ k tk l) 
                (v_to_name @@ k' tk l) (v_to_name @@ k' tk r);
                (* arctic  uniformaly decreasing *)
                (* with delta *)
                (* Printf.fprintf oc_arctic
                "(assert  (=> %s 
                              (and (=> %s %s)
                                  (> (- %s %s) %f)
                              )
                          )
                  )\n\n" 
                    (v_to_name @@ z rl) 
                    (v_to_name @@ k tk r) (v_to_name @@ k tk l)
                    (v_to_name @@ k' tk l) (v_to_name @@ k' tk r)
                    delta; *)
                (* no delta *)
                Printf.fprintf oc
                "(assert  (=> %s 
                              (and (=> %s %s)
                                  (> %s %s)
                              )
                          )
                  )\n\n" 
                    (v_to_name @@ z rl) 
                    (v_to_name @@ k tk r) (v_to_name @@ k tk l)
                    (v_to_name @@ k' tk l) (v_to_name @@ k' tk r)
                    ;
            end;
          (* arithmetic : weakly decreasing : cst if {- * r = tk} <> {} then {- * l = tk} <> {} *)
            if P.semiring = Arithmetic then begin
              Printf.fprintf oc
              "(assert (=> %s
                          (and %s
                                (>= %s %s)
                          )
                        )
                )\n\n" 
                (v_to_name @@ k tk r)
                (v_to_name @@ k tk l) 
                (v_to_name @@ k' tk l) (v_to_name @@ k' tk r);
                
            end;
        )
      tks;
      (*  tropical / unrestricted ; arctic / unrestricted
          1. existence of context closure *)
          (* mark flower tropical*)
      let cs = 
        if P.grs.monic_matching |> not then begin
          let flower = MGraph.generate_completeSimpleGraph_of_order 1 labels_l in
          let cs = GraphHomoFromTo.homSet_fast_with_y_acompletesimplegraph flower typeGraph labels_l |> List.map c |> List.map v_to_name in cs
        end else begin
          (* let l = Grs.lhs rl in
            let leftGraph = Homo.codom l in
            let leftGraph' = restricted_to_lK_and_complete_ToSimpleCompleteGraph labels_s l in
            let cs_node_inj = GraphHomoFromTo.homSet_fast_with_y_acompletesimplegraph leftGraph' typeGraph labels_l
            |> Homo.GraphHomoSet.of_list
            |> Homo.GraphHomoSet.filter (Homo.isInjOnNodes) 
            |> Homo.GraphHomoSet.elements in
            let l' = 
              Homo.fromGraphsAndMaps (Homo.dom l) leftGraph' (Homo.hv l) (Homo.he l) in
            let is = GraphHomoFromTo.homSet_fast_with_y_acompletesimplegraph leftGraph leftGraph' labels_l in
            let is_legal =  List.filter (fun i -> Homo.isCommutative [l; i] [l']) is in
            (* 2. for tk = K -l-> L -i-> L' -c-> T *) 
            let prod_card = Batteries.List.cartesian_product is_legal cs_node_inj in
            let context_closures = List.map (fun (i,c) -> Homo.compositionList [i;c]) prod_card in context_closures *)
            (* print_string ("not implemented yet"); *)
            []
        end in
      let s = Printf.sprintf
      "(assert  (=> %s
                    (or false %s)
                )
        )\n" (v_to_name @@ z rl)
        (String.concat " " cs) in
      if P.semiring = Tropical || P.semiring = Arctic then output_string oc s;
      (* arithmetic / unrestricted matching
         1. existence of context closure c and 
         2. for tk = K -l-> L -fl-> Flower -c-> T *)
      let csts = 
        if P.grs.monic_matching |> not then begin
          let flower = MGraph.generate_completeSimpleGraph_of_order 1 labels_l in
          let cs = GraphHomoFromTo.homSet_fast_with_y_acompletesimplegraph flower typeGraph labels_l in 
          (* |> List.map c |> List.map v_to_name*)
          (* let fls = Homo.homSet (Grs.leftGraph rl) flower in *)
          (* to debug fast homset *)
          let fls = GraphHomoFromTo.homSet_fast_with_y_acompletesimplegraph (Grs.leftGraph rl) flower labels_l in
          assert(List.length fls == 1);
          let fl = List.hd fls in
          let tks = List.map (fun c -> Homo.compositionList [l;fl;c]) cs in
          let csts =
            List.map2 
              (fun x tk -> Printf.sprintf 
              (* "(and %s
                    (and %s %s) 
                    (> %s %s)
                )"  
                                      (x |> c |> v_to_name)
                          (v_to_name @@ k tk l)
                            (v_to_name @@ k tk r)
                          (v_to_name @@ k' tk l) (v_to_name @@ k' tk r)
                *)
                "(and %s (> %s %s))" 
                (* (v_to_name @@ k tk l) = true
                            (v_to_name @@ k tk r) = true car tk flower *)
                  (x |> c |> v_to_name)
                  (v_to_name @@ k' tk l) (v_to_name @@ k' tk r)
              ) cs tks in csts
        end else begin
          let l = Grs.lhs rl in
          (* let leftGraph = Homo.codom l in *)
          let leftGraph' = restricted_to_lK_and_complete_ToSimpleCompleteGraph labels_s l in
          let cs_node_inj = GraphHomoFromTo.homSet_fast_with_y_acompletesimplegraph leftGraph' typeGraph labels_l
          |> Homo.GraphHomoSet.of_list
          |> Homo.GraphHomoSet.filter (Homo.isInjOnNodes) 
          |> Homo.GraphHomoSet.elements in
          let l' = 
            Homo.fromGraphsAndMaps (Homo.dom l) leftGraph' (Homo.hv l) (Homo.he l) in
          (* let is = GraphHomoFromTo.homSet_fast_with_y_acompletesimplegraph leftGraph leftGraph' labels_l in
          let is_legal =  List.filter (fun i -> Homo.isCommutative [l; i] [l']) is in *)
          (* 2. for tk = K -l-> L -i-> L' -c-> T *) 
          (* let prod_card = Batteries.List.cartesian_product is_legal cs_node_inj in *)
          (* let context_closures = List.map (fun (i,c) -> Homo.compositionList [i;c]) prod_card in *)
          let tks = List.map (fun c -> Homo.compositionList [l';c]) cs_node_inj  in
          let csts = 
            assert(List.length cs_node_inj == List.length tks);
            List.map2 
              (fun x tk -> Printf.sprintf 
              (* "(and %s
                    (and %s %s) 
                    (> %s %s)
                )"  
                                      (x |> c |> v_to_name)
                          (v_to_name @@ k tk l)
                            (v_to_name @@ k tk r)
                          (v_to_name @@ k' tk l) (v_to_name @@ k' tk r)
                *)
                "(and %s (> %s %s))" 
                (* (v_to_name @@ k tk l) = true
                            (v_to_name @@ k tk r) = true car tk flower *)
                  (x |> c |> v_to_name)
                  (v_to_name @@ k' tk l) (v_to_name @@ k' tk r)
              ) cs_node_inj tks in csts

              (* let context_closures = generate_homos_injOnNodes_from_l_ofOneRule rl in
              let tks = List.map (fun c -> Homo.compositionList [l;c]) context_closures  in
              let csts = 
                assert(List.length context_closures == List.length tks);
                List.map2 
                  (fun x tk -> Printf.sprintf 
                  (* "(and %s
                        (and %s %s) 
                        (> %s %s)
                    )"  
                                          (x |> c |> v_to_name)
                              (v_to_name @@ k tk l)
                                (v_to_name @@ k tk r)
                              (v_to_name @@ k' tk l) (v_to_name @@ k' tk r)
                    *)
                    "(and %s (> %s %s))" 
                    (* (v_to_name @@ k tk l) = true
                                (v_to_name @@ k tk r) = true car tk flower *)
                      (x |> c |> v_to_name)
                      (v_to_name @@ k' tk l) (v_to_name @@ k' tk r)
                  ) context_closures tks in csts *)

              (* let generate_homos_injOnNodes_from_l's_to_typegraph rules = 
          let lhss = List.map Grs.lhs rules in
          let lg's = List.map (fun g -> MGraph.generate_completeSimpleGraph_of_order (Homo.imgOf g |> MGraph.nodes |> MGraph.NodeSet.cardinal) labels_l ) lhss in
          let hs = List.map (fun lg' -> GraphHomoFromTo.homSet_fast_with_y_acompletesimplegraph lg' typeGraph labels_l) lg's 
          |> List.flatten
          |> Homo.GraphHomoSet.of_list
          |> Homo.GraphHomoSet.filter (Homo.isInjOnNodes) 
          |> Homo.GraphHomoSet.elements in
          hs *)
        end in
      let cst = String.concat " " csts in
      let s = Printf.sprintf
      "(assert  (=> %s
                    (or false %s
                    )
                )
        )\n" (v_to_name @@ z rl)
        cst in
      if P.semiring = Arithmetic then output_string oc s;
    )
    rules_l

(* arithmetic *)
(* let _ = 
  List.iter 
  (fun rl -> 
    let tks = GraphHomoFromTo.homSet (Grs.interfaceGraph rl) typeGraph in 
    let l,r = Grs.lhs rl, Grs.rhs rl in
    List.iter 
    (
      fun tk ->
        (* arithmetic : cst if {- * l = tk} <> {} then {- * r = tk} <> {} *)
        Printf.fprintf oc_arithmetic 
        "(assert 
        (=>  
                    (= %s true)
                    (and (= %s true)
                          (>= %s %s)
                    )
                  )
          )\n\n"
          (v_to_name @@ k tk l)
                    (v_to_name @@ k tk r) 
                    (v_to_name @@ k' tk l) (v_to_name @@ k' tk r);
          (* "(assert (>= %s %s))\n\n" 
          (v_to_name @@ k' tk l) 
          (v_to_name @@ k' tk r)*)
    )
  tks;
  (* closure decreasing *)
  (* cst on c *)
  let g = MGraph.generate_completeSimpleGraph_of_order 1 labels_l in
  let hs = GraphHomoFromTo.homSet_fast_with_y_acompletesimplegraph g typeGraph labels_l in
  let f hgt = 
    let hlgs = GraphHomoFromTo.homSet (rl |> GraphRewritingSystem.leftGraph) g in
    assert (List.length hlgs = 1);
    let hlg = List.hd hlgs in
    let tk = GraphHomomorphism.compositionList [l;hlg;hgt]  in 
      Printf.sprintf 
      "(and %s (>= (- %s %s) %f))" 
      (hgt |> c |> v_to_name)
      (k' tk l |> v_to_name)
      (k' tk r |> v_to_name)
      delta
     in
  let s = List.map f hs in 
  let s = String.concat " " s in
  (* monic begin*)
  let s = if P.grs.monic_matching then begin
      let l' = MGraph.completeToSimpleCompleteGraph (rl |> GraphRewritingSystem.leftGraph) labels_s in
      let hl'ts = GraphHomoFromTo.homSet_fast_with_y_acompletesimplegraph l' typeGraph labels_l in
      let f hl't = 
        (* h_k_l' est l mais avec l' comme codomain *)
        let hkl' = 
          GraphHomomorphism.fromGraphsAndMaps (l |> Homo.dom) l' (l |> Homo.hv) (l |> Homo.he) in
        let tk = GraphHomomorphism.compositionList [hkl'; hl't]  in 
          Printf.sprintf 
          "(and %s (>= (- %s %s) %f))" 
          (hl't |> c |> v_to_name)
          (k' tk l |> v_to_name)
          (k' tk r |> v_to_name)
          delta
        in
      let s_monic_matching = (List.map f hl'ts) |>  (fun x -> String.concat " " x) in
      Printf.sprintf "%s %s" s s_monic_matching
    end else s in
  (* monic end *)
  Printf.fprintf oc_arithmetic
      "(assert  (=> (= %s true) (or  %s)))\n\n" 
          (v_to_name @@ z rl)
      s
  )
  rules_l *)

    (* let add_cst_strictly_decreasing_rule ~env ~model ~ind_of_var =
      MapRuleHomo.iter
      (fun (rl,tk) v ->
        let l, r = Grs.lhs rl, Grs.rhs rl in
        Lp_grb.add_gen_constr_Indicator ~env ~model 
        ~name:(if not cst_name then "" else  "\n[Cst__Strictly_Decreasing_>>>_rl_" ^ (string_of_int (indRl_ext rl)) ^ "_tk_" ^ (name_homo tk "" "") ^ "<<<]\n" )
        ~binvar:v.ind ~binval:1 ~nvars:2 ~varinds:[k' tk l |> ind_of_var; k' tk r |> ind_of_var] ~varvals:[1.;-1.] ~sense:Lp_grb.Cs.GT ~rhs:0.01
        ;     Lp_grb.update_model env model;
      )
      map_w   *)

(*
  let indRl_ext rl = List.mapi (fun i rl' -> if Grs.compare rl rl' = 0 then Some i else None) rules_l |> List.map Option.to_list |> List.flatten |> List.hd

  let tk_eq_f_star_something tk f =
    assert(Homo.isSpan tk f);
    let gs = GraphHomoFromTo.homSet (Homo.codom f) (Homo.codom tk) in
    List.filter (fun g -> Homo.isCommutative [f; g] [tk]) gs

  module MapVar = Map.Make(Myvar)
  (* let map_v_id map_id_v = MapInt.bindings !map_id_v |> List.map (fun (x,y) -> (y,x)) |> MapVar.of_list *)
  (* let id map_v_id v = assert(MapVar.mem v map_v_id); MapVar.find v map_v_id *)



  let map_w  = rules_l |> List.mapi
  (fun i rl -> 
    List.map 
      (fun tk ->
        let name =       i |> ignore ;"w_" ^ (string_of_int !nbVars) in
          (* Printf.sprintf "w_%d_%s" i (name_homo tk "" "") in *)
        let v = {name; lb = 0.; ub = 1.; typ = B; ind = !nbVars} in
        nbVars := !nbVars |> succ;
        ((rl, tk),v)
      )
      (GraphHomoFromTo.homSet (Grs.interfaceGraph rl) typeGraph)
  ) 
  |> List.flatten |>List.to_seq |>  MapRuleHomo.of_seq

let w rl tk = 
  assert( MapRuleHomo.mem (rl,tk) map_w );
  MapRuleHomo.find (rl,tk) map_w

let add_cst_on_ws ~env ~model ~ind_of_var =
  MapRuleHomo.iter
  (fun (rl,tk) v ->
    let z_rl = z rl |> ind_of_var in
    let k_tk_l = k tk (Grs.lhs rl) |> ind_of_var in
    Lp_grb.add_gen_constr_And ~env ~model 
    ~name:(if not cst_name then "" else  "\n[Cst_w_>>>_rl_" ^ (string_of_int (indRl_ext rl)) ^ "_tk_" ^ (name_homo tk "" "") ^ "<<<]\n") ~resvar:v.ind ~nvars:2 ~varinds:[z_rl; k_tk_l]
    ;     
    Lp_grb.update_model env model;
  )
map_w

 let add_cst_strictly_decreasing_rule ~env ~model ~ind_of_var =
    MapRuleHomo.iter
    (fun (rl,tk) v ->
      let l, r = Grs.lhs rl, Grs.rhs rl in
      Lp_grb.add_gen_constr_Indicator ~env ~model 
      ~name:(if not cst_name then "" else  "\n[Cst__Strictly_Decreasing_>>>_rl_" ^ (string_of_int (indRl_ext rl)) ^ "_tk_" ^ (name_homo tk "" "") ^ "<<<]\n" )
      ~binvar:v.ind ~binval:1 ~nvars:2 ~varinds:[k' tk l |> ind_of_var; k' tk r |> ind_of_var] ~varvals:[1.;-1.] ~sense:Lp_grb.Cs.GT ~rhs:0.01
      ;     Lp_grb.update_model env model;
    )
    map_w  


  let add_cst_on_cs ~env ~model = 
  GraphHomoMap.iter 
  (fun homo tl' ->
    let varinds = List.map (fun v -> v.ind) @@ mipVars_onWhichDepend_ExistenceOfMorphismToTypeGraph homo in 
    let nvars = List.length varinds in
    (* let name = ("[Cst_C_>>>_" ^ (name_homo homo """") ^ "_<<<]") in *)
    let name = (if not cst_name then "" else  "[Cst_C]") in (* to do : why i can not use 
    "[Cst_C_>>>_" ^ (name_homo homo """") ^ "_<<<]" as name *)
    Lp_grb.add_gen_constr_And ~env ~model ~name
     ~resvar:tl'.ind ~nvars ~varinds;
     Lp_grb.update_model env model;
  )
  map_c
(* 
  let add_cst_context_closure ~env ~model ~ind_of_var = 
    List.iter 
    (fun rl -> 
      let binvar = z rl |> ind_of_var in 
      let l',c',o = calculate_l'_2 rl in
      let tl's = GraphHomoFromTo.homSet_l' l' c' o typeGraph in
      (* let l',_,_ = calculate_l'_2 rl in
      let tl's = GraphHomoFromTo.homSet l' typeGraph in *)
 
      (* let l' = calculate_l' rl in
      let tl's = GraphHomoFromTo.homSet l' typeGraph in *)
      let varinds = tl's |> List.map c |> List.map ind_of_var in
      let varvals = List.map (fun _ -> 1.) varinds in
      let nvars = List.length varvals in
      Lp_grb.add_gen_constr_Indicator ~env ~model ~name:("[Cst_Context_Closure_>>>_rl_" ^ (indRl_ext rl |> string_of_int) ^ "<<<]\n") ~binvar ~binval:1 ~nvars ~varinds ~varvals ~sense:Lp_grb.Cs.GT ~rhs:1.
      ;     Lp_grb.update_model env model;
    )
    rules_l *)


  let add_cst_context_closure ~env ~model ~ind_of_var = 
    List.iter 
    (fun rl -> 
      let binvar = z rl |> ind_of_var in 
      let l' = MGraph.completeToSimpleCompleteGraph (rl |> GraphRewritingSystem.interfaceGraph) labels_s in
      let tl's = GraphHomoFromTo.homSet l' typeGraph in
      (* let l',_,_ = calculate_l'_2 rl in
      let tl's = GraphHomoFromTo.homSet l' typeGraph in *)
 
      (* let l' = calculate_l' rl in
      let tl's = GraphHomoFromTo.homSet l' typeGraph in *)
      let varinds = tl's |> List.map c |> List.map ind_of_var in
      let varvals = List.map (fun _ -> 1.) varinds in
      let nvars = List.length varvals in
      Lp_grb.add_gen_constr_Indicator ~env ~model ~name:(if not cst_name then "" else  "[Cst_Context_Closure_>>>_rl_" ^ (indRl_ext rl |> string_of_int) ^ "<<<]\n") ~binvar ~binval:1 ~nvars ~varinds ~varvals ~sense:Lp_grb.Cs.GT ~rhs:1.
      ;     Lp_grb.update_model env model;
    )
    rules_l
   *)

   let _ = 
    (*  criterion 0: sum z  ; coeff 10000 *)
    let exp_sum_z = 
      let s = 
        List.map (fun (_,v) -> Printf.sprintf"(ite %s 1 0)"
        (v_to_name v) ) (map_z |> RuleMap.bindings) 
      |> String.concat " "  in
      Printf.sprintf 
          "(+ %s)" s in
    (* minimize criterion 2: sum y *)
    let s = List.map (fun (e,v) -> Printf.sprintf"(ite %s %s 0)"
      (v_to_name v)
      (y e|> v_to_name)) (map_x |> GraphHomoMap.bindings) 
    |> String.concat " " 
    in
    let exp_sum_y =  Printf.sprintf 
    "(+ %s)" s in
    (* minimize criterion 3 : sum x  ; *)
    let s = List.map (fun (_,v) -> Printf.sprintf"(ite %s 1 0)" (v_to_name v)) (map_x |> GraphHomoMap.bindings)
    |> String.concat " " in
    let exp_sum_x = Printf.sprintf 
    "(+ %s)" s in
    (* final criterion *)
    let coef_sum_z = 1000000 in
    let coef_sum_y = 1 in
    let coef_sum_x = 1000 in
    let exp = if P.integer then Printf.sprintf "(+ (* %d %s) (- (* %d %s)) (- (* %d %s)))" coef_sum_z exp_sum_z coef_sum_y exp_sum_y coef_sum_x exp_sum_x
    else Printf.sprintf "(+ (* %d %s) (- (* %d %s)))" coef_sum_z exp_sum_z coef_sum_x exp_sum_x in 
    (* let exp = exp_sum_z in *)
    (* let _ = exp_sum_x, exp_sum_y, exp_sum_z, coef_sum_x, coef_sum_y,coef_sum_z in *)
    (* tropical *)
    (* opt = true : rule elimination > nb of arrows > weights of arrows *)


    if P.opt then Printf.fprintf oc "(maximize %s) \n" exp;
        Printf.fprintf oc "(check-sat)\n(get-model)";
    (* if P.semiring = Tropical then 
      begin
        if P.opt then Printf.fprintf oc_tropical "(maximize %s) \n" exp;
        Printf.fprintf oc_tropical "(check-sat)\n(get-model)";
      end;
    if P.semiring = Arctic then 
      begin
        if P.opt then Printf.fprintf oc_arctic "(maximize %s) \n" exp;
        Printf.fprintf oc_arctic "(check-sat)\n(get-model)";
      end;
    if P.semiring = Arithmetic then 
      begin
        if P.opt then Printf.fprintf oc_arithmetic "(maximize %s) \n" exp;
        Printf.fprintf oc_arithmetic "(check-sat)\n(get-model)";
      end; *)
    (* arctic *)
    (* Printf.fprintf oc_arctic "( %s) \n" exp;
    Printf.fprintf oc_arctic "(check-sat)\n(get-model)"; *)
    close_out oc;
    (* close_out oc_arctic;
    close_out oc_tropical;
    close_out oc_arithmetic *)
    (* arithmetic *)
    (* Printf.fprintf oc_arithmetic "( %s) \n" exp;
    Printf.fprintf oc_arithmetic "(check-sat)\n(get-model)";
    close_out oc_arithmetic;; *)
    
end




let file_contains str filename =
  let contains_unsat line =
    let len_line = String.length line in
    let len_unsat = String.length str in
    let rec aux (i:int) =
      if i + len_unsat > len_line then false
      else if String.sub line i len_unsat = str then true
      else aux (i + 1)
    in
    aux 0 in
  let rec check_file ic =
    try
      let line = input_line ic in
      if contains_unsat line then (
        true
      ) else
        check_file ic
    with
    | End_of_file ->
 
      false
  in
  let ic = open_in filename in
  let res = check_file ic in
  close_in ic;
  res
