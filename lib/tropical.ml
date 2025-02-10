(* module MGraph = MGraph 
(* module Cs = ConcretBoundedSemiring *)
(* type l = ConcretBoundedSemiring.lpexp *)
(* type lpexp = {
  varsToBeMaximized : Lp.Poly.t list;
  cstsToBeSatisfied : Lp.Cnstr.t list;
  varOfExp : Lp.Poly.t
} *)
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
(* 

let mul_coeff_z3 z3_inf ctx c1 c2  = 
  (* | inf, _ -> inf
     | _, inf -> inf
     | _ -> c1 + c2 *)
  let open Z3.Boolean in
    mk_ite ctx
    (mk_eq ctx c1 z3_inf)
    z3_inf 
    (mk_ite ctx 
      (mk_eq ctx c2 z3_inf)
      z3_inf
      (Z3.Arithmetic.mk_add ctx [c1;c2])
    )

let add_coeff_z3 z3_inf ~comp ctx c1 c2 =
    (*  | inf, _ -> c2
        | _, inf -> c1
        | _ -> min(c1, c2) *)
  let open Z3.Boolean in
  mk_ite ctx
    (mk_eq ctx c1 z3_inf)
    c2 
    (mk_ite ctx 
      (mk_eq ctx c2 z3_inf)
      c1 
      (mk_ite ctx 
        (comp ctx c1 c2)
        c1 
        c2)) *)
(* 
let generate_constraints_all_var_leq z3_inf ctx elt_z3elt_htbl = 
  let z3_zero = (Z3.Arithmetic.Integer.mk_numeral_i ctx 0) in
  let vars = elt_z3elt_htbl |> Hashtbl.to_seq_values |> List.of_seq |> List.map Array.to_list |> List.flatten |> List.map Array.to_list |> List.flatten in
  let constraints_all_positifs =
  List.map (fun v_exp ->
    Z3.Boolean.mk_or ctx [
    (Z3.Boolean.mk_eq ctx v_exp z3_inf);
    (Z3.Arithmetic.mk_ge 
    ctx 
    v_exp
    z3_zero)
    ]
    ) vars in
  constraints_all_positifs *)
  

module type Parm = sig
  val grs : ConcretGraphRewritingSystems.named_grs
  val size : int
  val integer : bool
  val ub : int
end
 
 
module Make (P:Parm) = struct  
  let rules_l = P.grs.grs 
  let labels_s = (GraphRewritingSystem.RuleSet.of_list P.grs.grs) |> Grs.labels
  let labels_l = (GraphRewritingSystem.RuleSet.of_list P.grs.grs) |> Grs.labels_l 
  let integer = P.integer
  let size = P.size
  let ub = P.ub
  let oc = open_out "./tmp/out.smt2"
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
      |> List.map (fun dom -> GraphHomoFromTo.homSet dom typeGraph)
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
    Printf.sprintf "___%d->%d_%s" s d l 
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
        Printf.fprintf oc "(declare-const %s %s)\n" name  sort_flag;
        (e,v))
      |> List.to_seq |> GraphHomoMap.of_seq

  let y a = 
    (* assert(isMeasuringMorphismToTypeGraph a); *)
    assert(GraphHomoMap.mem a map_y);
    GraphHomoMap.find a map_y;;
    
  let map_z = rules_l |> List.map
  (fun rl -> 
      let name =
        "z_" ^ (string_of_int !nbVars)
      in 
      let bool_sort = Z3.Boolean.mk_sort ctx in
      let v = Z3.Expr.mk_const_s ctx name bool_sort in
      vars := !vars @ [(v,name)];
      nbVars := !nbVars |> succ;     
      Printf.fprintf oc "(declare-const %s Bool)\n" name;
      (rl, v)
  ) |> List.to_seq |>  RuleMap.of_seq

  let z rl = 
    assert( RuleMap.mem rl map_z);
    RuleMap.find rl map_z 

  let map_h = 
    let graphs = List.map (fun rl -> [Grs.leftGraph rl; Grs.rightGraph rl]) rules_l
      |> List.flatten
        (* no dupli *)
      |> MGraph.GraphSet.of_list
      |> MGraph.GraphSet.elements in
    let homos = 
      List.map (fun g -> GraphHomoFromTo.homSet g typeGraph) graphs
    (* no dupli *)
      |> List.flatten
      |> GraphHomoSet.of_list 
      |> GraphHomoSet.elements in
    List.map
      (fun h -> 
        let name =       
          "h_" ^ (string_of_int !nbVars)
          (* Printf.sprintf "h_%d_%s_ind[%d]" i (name_homo h "" "") !nbVars  *)
        in
        let bool_sort = Z3.Boolean.mk_sort ctx in
        let v = Z3.Expr.mk_const_s ctx name bool_sort in
        vars := !vars @ [(v,name)];
        nbVars := !nbVars |> succ;
        Printf.fprintf oc "(declare-const %s Bool)\n" name;
        (h,v)) homos
      |>List.to_seq |> GraphHomoMap.of_seq 
  
  let h x = assert(GraphHomoMap.mem x map_h);
   GraphHomoMap.find x map_h


  let map_c = 
    (* 
    (* let graphs = List.map (fun rl -> calculate_l' rl ) rules_l  *)
    let graphs = List.map (fun rl -> MGraph.completeToSimpleCompleteGraph (rl |> GraphRewritingSystem.interfaceGraph) labels_s ) rules_l 
      (* no dupli *)
      |> MGraph.GraphSet.of_list
      |> MGraph.GraphSet.elements in
    (* Printf.fprintf stdout "|graphs| = %d" (List.length graphs);flush stdout;  *)
    *)
    let gs = [MGraph.generate_completeSimpleGraph_of_order 1 labels_l] in 
    let hs = List.fold_left (fun acc g ->  GraphHomoFromTo.homSet g typeGraph @ acc) [] gs in 
    List.map 
      (fun h -> 
        (* let name = Printf.sprintf "c_%d_%s" i (name_homo h "" "") in *)
        let name = 
          "c_" ^ (string_of_int !nbVars) in
          (* Printf.sprintf "c_%d_%s_ind[%d]" i (name_homo h "" "") !nbVars in *)
        let bool_sort = Z3.Boolean.mk_sort ctx in
        let v = Z3.Expr.mk_const_s ctx name bool_sort in
        vars := !vars @ [(v,name)];
        nbVars := !nbVars |> succ;
        Printf.fprintf oc "(declare-const %s Bool)\n" name;
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
        (fun g -> GraphHomoFromTo.homSet g typeGraph) 
        graphs
    (* no dupli *)
    |> List.flatten
    |> GraphHomoSet.of_list 
    |> GraphHomoSet.elements
    in
    List.map
      (fun h -> 
        let name = 
        "hp_" ^ (string_of_int !nbVars)
          (* Printf.sprintf "h'_%d_%s_ind[%d]" i (name_homo h "" "") !nbVars *)
        in
        let sort = if integer then Z3.Arithmetic.Integer.mk_sort ctx else Z3.Arithmetic.Real.mk_sort ctx in
        let sort_flag = if integer then "Int" else "Real" in
        let v = Z3.Expr.mk_const_s ctx name sort in
        vars := !vars @ [(v,name)];
        nbVars := !nbVars |> succ;
        Printf.fprintf oc "(declare-const %s %s)\n" name  sort_flag;
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
      let tks = GraphHomoFromTo.homSet k typeGraph in
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
          "k_" ^ (string_of_int !nbVars)
          in
          (* Printf.sprintf "k_%d_tk_%s_f_%s" i (name_homo tk "" "") (Homo.toStr f) in *)
        let bool_sort = Z3.Boolean.mk_sort ctx in
        let v = Z3.Expr.mk_const_s ctx name bool_sort in
        vars := !vars @ [(v,name)];
        nbVars := !nbVars |> succ;
        Printf.fprintf oc "(declare-const %s Bool)\n" name;
        ((tk,f),v)
      )
      tmp
    |> List.to_seq |> Map_HomoHomo_mipvar.of_seq in
    map_k 

    

  let map_k' = 
    let left rl = 
      let k = Grs.interfaceGraph rl in 
      let tks = GraphHomoFromTo.homSet k typeGraph in
      List.map (fun tk -> (tk, Grs.lhs rl)) tks in
    let right rl = 
      let k = Grs.interfaceGraph rl in 
      let tks = GraphHomoFromTo.homSet k typeGraph in
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
        "kp_" ^ (string_of_int !nbVars) in
        let sort = if integer then Z3.Arithmetic.Integer.mk_sort ctx else Z3.Arithmetic.Real.mk_sort ctx in
        let sort_flag = if integer then "Int" else "Real" in
        let v = Z3.Expr.mk_const_s ctx name sort in
        vars := !vars @ [(v,name)];
        nbVars := !nbVars |> succ;
        Printf.fprintf oc "(declare-const %s %s)\n" name  sort_flag;
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
      if integer then Printf.fprintf oc 
        (* "(assert (=> 
                    (= %s true) 
                    (and (>= %s 0) 
                         (<= %s %d)
                    )
                  )
          )\n"
           (List.assoc xa !vars) (List.assoc ya !vars) (List.assoc ya !vars) ub
          *)
        "(assert 
                  (and (>= %s 0) 
                      (<= %s %d)
                  )
        )\n"
       (List.assoc ya !vars) (List.assoc ya !vars) ub
      else Printf.fprintf oc 
        (* "(assert (=> 
                    (= %s true) 
                    (and (>= %s 0.0) 
                         (<= %s %d.0)
                    )
                  )
          )\n" 
          (List.assoc xa !vars) (List.assoc ya !vars) (List.assoc ya !vars) ub  *)
          "(assert 
          (and (>= %s 0.0) 
              (<= %s %d.0)
          )
        )\n"
        (List.assoc ya !vars) (List.assoc ya !vars) ub
  ) 
  map_y

  (*



  *)

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
    Printf.fprintf oc 
        "(assert 
        (or %s
        )
    )\n" s 
  

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
      let vars_names = List.map v_to_name xs in
      let s = String.concat " " vars_names in
      Printf.fprintf oc 
        "(assert (= %s 
                    (and %s)
                  )
          )\n" (v_to_name v) s
    )
    map_h

  (* cst on c *)
  let _ = 
    GraphHomoMap.iter 
    (fun c v ->
      let xs = onWhichDepend_ExistenceOfMorphismToTypeGraph c |> List.map x  in 
      let vars_names = List.map (fun e -> List.assoc e !vars) xs in
      let s = String.concat " " vars_names in
      Printf.fprintf oc 
        "(assert (= %s 
                    (and %s)
                  )
          )\n" (v_to_name v) s
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

  (* cst on h' *)
  let _ = 
    GraphHomoMap.iter 
    (fun h' v ->
      let y_name_s,cs = weightOfMorph h' in 
      let exps = List.map2 (fun y_name c -> 
          if integer then Printf.sprintf "(* %s %d)" y_name c
          else Printf.sprintf "(* %s %d.0)" y_name c) 
          y_name_s cs in
      let exp = Printf.sprintf "(+ %s )" (String.concat " " exps) in
      (* let exp = List.fold_left (fun acc x -> Printf.sprintf "(+ %s %s)" acc x ) "" exps in *)
      Printf.fprintf oc 
        "(assert (= %s %s ) )\n" (v_to_name v) exp
    )
    map_h' 

  let tk_eq_f_star_something_value tk f = 
        (** w({g | tk = f star g})
      tk : K -> T
      f : K -> L or K -> R 
      (K,f\in {l,r}) in a certain rule
      *)
    assert(Homo.isSpan tk f);
    let gs = GraphHomoFromTo.homSet (Homo.codom f) (Homo.codom tk) in
    List.filter (fun g -> Homo.isCommutative [f;g] [tk]) gs

  (* cst on k *)
  let _ =
    Map_HomoHomo_mipvar.iter  
    (fun (tk,f) v ->
      let v = v_to_name v in
      let xs = tk_eq_f_star_something_value tk f  in 
      (* cst on k *)
      let ys = xs |> List.map h |> List.map v_to_name in
      let s = String.concat " " ys in
      Printf.fprintf oc 
        "(assert (= %s 
                    (or %s)
                  )
          )\n" v s;
    ) 
    map_k 

  (* cst on k' *)
  let _ =
    Map_HomoHomo_mipvar.iter  
    (fun (tk,f) v ->
      let v = v_to_name v in
      let xs = tk_eq_f_star_something_value tk f  in 
      (* cst on k' *)
      (* let ys = xs |> List.map h' |> List.map v_to_name in
      let leqs = ys |>
        List.map (fun x -> 
          Printf.sprintf "(<= %s %s)" v x
        )
        |> String.concat " "
        in
        let eqs = ys |>
        List.map (fun x -> 
          Printf.sprintf "(= %s %s)" v x
        ) |> String.concat " "
      in *)
      let leqs = xs |>
        List.map (fun x -> 
          let h = h x |> v_to_name in
          let h' = h' x |> v_to_name in
          Printf.sprintf "(ite (= %s true)
                              (<= %s %s)
                              true
                          )\n" 
                            h 
                            v h'
        )
        |> String.concat " "
        in
        let eqs = xs |>
        List.map (fun x -> 
          let h = h x |> v_to_name in
          let h' = h' x |> v_to_name in
          Printf.sprintf "(ite (= %s true)
                              (= %s %s)
                              false
                          )" 
                            h 
                            v h'
        ) |> String.concat " "
      in
      Printf.fprintf oc 
        "(assert (=> (= %s true)
                      (and 
                        %s
                        (or %s)
                      )
                  )
          )\n" (k tk f |> v_to_name) leqs eqs
(* 
          (* cst if {- * l = tk} <> {} then {- * r = tk} <> {} *)
      Printf.fprintf oc 
      "(assert (=>  
                  (= %s true)
                  (= 
                )
        )\n" (v_to_name v) s;  *)
    ) 
    map_k' 

(* cst all rules decreasing *)
  let _ = 
    List.iter 
    (fun rl -> 
      let tks = GraphHomoFromTo.homSet (Grs.interfaceGraph rl) typeGraph in 
      let l,r = Grs.lhs rl, Grs.rhs rl in
      List.iter 
      (
        fun tk ->
          (* cst if {- * l = tk} <> {} then {- * r = tk} <> {} *)
              Printf.fprintf oc 
              "(assert (=>  
                          (= %s true)
                          (and (= %s true)
                               (>= %s %s)
                          )
                        )
                )\n\n" (v_to_name @@ k tk l)
                      (v_to_name @@ k tk r) 
                      (v_to_name @@ k' tk l) (v_to_name @@ k' tk r);
          (* Lp_grb.add_gen_constr_Indicator ~env ~model 
        ~name:(if not cst_name then "" else  "\n[Cst_All_Rules_Decreasing_>>>" ^ "rl_" ^ (indRl_ext rl |> string_of_int) ^ name_homo tk "tk_" "_exist" ^ "<<<]\n") 
        ~binvar:(k tk l |> ind_of_var) 
        ~binval:1 
        ~nvars:1 
        ~varinds:[k tk r |> ind_of_var] 
        ~varvals:[1.] 
        ~sense:Lp_grb.Cs.EQ 
        ~rhs:1.
        ;     Lp_grb.update_model env model;

        Lp_grb.add_gen_constr_Indicator ~env ~model 
        ~name:(if not cst_name then "" else  "\n[Cst_All_Rules_Decreasing_>>>" ^ "rl_" ^ (indRl_ext rl |> string_of_int) ^ name_homo tk "tk_" "_decreasing" ^ "<<<]\n") 
        ~binvar:(k tk l |> ind_of_var) 
        ~binval:1 
        ~nvars:2
        ~varinds:[k' tk l |> ind_of_var;
          let v = k' tk r in
          let ind = ind_of_var v in
          ind] 
        ~varvals:[1.; (-1.)] 
        ~sense:Lp_grb.Cs.GT
        ~rhs:0.
        ;     Lp_grb.update_model env model; *)
        (* add_cst_strictly_decreasing_rule : > *)
        (* Printf.fprintf oc 
        "(assert  (=> (= %s true)
                      (or 
                        (and (= %s false) (= %s false))
                        (=>  
                              (= %s true)
                              (and 
                                  (= %s true)
                                  (> %s %s)
                              )
                        )
                      )
                  )
          )\n" (v_to_name @@ z rl)
               (v_to_name @@ k tk l) (v_to_name @@ k tk r) 
               (v_to_name @@ k tk l)
               (v_to_name @@ k tk r)
               (v_to_name @@ k' tk l) (v_to_name @@ k' tk r); *)
          Printf.fprintf oc 
          "(assert  (=> (= %s true)
                          (=>  
                                (= %s true) 
                                (and 
                                    (= %s true)
                                    (> %s %s)
                                )
                          )
                    )
            )\n\n" (v_to_name @@ z rl)
                (v_to_name @@ k tk l)
                (v_to_name @@ k tk r)
                (v_to_name @@ k' tk l) (v_to_name @@ k' tk r);
      )
    tks;
      (* context closure *)
      (* cst on c *)
      let g = MGraph.generate_completeSimpleGraph_of_order 1 labels_l in
      let hs = GraphHomoFromTo.homSet g typeGraph |> List.map c |> List.map v_to_name in
      Printf.fprintf oc 
      "(assert  (=> (= %s true)
                    (or %s
                    )
                )
        )\n" (v_to_name @@ z rl)
        (String.concat " " hs);
      )
    rules_l

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
    (* minimize criterion 1: sum y *)
    let s' = List.map (fun (e,v) -> Printf.sprintf"(ite %s %s 0)"
      (v_to_name v)
      (y e|> v_to_name)) (map_x |> GraphHomoMap.bindings) 
    |> String.concat " " in
    let s = List.map (fun (_,v) -> Printf.sprintf"(ite %s 1 0)" (v_to_name v)) (map_x |> GraphHomoMap.bindings)
    |> String.concat " " in
    let exp = Printf.sprintf "(+ %s %s)" s' s in
    Printf.fprintf oc "(minimize %s) \n" exp;
    Printf.fprintf oc "(check-sat)\n(get-model)";
    close_out oc;;
end *)
