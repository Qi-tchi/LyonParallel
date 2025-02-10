open GraphHomomorphism
(* let rec homSet g h homos = 
  match MGraph.is_empty g with
  | true -> homos  
  | false -> 
      begin
        match MGraph.arrows g |> MGraph.ArrowSet.elements with
        | ar::ars -> 
            let ar'sH = MGraph.arrows h |>  MGraph.ArrowSet.elements in
            let ar's = ar'sH |> List.filter 
              (fun ar' -> let lar' = MGraph.labelOf h ar' in
                MGraph.Label.equal lar lar') in
            let 
      end *)
(*           
let mapsFromTo dom codom =
  let rec aux dom img res = 
    if dom <> [] then 
      begin
        let sol = ref [] in
        List.iter 
          (fun e -> 
              List.iter 
              (fun r -> sol := ((List.hd dom,e)::r)::!sol)
              res
          ) 
        img;
        aux (List.tl dom) img !sol
      end
    else res in
  aux dom codom [[]] 

  let mapsFromToLabelPreserved dom ldom codom lcodom =
    let rec aux dom img res = 
      match dom with
      | e :: es -> 
        begin
          let le = ArrowMap.find e ldom in
          let sol = ref [] in
          List.iter 
            (fun e' -> 
                let le' = ArrowMap.find e' lcodom in
                if MGraph.Label.equal le le' then
                  List.iter 
                  (fun r -> sol := ((e,e')::r)::!sol)
                  res
            ) 
          img;
          aux es img !sol
        end
      |[] -> res in
    aux dom codom [[]] 

let homSet x y =
  assert (MGraph.isGraph x &&  MGraph.isGraph y);
  let hvs = mapsFromTo (MGraph.nodes x |> NodeSet.elements) (MGraph.nodes y |> NodeSet.elements) in
  let hvs = List.map (fun x -> x |> List.to_seq |> NodeMap.of_seq) hvs in
  let hes = mapsFromToLabelPreserved (MGraph.arrows x |> ArrowSet.elements) 
    (MGraph.labelFuncOf x) 
    (MGraph.arrows y |> ArrowSet.elements) 
    (MGraph.labelFuncOf y) in
  let hes = List.map (fun x -> x |> List.to_seq |> ArrowMap.of_seq) hes  in
  let vsEs = Base.List.cartesian_product hvs hes in
  let homos =  List.filter_map
              (fun (vs,es) -> fromGraphsAndMaps_opt x y vs es) vsEs in 
  homos *)
let addXSthInHe (ns, ars, src, dst, l) (src', dst', l') hv he x y=
  let lx = MGraph.ArrowMap.find x l in
  let ly = MGraph.ArrowMap.find y l' in 
  let sx, dx = MGraph.ArrowMap.find x src, MGraph.ArrowMap.find x dst in
  let sy, dy = MGraph.ArrowMap.find y src', MGraph.ArrowMap.find y dst' in  
  match 
        (if MGraph.Node.equal sx dx then MGraph.Node.equal sy dy else true) 
        (* if x is reflexive then y is reflexive, too *)
        &&
        MGraph.Label.equal lx ly (* label preserved *)
        &&  
        ((NodeMap.exists 
            (fun u v -> 
              (MGraph.Node.equal u sx && (MGraph.Node.equal v sy = false)) ||
              (MGraph.Node.equal u dx && (MGraph.Node.equal v dy = false)))
            hv) |> not) (* src and dst preserved *)
  with
  |false -> None 
  |true -> begin
             let he = assert(ArrowMap.mem x he |> not); ArrowMap.add x y he in
             let ars = assert(ArrowSet.mem x ars); ArrowSet.remove x ars in
             let hv = (NodeMap.add sx sy hv) |> NodeMap.add dx dy in
             let ns = (NodeSet.remove sx ns) |> NodeSet.remove dx in
             Some ((ns, ars, src, dst, l), hv, he) 
           end
           
let%expect_test _ = 
  let typeGraph = 
    let nodeIDs = List.init 2 (fun i -> i) in 
    let g = List.fold_left (fun acc id -> MGraph.addNode acc id) MGraph.empty nodeIDs in
    MGraph.completeToSimpleCompleteGraph g (LabelSet.of_list ["a";"b"]) in
  let rl = ConcretGraphRewritingSystems.bruggink_2014_ex_4_rl_1 in
  let leftGraph = GraphRewritingSystem.leftGraph rl in
  let hs = homSet leftGraph typeGraph in
    print_endline ("L =\n" ^ MGraph.toStr @@ leftGraph); 
    print_endline ("| hs | =" ^ (string_of_int (List.length hs))); 
    print_endline ("typegraph =\n" ^ MGraph.toStr @@ typeGraph); 
  let (ns, ars, src, dst, l),  (_, _, src', dst', l') = MGraph.decomp leftGraph, MGraph.decomp typeGraph in 
  let x,y = 1,1 in
  let lx = MGraph.ArrowMap.find x l in
  let ly = MGraph.ArrowMap.find y l' in 
  let sx, dx = MGraph.ArrowMap.find x src, MGraph.ArrowMap.find x dst in
  let sy, dy = MGraph.ArrowMap.find y src', MGraph.ArrowMap.find y dst' in
    Printf.printf "x=%d y=%d\nlx=%s ly=%s\nsx=%d dx=%d\nsy=%d dy=%d\n" x y lx ly sx dx sy dy;
  let hv = NodeMap.empty in
  let he = ArrowMap.empty in
  let he = assert(ArrowMap.mem x he |> not); ArrowMap.add x y he in
  let ars = assert(ArrowSet.mem x ars); ArrowSet.remove x ars in
  let hv = (NodeMap.add sx sy hv) |> NodeMap.add dx dy in
  let ns = (NodeSet.remove sx ns) |> NodeSet.remove dx in
  let s = Some ((ns, ars, src, dst, l), hv, he) in
  let printints l = List.map string_of_int l |> String.concat " " in
  let printintints l = List.map (fun (x,y) -> ("(" ^ string_of_int x ^ "," ^ string_of_int y ^ ")")) l |> String.concat " " in
  Printf.printf "hv= %s\n" (printintints (hv |> NodeMap.bindings));
  Printf.printf "he= %s\n" (printintints (he |> ArrowMap.bindings));
  Printf.printf "ars= %s\n" (printints (ars |> ArrowSet.elements));
  Printf.printf "ns= %s\n" (printints (ns |> NodeSet.elements));
  (s,printints) |>ignore 
  ;[%expect{|
    L =
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,a,2,2) ]
    | hs | =8
    typegraph =
    nodes : [ 0;1 ]
    arrows : [ (0,a,1,3);(0,b,1,4);(0,a,0,1);(0,b,0,2);(1,a,1,7);(1,b,1,8);(1,a,0,5);(1,b,0,6) ]
    x=1 y=1
    lx=a ly=a
    sx=1 dx=3
    sy=0 dy=0
    hv= (1,0) (3,0)
    he= (1,1)
    ars= 2
    ns= 2
  |}]
let rec aux (ns, ars, src, dst, l) (ns', ars', src', dst', l') hv he =
  match ars |> ArrowSet.elements, ns |> NodeSet.elements with
  | x::_, _ -> 
    let possibilities = 
      List.filter_map 
      (addXSthInHe (ns, ars, src, dst, l) (src', dst', l') hv he x)
      (ars' |> ArrowSet.elements) in
    List.map (fun (a,c,d) -> aux a (ns', ars', src', dst', l') c d) possibilities |> List.flatten
  | [], [] -> [(hv,he)]
  | [], _ -> begin
          let hv's = mapsFromTo (ns |> NodeSet.elements) (ns' |> NodeSet.elements) in
            List.map 
              (fun hv' -> 
                let hv'' = hv' @ (hv |> NodeMap.bindings) |>List.to_seq |>  NodeMap.of_seq in
                    (hv'', he)
              ) 
            hv's
        end


(* module type T = sig
  val addXSthInHe : NodeSet.t * ArrowSet.t * Node.t ArrowMap.t * Node.t ArrowMap.t
  -> NodeSet.t * ArrowSet.t * Node.t ArrowMap.t * Node.t ArrowMap.t 
  -> (Node.t * Node.t) list 
  -> (Arrow.t * Arrow.t) list 
  -> Arrow.t 
  -> Arrow.t ->

    
  val aux : NodeSet.t * ArrowSet.t * Node.t ArrowMap.t * Node.t ArrowMap.t
      -> NodeSet.t * ArrowSet.t * Node.t ArrowMap.t * Node.t ArrowMap.t 
      -> (Node.t * Node.t) list 
      -> (Arrow.t * Arrow.t) list 
      -> ((Node.t * Node.t) * (Arrow.t * Arrow.t)) list
end *)

let pre_process x y = 
  let ns, ars = MGraph.nodes x, MGraph.arrows x |> ArrowSet.elements in
  let nsy = MGraph.nodes y in
  let hvs = mapsFromTo (ns |> NodeSet.elements) (nsy |> NodeSet.elements) 
            |> List.map hvFromList in
  let trivail_arrow_corresp hv ar x y = 
    let (s, t),l = MGraph.srcDstOf x ar, MGraph.labelOf x ar in
    let s',t' = hvX hv s, hvX hv t in
    let ars' = MGraph.find_all_arrows_satisfying_property y
      (fun e -> let s'', t'' = MGraph.srcDstOf y e in
      let l'' = MGraph.labelOf y e in
      MGraph.Label.equal l l'' &&  MGraph.Node.equal s' s'' && MGraph.Node.equal t' t'') in
    assert(List.length ars' = 1);
    (ar, List.hd ars')
  in
  let trivial_he hv ars x y = 
    List.map (fun ar -> trivail_arrow_corresp hv ar x y) ars in
  let hes = List.map
    (fun hv -> trivial_he hv ars x y)
    hvs in
  List.map2 (fun hv he -> hv, he |> ArrowMap.of_list) hvs hes



let homSet_l' l' c o codom =
(** [c] biggest complete graph in l'
    [o] other nodes and arrows of l'
    [y] domain graph 
    same as [homSet] but optimized for l'
    *)
  let tmp = pre_process c codom in
  let y = MGraph.decomp codom in
  let tmp2 = List.map (fun (hv,he) -> aux o y hv he) tmp in
  tmp2
  |> List.flatten
  |> List.map (fun (hv,he) -> fromGraphsAndMaps l' codom hv he)

(* let rec combinations k lst =
  if k = 0 then
    [[]]  (* Base case: one combination of zero elements—the empty list *)
  else
    match lst with
    | [] -> []
    | x :: xs ->
        let with_x = List.map (fun l -> x :: l) (combinations (k - 1) xs) in
        let without_x = combinations k xs in
        with_x @ without_x *)
  
let rec arrangements_with_repetition k lst =
  if k = 0 then
    [[]]  (* Cas de base : une seule liste vide *)
  else
    List.concat_map (fun x ->
      let sub_arrangements = arrangements_with_repetition (k - 1) lst in
      List.map (fun arr -> x :: arr) sub_arrangements
    ) lst

let rec arrangements k lst =
  if k = 0 then
    [[]]  (* Cas de base : une seule liste vide *)
  else
    List.concat_map (fun x ->
      let remaining = List.filter (fun y -> y <> x) lst in
      let sub_arrangements = arrangements (k - 1) remaining in
      List.map (fun arr -> x :: arr) sub_arrangements
    ) lst

let aux_calculate_he (g:MGraph.t) h hv = 
  let g_arrows = MGraph.arrows g |> ArrowSet.elements in
  List.map
  (fun ar -> 
    let (s,t),l = MGraph.srcDstOf g ar, MGraph.labelOf g ar in
    let s',t' = List.assoc s hv, List.assoc t hv in
    let ar' = MGraph.arrowsFromToLabeledBy h s' t' l |> ArrowSet.choose in
    (ar, ar')
  )
  g_arrows

let homSet_fast_with_y_acompletesimplegraph x y labels = 
  let x_nodes = (MGraph.nodes x |> MGraph.NodeSet.elements) in
  assert( MGraph.isCompleteSimpleGraph y labels);
  assert(MGraph.LabelSet.subset (MGraph.labels x) (labels |> MGraph.LabelSet.of_list));
  (* assert( MGraph.order x <= MGraph.order y ); *)
  let hvs = 
    let k = x_nodes |> List.length in
    let y_nodes = (MGraph.nodes y |> MGraph.NodeSet.elements) in
    List.map (Batteries.List.combine x_nodes) (arrangements_with_repetition k y_nodes)
  in
  List.map 
  (fun hv -> 
    let he = aux_calculate_he x y hv in
    fromGraphsAndMaps_exn x y (hv |> NodeMap.of_list) (he |> ArrowMap.of_list)
  ) 
  hvs

 
let%expect_test "homSet_fast_with_y_acompletesimplegraph" = 
  let x = MGraph.fromList [1;2;3] [(2,"count",1,1);(3,"1",1,3)] in
  let y = MGraph.generate_completeSimpleGraph_of_order 2 ["0";"count";"1";"c"] in
  Printf.fprintf stdout "order x:%d\norder y:%d" (MGraph.order x) (MGraph.order y);
  let hs = homSet_fast_with_y_acompletesimplegraph x y ["0";"count";"1";"c"] in
  List.iteri (fun i h -> Printf.fprintf stdout "\n|hs| = %d \nh %d :\n%s" (List.length hs) i (toStr h)) hs;
  [%expect {|
    order x:3
    order y:2
    |hs| = 8
    h 0 :
    dom:
    nodes : [ 1;2;3 ]
    arrows : [ (2,count,1,1);(3,1,1,3) ]
    codom:
    nodes : [ 0;1 ]
    arrows : [ (0,0,1,5);(0,1,1,6);(0,c,1,7);(0,count,1,8);(0,0,0,1);(0,1,0,2);(0,c,0,3);(0,count,0,4);(1,0,1,13);(1,1,1,14);(1,c,1,15);(1,count,1,16);(1,0,0,9);(1,1,0,10);(1,c,0,11);(1,count,0,12) ]
    hv:[(1,0);(2,0);(3,0)]
    he:[(1,4);(3,2)]
    |hs| = 8
    h 1 :
    dom:
    nodes : [ 1;2;3 ]
    arrows : [ (2,count,1,1);(3,1,1,3) ]
    codom:
    nodes : [ 0;1 ]
    arrows : [ (0,0,1,5);(0,1,1,6);(0,c,1,7);(0,count,1,8);(0,0,0,1);(0,1,0,2);(0,c,0,3);(0,count,0,4);(1,0,1,13);(1,1,1,14);(1,c,1,15);(1,count,1,16);(1,0,0,9);(1,1,0,10);(1,c,0,11);(1,count,0,12) ]
    hv:[(1,0);(2,0);(3,1)]
    he:[(1,4);(3,10)]
    |hs| = 8
    h 2 :
    dom:
    nodes : [ 1;2;3 ]
    arrows : [ (2,count,1,1);(3,1,1,3) ]
    codom:
    nodes : [ 0;1 ]
    arrows : [ (0,0,1,5);(0,1,1,6);(0,c,1,7);(0,count,1,8);(0,0,0,1);(0,1,0,2);(0,c,0,3);(0,count,0,4);(1,0,1,13);(1,1,1,14);(1,c,1,15);(1,count,1,16);(1,0,0,9);(1,1,0,10);(1,c,0,11);(1,count,0,12) ]
    hv:[(1,0);(2,1);(3,0)]
    he:[(1,12);(3,2)]
    |hs| = 8
    h 3 :
    dom:
    nodes : [ 1;2;3 ]
    arrows : [ (2,count,1,1);(3,1,1,3) ]
    codom:
    nodes : [ 0;1 ]
    arrows : [ (0,0,1,5);(0,1,1,6);(0,c,1,7);(0,count,1,8);(0,0,0,1);(0,1,0,2);(0,c,0,3);(0,count,0,4);(1,0,1,13);(1,1,1,14);(1,c,1,15);(1,count,1,16);(1,0,0,9);(1,1,0,10);(1,c,0,11);(1,count,0,12) ]
    hv:[(1,0);(2,1);(3,1)]
    he:[(1,12);(3,10)]
    |hs| = 8
    h 4 :
    dom:
    nodes : [ 1;2;3 ]
    arrows : [ (2,count,1,1);(3,1,1,3) ]
    codom:
    nodes : [ 0;1 ]
    arrows : [ (0,0,1,5);(0,1,1,6);(0,c,1,7);(0,count,1,8);(0,0,0,1);(0,1,0,2);(0,c,0,3);(0,count,0,4);(1,0,1,13);(1,1,1,14);(1,c,1,15);(1,count,1,16);(1,0,0,9);(1,1,0,10);(1,c,0,11);(1,count,0,12) ]
    hv:[(1,1);(2,0);(3,0)]
    he:[(1,8);(3,6)]
    |hs| = 8
    h 5 :
    dom:
    nodes : [ 1;2;3 ]
    arrows : [ (2,count,1,1);(3,1,1,3) ]
    codom:
    nodes : [ 0;1 ]
    arrows : [ (0,0,1,5);(0,1,1,6);(0,c,1,7);(0,count,1,8);(0,0,0,1);(0,1,0,2);(0,c,0,3);(0,count,0,4);(1,0,1,13);(1,1,1,14);(1,c,1,15);(1,count,1,16);(1,0,0,9);(1,1,0,10);(1,c,0,11);(1,count,0,12) ]
    hv:[(1,1);(2,0);(3,1)]
    he:[(1,8);(3,14)]
    |hs| = 8
    h 6 :
    dom:
    nodes : [ 1;2;3 ]
    arrows : [ (2,count,1,1);(3,1,1,3) ]
    codom:
    nodes : [ 0;1 ]
    arrows : [ (0,0,1,5);(0,1,1,6);(0,c,1,7);(0,count,1,8);(0,0,0,1);(0,1,0,2);(0,c,0,3);(0,count,0,4);(1,0,1,13);(1,1,1,14);(1,c,1,15);(1,count,1,16);(1,0,0,9);(1,1,0,10);(1,c,0,11);(1,count,0,12) ]
    hv:[(1,1);(2,1);(3,0)]
    he:[(1,16);(3,6)]
    |hs| = 8
    h 7 :
    dom:
    nodes : [ 1;2;3 ]
    arrows : [ (2,count,1,1);(3,1,1,3) ]
    codom:
    nodes : [ 0;1 ]
    arrows : [ (0,0,1,5);(0,1,1,6);(0,c,1,7);(0,count,1,8);(0,0,0,1);(0,1,0,2);(0,c,0,3);(0,count,0,4);(1,0,1,13);(1,1,1,14);(1,c,1,15);(1,count,1,16);(1,0,0,9);(1,1,0,10);(1,c,0,11);(1,count,0,12) ]
    hv:[(1,1);(2,1);(3,1)]
    he:[(1,16);(3,14)]
    |}]


let%expect_test "homSet_fast_with_y_acompletesimplegraph" = 
  let x = MGraph.fromList [1;3] 
  [(1,"a",1,111);(1,"b",1,112);(1,"a",1,113);(1,"b",1,114);
    (1,"a",3,131);(1,"b",3,132);
    (3,"a",1,311);
    (3,"b",3,332);] in
  let y = MGraph.fromList [1;3] 
    [(1,"a",1,1);(1,"b",1,2);
      (1,"a",3,3);(1,"b",3,6);
      (3,"a",1,4);(3,"b",1,7);
      (3,"a",3,5);(3,"b",3,8);] in
  let hs = homSet_fast_with_y_acompletesimplegraph x y ["a";"b"] in
  List.iteri (fun i h -> Printf.fprintf stdout "\n|hs| = %d \nh %d :\n%s" (List.length hs) i (toStr h)) hs;
  [%expect {|
    |hs| = 4
    h 0 :
    dom:
    nodes : [ 1;3 ]
    arrows : [ (1,a,3,131);(1,b,3,132);(1,a,1,111);(1,b,1,112);(1,a,1,113);(1,b,1,114);(3,b,3,332);(3,a,1,311) ]
    codom:
    nodes : [ 1;3 ]
    arrows : [ (1,a,3,3);(1,b,3,6);(1,a,1,1);(1,b,1,2);(3,a,3,5);(3,b,3,8);(3,a,1,4);(3,b,1,7) ]
    hv:[(1,1);(3,1)]
    he:[(111,1);(112,2);(113,1);(114,2);(131,1);(132,2);(311,1);(332,2)]
    |hs| = 4
    h 1 :
    dom:
    nodes : [ 1;3 ]
    arrows : [ (1,a,3,131);(1,b,3,132);(1,a,1,111);(1,b,1,112);(1,a,1,113);(1,b,1,114);(3,b,3,332);(3,a,1,311) ]
    codom:
    nodes : [ 1;3 ]
    arrows : [ (1,a,3,3);(1,b,3,6);(1,a,1,1);(1,b,1,2);(3,a,3,5);(3,b,3,8);(3,a,1,4);(3,b,1,7) ]
    hv:[(1,1);(3,3)]
    he:[(111,1);(112,2);(113,1);(114,2);(131,3);(132,6);(311,4);(332,8)]
    |hs| = 4
    h 2 :
    dom:
    nodes : [ 1;3 ]
    arrows : [ (1,a,3,131);(1,b,3,132);(1,a,1,111);(1,b,1,112);(1,a,1,113);(1,b,1,114);(3,b,3,332);(3,a,1,311) ]
    codom:
    nodes : [ 1;3 ]
    arrows : [ (1,a,3,3);(1,b,3,6);(1,a,1,1);(1,b,1,2);(3,a,3,5);(3,b,3,8);(3,a,1,4);(3,b,1,7) ]
    hv:[(1,3);(3,1)]
    he:[(111,5);(112,8);(113,5);(114,8);(131,4);(132,7);(311,3);(332,2)]
    |hs| = 4
    h 3 :
    dom:
    nodes : [ 1;3 ]
    arrows : [ (1,a,3,131);(1,b,3,132);(1,a,1,111);(1,b,1,112);(1,a,1,113);(1,b,1,114);(3,b,3,332);(3,a,1,311) ]
    codom:
    nodes : [ 1;3 ]
    arrows : [ (1,a,3,3);(1,b,3,6);(1,a,1,1);(1,b,1,2);(3,a,3,5);(3,b,3,8);(3,a,1,4);(3,b,1,7) ]
    hv:[(1,3);(3,3)]
    he:[(111,5);(112,8);(113,5);(114,8);(131,5);(132,8);(311,5);(332,8)]
    |}]

let homSet x y = 
  (aux 
    (MGraph.decomp x)
    (MGraph.decomp y) 
    NodeMap.empty
    ArrowMap.empty
  )
  |> List.map (fun (hv,he) -> fromGraphsAndMaps_exn x y hv he)

let%expect_test _ = 
  let typeGraph = 
    let nodeIDs = List.init 2 (fun i -> i) in 
    let g = List.fold_left (fun acc id -> MGraph.addNode acc id) MGraph.empty nodeIDs in
    MGraph.completeToSimpleCompleteGraph g (LabelSet.of_list ["a";"b"]) in
  let rl = ConcretGraphRewritingSystems.bruggink_2014_ex_4_rl_1 in
  let leftGraph = GraphRewritingSystem.leftGraph rl in
  let hs = homSet leftGraph typeGraph in
    print_endline ("L =\n" ^ MGraph.toStr @@ leftGraph); 
    print_endline ("| hs | =" ^ (string_of_int (List.length hs))); 
    print_endline ("typegraph =\n" ^ MGraph.toStr @@ typeGraph); 
  let (ns, ars, src, dst, l),  (_, ars', src', dst', l') = MGraph.decomp leftGraph, MGraph.decomp typeGraph in 
  let possibilities = 
    List.filter_map  
    (addXSthInHe (ns, ars, src, dst, l) (src', dst', l') (NodeMap.empty) ArrowMap.empty 1) 
    (ars' |> ArrowSet.elements) in 
    print_endline ("|possibilities| " ^ (List.length possibilities |> string_of_int)) ;
  (* let sth =  addXSthInHe (ns, ars, src, dst, l) (src', dst', l') NodeMap.empty ArrowMap.empty 1 1 in
  print_endline (string_of_bool (Option.is_none sth)); *)
  List.iteri (fun i h -> 
    Printf.printf "h %d\n: %s\n" i (toStr h);
  )
  hs
;[%expect {|
    L =
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,a,2,2) ]
    | hs | =8
    typegraph =
    nodes : [ 0;1 ]
    arrows : [ (0,a,1,3);(0,b,1,4);(0,a,0,1);(0,b,0,2);(1,a,1,7);(1,b,1,8);(1,a,0,5);(1,b,0,6) ]
    |possibilities| 4
    h 0
    : dom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,a,2,2) ]
    codom:
    nodes : [ 0;1 ]
    arrows : [ (0,a,1,3);(0,b,1,4);(0,a,0,1);(0,b,0,2);(1,a,1,7);(1,b,1,8);(1,a,0,5);(1,b,0,6) ]
    hv:[(1,0);(2,0);(3,0)]
    he:[(1,1);(2,1)]
    h 1
    : dom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,a,2,2) ]
    codom:
    nodes : [ 0;1 ]
    arrows : [ (0,a,1,3);(0,b,1,4);(0,a,0,1);(0,b,0,2);(1,a,1,7);(1,b,1,8);(1,a,0,5);(1,b,0,6) ]
    hv:[(1,0);(2,1);(3,0)]
    he:[(1,1);(2,3)]
    h 2
    : dom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,a,2,2) ]
    codom:
    nodes : [ 0;1 ]
    arrows : [ (0,a,1,3);(0,b,1,4);(0,a,0,1);(0,b,0,2);(1,a,1,7);(1,b,1,8);(1,a,0,5);(1,b,0,6) ]
    hv:[(1,0);(2,0);(3,1)]
    he:[(1,3);(2,5)]
    h 3
    : dom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,a,2,2) ]
    codom:
    nodes : [ 0;1 ]
    arrows : [ (0,a,1,3);(0,b,1,4);(0,a,0,1);(0,b,0,2);(1,a,1,7);(1,b,1,8);(1,a,0,5);(1,b,0,6) ]
    hv:[(1,0);(2,1);(3,1)]
    he:[(1,3);(2,7)]
    h 4
    : dom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,a,2,2) ]
    codom:
    nodes : [ 0;1 ]
    arrows : [ (0,a,1,3);(0,b,1,4);(0,a,0,1);(0,b,0,2);(1,a,1,7);(1,b,1,8);(1,a,0,5);(1,b,0,6) ]
    hv:[(1,1);(2,0);(3,0)]
    he:[(1,5);(2,1)]
    h 5
    : dom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,a,2,2) ]
    codom:
    nodes : [ 0;1 ]
    arrows : [ (0,a,1,3);(0,b,1,4);(0,a,0,1);(0,b,0,2);(1,a,1,7);(1,b,1,8);(1,a,0,5);(1,b,0,6) ]
    hv:[(1,1);(2,1);(3,0)]
    he:[(1,5);(2,3)]
    h 6
    : dom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,a,2,2) ]
    codom:
    nodes : [ 0;1 ]
    arrows : [ (0,a,1,3);(0,b,1,4);(0,a,0,1);(0,b,0,2);(1,a,1,7);(1,b,1,8);(1,a,0,5);(1,b,0,6) ]
    hv:[(1,1);(2,0);(3,1)]
    he:[(1,7);(2,5)]
    h 7
    : dom:
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,a,2,2) ]
    codom:
    nodes : [ 0;1 ]
    arrows : [ (0,a,1,3);(0,b,1,4);(0,a,0,1);(0,b,0,2);(1,a,1,7);(1,b,1,8);(1,a,0,5);(1,b,0,6) ]
    hv:[(1,1);(2,1);(3,1)]
    he:[(1,7);(2,7)]
    |}]


let%expect_test _ = 
  let typeGraph = MGraph.generate_completeSimpleGraph_of_order 2 ["0";"count";"1";"c"] in
  Printf.fprintf stdout "typegraph:\n%s" (typeGraph |> MGraph.toStr);
  let lp2 = 
    fromList   
    [1;2] [] 
    [1;2;3] [(2,"count",1,1);(3,"1",1,3)]
    [(1,1);(2,2)] [] in
  let inputGraph = codom lp2 in
  Printf.fprintf stdout "\ninput Graph:\n%s" (inputGraph |> MGraph.toStr);
  let hs = homSet inputGraph typeGraph in
  List.iteri (fun i h -> 
  Printf.fprintf stdout "\nh %d:\n%s" i (toStr h)) hs;
  (* let hs' = homSet_fast_with_y_acompletesimplegraph inputGraph typeGraph in
  hs' |> ignore; *)
  (* let eq = GraphHomoSet.equal (hs |> GraphHomoSet.of_list) (hs'|> GraphHomoSet.of_list) in *)
  Printf.fprintf stdout "\nhomSet() = homSet_fast ():" 
;[%expect {|
  typegraph:
  nodes : [ 0;1 ]
  arrows : [ (0,0,1,5);(0,1,1,6);(0,c,1,7);(0,count,1,8);(0,0,0,1);(0,1,0,2);(0,c,0,3);(0,count,0,4);(1,0,1,13);(1,1,1,14);(1,c,1,15);(1,count,1,16);(1,0,0,9);(1,1,0,10);(1,c,0,11);(1,count,0,12) ]
  input Graph:
  nodes : [ 1;2;3 ]
  arrows : [ (2,count,1,1);(3,1,1,3) ]
  h 0:
  dom:
  nodes : [ 1;2;3 ]
  arrows : [ (2,count,1,1);(3,1,1,3) ]
  codom:
  nodes : [ 0;1 ]
  arrows : [ (0,0,1,5);(0,1,1,6);(0,c,1,7);(0,count,1,8);(0,0,0,1);(0,1,0,2);(0,c,0,3);(0,count,0,4);(1,0,1,13);(1,1,1,14);(1,c,1,15);(1,count,1,16);(1,0,0,9);(1,1,0,10);(1,c,0,11);(1,count,0,12) ]
  hv:[(1,0);(2,0);(3,0)]
  he:[(1,4);(3,2)]
  h 1:
  dom:
  nodes : [ 1;2;3 ]
  arrows : [ (2,count,1,1);(3,1,1,3) ]
  codom:
  nodes : [ 0;1 ]
  arrows : [ (0,0,1,5);(0,1,1,6);(0,c,1,7);(0,count,1,8);(0,0,0,1);(0,1,0,2);(0,c,0,3);(0,count,0,4);(1,0,1,13);(1,1,1,14);(1,c,1,15);(1,count,1,16);(1,0,0,9);(1,1,0,10);(1,c,0,11);(1,count,0,12) ]
  hv:[(1,0);(2,0);(3,1)]
  he:[(1,4);(3,10)]
  h 2:
  dom:
  nodes : [ 1;2;3 ]
  arrows : [ (2,count,1,1);(3,1,1,3) ]
  codom:
  nodes : [ 0;1 ]
  arrows : [ (0,0,1,5);(0,1,1,6);(0,c,1,7);(0,count,1,8);(0,0,0,1);(0,1,0,2);(0,c,0,3);(0,count,0,4);(1,0,1,13);(1,1,1,14);(1,c,1,15);(1,count,1,16);(1,0,0,9);(1,1,0,10);(1,c,0,11);(1,count,0,12) ]
  hv:[(1,1);(2,0);(3,0)]
  he:[(1,8);(3,6)]
  h 3:
  dom:
  nodes : [ 1;2;3 ]
  arrows : [ (2,count,1,1);(3,1,1,3) ]
  codom:
  nodes : [ 0;1 ]
  arrows : [ (0,0,1,5);(0,1,1,6);(0,c,1,7);(0,count,1,8);(0,0,0,1);(0,1,0,2);(0,c,0,3);(0,count,0,4);(1,0,1,13);(1,1,1,14);(1,c,1,15);(1,count,1,16);(1,0,0,9);(1,1,0,10);(1,c,0,11);(1,count,0,12) ]
  hv:[(1,1);(2,0);(3,1)]
  he:[(1,8);(3,14)]
  h 4:
  dom:
  nodes : [ 1;2;3 ]
  arrows : [ (2,count,1,1);(3,1,1,3) ]
  codom:
  nodes : [ 0;1 ]
  arrows : [ (0,0,1,5);(0,1,1,6);(0,c,1,7);(0,count,1,8);(0,0,0,1);(0,1,0,2);(0,c,0,3);(0,count,0,4);(1,0,1,13);(1,1,1,14);(1,c,1,15);(1,count,1,16);(1,0,0,9);(1,1,0,10);(1,c,0,11);(1,count,0,12) ]
  hv:[(1,0);(2,1);(3,0)]
  he:[(1,12);(3,2)]
  h 5:
  dom:
  nodes : [ 1;2;3 ]
  arrows : [ (2,count,1,1);(3,1,1,3) ]
  codom:
  nodes : [ 0;1 ]
  arrows : [ (0,0,1,5);(0,1,1,6);(0,c,1,7);(0,count,1,8);(0,0,0,1);(0,1,0,2);(0,c,0,3);(0,count,0,4);(1,0,1,13);(1,1,1,14);(1,c,1,15);(1,count,1,16);(1,0,0,9);(1,1,0,10);(1,c,0,11);(1,count,0,12) ]
  hv:[(1,0);(2,1);(3,1)]
  he:[(1,12);(3,10)]
  h 6:
  dom:
  nodes : [ 1;2;3 ]
  arrows : [ (2,count,1,1);(3,1,1,3) ]
  codom:
  nodes : [ 0;1 ]
  arrows : [ (0,0,1,5);(0,1,1,6);(0,c,1,7);(0,count,1,8);(0,0,0,1);(0,1,0,2);(0,c,0,3);(0,count,0,4);(1,0,1,13);(1,1,1,14);(1,c,1,15);(1,count,1,16);(1,0,0,9);(1,1,0,10);(1,c,0,11);(1,count,0,12) ]
  hv:[(1,1);(2,1);(3,0)]
  he:[(1,16);(3,6)]
  h 7:
  dom:
  nodes : [ 1;2;3 ]
  arrows : [ (2,count,1,1);(3,1,1,3) ]
  codom:
  nodes : [ 0;1 ]
  arrows : [ (0,0,1,5);(0,1,1,6);(0,c,1,7);(0,count,1,8);(0,0,0,1);(0,1,0,2);(0,c,0,3);(0,count,0,4);(1,0,1,13);(1,1,1,14);(1,c,1,15);(1,count,1,16);(1,0,0,9);(1,1,0,10);(1,c,0,11);(1,count,0,12) ]
  hv:[(1,1);(2,1);(3,1)]
  he:[(1,16);(3,14)]
  homSet() = homSet_fast ():
    |}]
