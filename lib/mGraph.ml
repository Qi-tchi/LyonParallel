
open Printf
module Ulg = UnlabelledDirectedMultGraph
module NodeSet =  Ulg.NodeSet 
module NodeMap = Ulg.NodeMap 
module ArrowSet =  Ulg.ArrowSet 
module ArrowMap =  Ulg.ArrowMap
module Node = Ulg.Node
module Arrow = Ulg.Arrow
module Label = struct 
  type t = string 
  let compare = Stdlib.compare
  let equal x y = compare x y = 0
  let fromStr s = s
  let toStr l = l
end 

module LabelSet = Set.Make(Label)
module Graph = struct 
  type t = {
    g : Ulg.Graph.t;
    l : Label.t ArrowMap.t
  } 
  let compare g g' = 
    let r = Ulg.compare g.g g'.g in 
    if r <> 0 then r else
    ArrowMap.compare Label.compare g.l g'.l
  let equal g g' = compare g g' = 0

  let unlabelled g = g.g;;
  (** # nodes *)
  let order lg = lg |> unlabelled |> Ulg.order

  let size lg = lg |> unlabelled |> Ulg.size
  (** nb of arrows *)
  let empty   = {g = Ulg.empty; l =  ArrowMap.empty}
  let is_empty graph = equal empty graph

  let labelFuncOf (g ) = g.l
  let isArrowOf lg ar = let g = lg |> unlabelled in Ulg.isArrowOf g ar

  let labelOf lg ar = assert (isArrowOf lg ar); ArrowMap.find ar (labelFuncOf lg)

  let nodes g = g |> unlabelled |> Ulg.nodes
  let get_node_list g = nodes g |> NodeSet.elements
  let arrows g = g |> unlabelled |> Ulg.arrows

  let addNewArrow lg ~ar:(u,label,v,id)   =
    let g = unlabelled lg in
    let l = labelFuncOf lg in
    assert (Ulg.isNodeOf g u && Ulg.isNodeOf g v && Ulg.isArrowOf g id |> not); 
    (* let id = Ulg.getNonUsedID g in *)
    (* let arrow = Ulg.Arrow.fromInt id in *)
    {g = Ulg.addArrowWithID g ~ar:(u,v,id); 
    (* {g with arrows =  ArrowSet.add id (Ulg.arrows g);
            src =  ArrowMap.add arrow u (Ulg.src g);
            dst =  ArrowMap.add arrow v (Ulg.dst g)}; *)
     l =  ArrowMap.add id label l
    }
  let addNewArrowNoID lg ~ar:(u,label,v)   =
    let id = Ulg.getNonUsedArrowID (lg |> unlabelled) in
      addNewArrow lg ~ar:(u,label,v,id)
 
  let addNewNode lg   = {lg with g = Ulg.addNewNode (unlabelled lg)}
  let addNode lg id  = {lg with g = Ulg.addNode (lg |> unlabelled) id}
  let isNodeOf lg = Ulg.isNodeOf (unlabelled lg) 

  let fromList ns ars =
    (* add nodes *)
    let ns = List.map Node.fromInt ns in
    let lg = List.fold_right (fun n acc -> addNode acc n) ns empty in
    (* all edges have extremities in vertices *)
    let ars = List.map (fun (u,l, v, id) -> Node.fromInt u, Label.fromStr l, Node.fromInt v, Arrow.fromInt id) ars in
    assert (List.for_all (fun (u,_, v, _) -> isNodeOf lg u && isNodeOf lg v) ars);
    (* add arrows *)
    List.fold_left (fun acc ar -> addNewArrow acc ~ar) lg ars
  let%test "mfromLists" = try fromList [1;2;3] [(1,"a",3,1);(3,"a",2,2)] |> ignore; true with _ -> false;;
  let%test "mfromLists" = try fromList  [1;2;3] [(1,"a",3,1);(3,"a",4,2)] |> ignore; false with _ -> true;; 
  let labels lg = 
    (labelFuncOf lg) |>  ArrowMap.bindings |> List.map snd
    |> LabelSet.of_list
  
  let labelsToStr lg = let ls =  labels lg |> LabelSet.elements in List.map Label.toStr ls |> String.concat ","
  let isGraph lg = 
    Ulg.isGraph (unlabelled lg) && 
    let ldom = (labelFuncOf lg) |>  ArrowMap.bindings |> List.map fst |>  ArrowSet.of_list in
     ArrowSet.equal ldom (lg |> unlabelled |> Ulg.arrows)
  let cleanL lg  = 
     {lg with 
       l =  ArrowMap.filter (fun a _ -> Ulg.isArrowOf (lg |> unlabelled) a) (labelFuncOf lg)} 


  let deleteArrow lg a = 
    assert (isGraph lg && isArrowOf lg a);
    {lg with g = Ulg.deleteArrow (unlabelled lg) a} |> cleanL

  let deleteNodeOfId lg ~n = 
    assert( isGraph lg && isNodeOf lg n );
    let g = lg |> unlabelled in let newg =  Ulg.deleteNode g (Node.fromInt n) in
    {g = newg; l = (labelFuncOf lg)} |> cleanL
  
  let nodesToStr lg = 
    assert (isGraph lg);
    lg |> unlabelled |> Ulg.nodesToStr
  let src lg = Ulg.src (lg |> unlabelled)
  let dst lg = Ulg.dst (lg |> unlabelled)
  let decomp lg = (nodes lg, arrows lg, src lg, dst lg, labelFuncOf lg)
  let dstOf lg ar = 
    assert (isGraph lg && isArrowOf lg ar);
    let g = unlabelled lg in Ulg.dstOf ~g ar
  let srcOf lg ar = 
    assert (isGraph lg && isArrowOf lg ar);
    let g = unlabelled lg in Ulg.srcOf ~g ar
  let srcDstOf lg ar = 
    assert (isGraph lg && isArrowOf lg ar);
    srcOf lg ar, dstOf lg ar
  let arrowToStrNoID ~g:g a = 
    assert (isGraph g && isArrowOf g a);
    let s = String.concat "," [(srcOf g a) |> Node.toStr; labelOf g a |> Label.toStr ; dstOf g a |> Node.toStr] in
    "(" ^ s ^ ")"

  let arrowToStr ~g:g a = 
    assert( isGraph g && isArrowOf g a);
    let s = String.concat "," [(srcOf g a) |> Node.toStr; labelOf g a |> Label.toStr; dstOf g a |> Node.toStr; Arrow.toStr a] in
    "(" ^ s ^ ")"
  let arrows lg = let g = unlabelled lg in Ulg.arrows g
  let arrowsToStr g =
    assert(isGraph g); 
    let ars = arrows g |> ArrowSet.elements
    (* *)
    |> List.sort (fun a1 a2 -> 
                    let c1 = Node.compare (srcOf g a1) (srcOf g a2) in
                    if c1 <> 0 then c1 
                    else  Node.compare (dstOf g a2) (dstOf g a1))
    in
    String.concat ";" (List.map (arrowToStr ~g:g) ars)
    

  let arrowsToStrNoID g = 
    assert(isGraph g);
    let ars = arrows g |> ArrowSet.elements
    (* *)
    |> List.sort (fun a1 a2 -> 
                    let c1 = Node.compare (srcOf g a1) (srcOf g a2) in
                    if c1 <> 0 then c1 
                    else  Node.compare (dstOf g a1) (dstOf g a2))
    in
    String.concat ";" (List.map (arrowToStrNoID ~g:g) ars)
  let toStr g = 
    assert(isGraph g);
    let nodesStr = nodesToStr g in
    let arrowsStr = arrowsToStr g in
    "nodes : [ " ^ nodesStr ^ " ]\n" ^ 
    "arrows : [ " ^ arrowsStr ^ " ]" 
  let toStrNoID g = 
    assert(isGraph g);
    let nodesStr = nodesToStr g in
    let arrowsStr = arrowsToStrNoID g in
    "nodes : [ " ^ nodesStr ^ " ]\n" ^ 
    "arrows : [ " ^ arrowsStr ^ " ]" 



  let%expect_test "" = 
    let g = fromList  [1;2;3] [(1,"a",3,1);(3,"b",2,2)] in 
    g |> toStrNoID |> print_string; print_newline ();
    print_string "labels: "; labelsToStr g |> print_string; print_newline ();
    print_string "add new node 4 and new arrows 1 -c-> 4 ; 2 -d-> 4 \n";
    let g = addNode g 4 |> addNewArrow ~ar:(1,"c",4,3) 
    |> addNewArrow ~ar:(2,"d",4,4) in g
     |> toStrNoID |> print_string; print_newline ();
    print_string "delete arrow 1 -c-> 4\n";
    let g = deleteArrow g 3 in g
    |> toStrNoID |> print_string; print_newline ();
    print_string "delete node 4\n";
    let g = deleteNodeOfId g ~n:4 in g
    |> toStrNoID |> print_string; print_newline ();
    print_string "graph with Id \n";
    g |> toStr |> print_string; print_newline ();
    ;
    [%expect{|
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3);(3,b,2) ]
    labels: a,b
    add new node 4 and new arrows 1 -c-> 4 ; 2 -d-> 4 
    nodes : [ 1;2;3;4 ]
    arrows : [ (1,a,3);(1,c,4);(2,d,4);(3,b,2) ] 
    delete arrow 1 -c-> 4
    nodes : [ 1;2;3;4 ]
    arrows : [ (1,a,3);(2,d,4);(3,b,2) ] 
    delete node 4
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3);(3,b,2) ] 
    graph with Id 
    nodes : [ 1;2;3 ]
    arrows : [ (1,a,3,1);(3,b,2,2) ]
    |}]

  let%test "mfromLists" =
    let g = fromList  [1;2;3] [(1,"a",3,1);(3,"b",2,2)] in 
    let g' = fromList  [1;2;3] [(1,"a",3,1);(3,"b",2,2)] in
    equal g g'
    
  let%test "mfromLists" =
    let g = fromList  [1;2;3] [(1,"a",3,1);(3,"c",2,2)] in 
    let g' = fromList  [1;2;3;4] [(1,"a",3,1);(3,"b",2,2)] in
    let g'' = fromList  [1;2;3] [(2,"a",3,1);(3,"b",2,2)] in
    let g''' = fromList  [1;2;3] [(1,"a",3,1);(3,"b",2,2)] in 
    let g'''' = fromList  [1;2;3] [(1,"a",3,1);(3,"c",2,3)] in 
    equal g g' |> not && (* diff nb nodes *)
    equal g g'' |> not && (* diff arrow source *)
    equal g g''' |> not && (* diff label *)
    equal g g'''' |> not  (* diff id *)
  let isConnected lg = lg |> unlabelled |> Ulg.isConnected

  let canFormSubGraph lg ns ars =
    isGraph lg &&
    Ulg.canFormSubGraph (lg |> unlabelled) ns ars
  let subgraphFrom lg ns ars =
    assert(canFormSubGraph lg ns ars);
    {lg with g = Ulg.subgraphFrom (lg |> unlabelled) ns ars} |> cleanL

  (* let subgraphUnion g h =
  (* g and h are subgraphs of certain graph *)
  let vs = List.dedup_and_sort ((verticesMgraph g) @ h.vertices) ~compare:compareVertex in
  let es = List.dedup_and_sort ((edgesMgraph g) @ h.edges) ~compare:compareEdge in
  mgraphFromVerticesAndEdges vs es *)



  let fromUnlabGraphAndLabFunc_opt g l = let lg = {g;l} in 
    if isGraph lg then Some lg else None
  let subGraphs lg =
    let l, g = labelFuncOf lg, unlabelled lg in
    let unlabSubGraphs = Ulg.subGraphs g in
    let subgraphs = List.map 
      (fun sg -> {g=sg;l} |> cleanL) unlabSubGraphs in
    (* let subgraphs = List.map  preSubgraphs in *)
    (*remark no possible repetition *)
    subgraphs

  let%expect_test "" = 
    let x = fromList [1;2;3] [(1,"s",3,1);(3,"s",2,2)] in
    let sgs = subGraphs x in
    Printf.printf "nb subgraphs : %d\n" (List.length sgs);
    List.iteri (fun i sg ->
      Printf.printf "sg [%d] : %s\n" i (sg |> toStr))
    sgs
    ;[%expect {|
      nb subgraphs : 13
      sg [0] : nodes : [  ]
      arrows : [  ]
      sg [1] : nodes : [ 3 ]
      arrows : [  ]
      sg [2] : nodes : [ 2 ]
      arrows : [  ]
      sg [3] : nodes : [ 2;3 ]
      arrows : [  ]
      sg [4] : nodes : [ 2;3 ]
      arrows : [ (3,s,2,2) ]
      sg [5] : nodes : [ 1 ]
      arrows : [  ]
      sg [6] : nodes : [ 1;3 ]
      arrows : [  ]
      sg [7] : nodes : [ 1;3 ]
      arrows : [ (1,s,3,1) ]
      sg [8] : nodes : [ 1;2 ]
      arrows : [  ]
      sg [9] : nodes : [ 1;2;3 ]
      arrows : [  ]
      sg [10] : nodes : [ 1;2;3 ]
      arrows : [ (3,s,2,2) ]
      sg [11] : nodes : [ 1;2;3 ]
      arrows : [ (1,s,3,1) ]
      sg [12] : nodes : [ 1;2;3 ]
      arrows : [ (1,s,3,1);(3,s,2,2) ]
    |}]


  let%expect_test "" = 
    let x = fromList [1;2;3] [(1,"s",3,1);(3,"0",3,2); (2,"s",3,3)] in
    let sgs = subGraphs x in
    Printf.printf "nb subgraphs : %d\n" (List.length sgs);
    List.iteri (fun i sg ->
      Printf.printf "sg [%d] : %s\n" i (sg |> toStr))
    sgs
    ;[%expect {|
      nb subgraphs : 22
      sg [0] : nodes : [  ]
      arrows : [  ]
      sg [1] : nodes : [ 3 ]
      arrows : [  ]
      sg [2] : nodes : [ 3 ]
      arrows : [ (3,0,3,2) ]
      sg [3] : nodes : [ 2 ]
      arrows : [  ]
      sg [4] : nodes : [ 2;3 ]
      arrows : [  ]
      sg [5] : nodes : [ 2;3 ]
      arrows : [ (2,s,3,3) ]
      sg [6] : nodes : [ 2;3 ]
      arrows : [ (3,0,3,2) ]
      sg [7] : nodes : [ 2;3 ]
      arrows : [ (2,s,3,3);(3,0,3,2) ]
      sg [8] : nodes : [ 1 ]
      arrows : [  ]
      sg [9] : nodes : [ 1;3 ]
      arrows : [  ]
      sg [10] : nodes : [ 1;3 ]
      arrows : [ (3,0,3,2) ]
      sg [11] : nodes : [ 1;3 ]
      arrows : [ (1,s,3,1) ]
      sg [12] : nodes : [ 1;3 ]
      arrows : [ (1,s,3,1);(3,0,3,2) ]
      sg [13] : nodes : [ 1;2 ]
      arrows : [  ]
      sg [14] : nodes : [ 1;2;3 ]
      arrows : [  ]
      sg [15] : nodes : [ 1;2;3 ]
      arrows : [ (2,s,3,3) ]
      sg [16] : nodes : [ 1;2;3 ]
      arrows : [ (3,0,3,2) ]
      sg [17] : nodes : [ 1;2;3 ]
      arrows : [ (2,s,3,3);(3,0,3,2) ]
      sg [18] : nodes : [ 1;2;3 ]
      arrows : [ (1,s,3,1) ]
      sg [19] : nodes : [ 1;2;3 ]
      arrows : [ (1,s,3,1);(2,s,3,3) ]
      sg [20] : nodes : [ 1;2;3 ]
      arrows : [ (1,s,3,1);(3,0,3,2) ]
      sg [21] : nodes : [ 1;2;3 ]
      arrows : [ (1,s,3,1);(2,s,3,3);(3,0,3,2) ]
    |}]
  let isSubGraphOf sg g = Ulg.isSubGraphOf (sg |> unlabelled) (g |> unlabelled)
  let unionOfSubGraphs g g' =  
    let newulg = Ulg.unionOfSubGraphs (unlabelled g) (unlabelled g') in
    let newl = ArrowMap.union 
      (fun _ l1 l2 -> assert(Label.equal l1 l2); Some l1)
      (labelFuncOf g) (labelFuncOf g') in
    match fromUnlabGraphAndLabFunc_opt newulg newl with
    |Some g' -> g'
    |None -> assert(false)

  (* to do todo : debug *)
  let intersectionOfSubGraphs g g' =  
    let newulg = Ulg.intersectionOfSubGraphs (unlabelled g) (unlabelled g') in
    let newl = ArrowMap.filter 
      (fun ar _ -> ArrowSet.mem ar (Ulg.arrows newulg))
      (labelFuncOf g) in
    match fromUnlabGraphAndLabFunc_opt newulg newl with
    |Some g' -> g'
    |None -> assert(false)

  let isProperSubgraph sg g =
    isSubGraphOf sg g &&
    (size sg < size g ||
    order sg < order g)

  let%expect_test "" = 
    let x = fromList [1;2;3] [(1,"s",3,1);(3,"s",2,2)] in
    let sgs = subGraphs x in
    Printf.printf "nb propre subgraphs : %d\n" 
      (List.length (List.filter (fun sg -> isProperSubgraph sg x) sgs));
    List.iteri (fun i sg -> if isProperSubgraph sg x then
      Printf.printf "sg [%d] : %s\n" i (sg |> toStr))
    sgs
    ;[%expect {|
    nb propre subgraphs : 12
    sg [0] : nodes : [  ]
    arrows : [  ]
    sg [1] : nodes : [ 3 ]
    arrows : [  ]
    sg [2] : nodes : [ 2 ]
    arrows : [  ]
    sg [3] : nodes : [ 2;3 ]
    arrows : [  ]
    sg [4] : nodes : [ 2;3 ]
    arrows : [ (3,s,2,2) ]
    sg [5] : nodes : [ 1 ]
    arrows : [  ]
    sg [6] : nodes : [ 1;3 ]
    arrows : [  ]
    sg [7] : nodes : [ 1;3 ]
    arrows : [ (1,s,3,1) ]
    sg [8] : nodes : [ 1;2 ]
    arrows : [  ]
    sg [9] : nodes : [ 1;2;3 ]
    arrows : [  ]
    sg [10] : nodes : [ 1;2;3 ]
    arrows : [ (3,s,2,2) ]
    sg [11] : nodes : [ 1;2;3 ]
    arrows : [ (1,s,3,1) ]
    |}]
  let propreSubgraphs lg = 
    List.filter (fun sg -> isProperSubgraph sg lg) (subGraphs lg)
  let isSingleton g = order g = 1 && size g = 0

  let%test "" = 
    fromList [1] [] |> isSingleton
  let%test "" = 
    fromList [1] [(1,"",1,1)] |> isSingleton |> not

  let arrowsFromTo g s t = 
    let ulg = g |> unlabelled in
    Ulg.arrowsFromTo ulg s t

  let arrowsFromToLabeledBy g s t l = 
    let ars = arrowsFromTo g s t in
    ArrowSet.filter (fun a -> (labelOf g a) |> Label.equal l) ars

  let completeToSimpleCompleteGraph g labels = 
    let nodes = nodes g in
    NodeSet.fold 
      (fun u acc -> NodeSet.fold 
        (fun v acc' -> LabelSet.fold 
          (fun l acc'' -> 
            if arrowsFromToLabeledBy acc'' u v l |> ArrowSet.is_empty
            then addNewArrowNoID acc'' ~ar:(u,l,v)
            else acc'')
          labels 
          acc'
        ) 
      nodes
      acc
      ) 
    nodes
    g

  let generate_completeSimpleGraph_of_order o labels = 
    let vs = List.init o (fun i -> i) in
    let g = fromList vs [] in
    let labels = labels |> LabelSet.of_list in
    completeToSimpleCompleteGraph g labels
  let completeToSimpleCompleteGraphWithIDStartFrom g labels idstart = 
    let id = ref idstart in
    let nodes = nodes g in
    NodeSet.fold 
      (fun u acc -> NodeSet.fold 
        (fun v acc' -> LabelSet.fold 
          (fun l acc'' -> 
            if arrowsFromToLabeledBy acc'' u v l |> ArrowSet.is_empty
            then addNewArrow acc'' ~ar:(u,l,v,(id:=!id+1;!id))
            else acc'')
          labels 
          acc'
        ) 
      nodes
      acc
      ) 
    nodes
    g

  let%expect_test "completeToSimpleCompleteGraph" = 
    let x = fromList [1;2;3] [(1,"s",3,1);(3,"s",2,2)] in
    let labels = ["c"] |> LabelSet.of_list in
    let x' = completeToSimpleCompleteGraph x labels in
    let s = toStr x' in
    printf "%s" s;
    printf "\n|E|= %d" (size x');
    let labels = ["s"] |> LabelSet.of_list in
    let x' = completeToSimpleCompleteGraph x' labels in
    let s = toStr x' in
    printf "\n%s" s;
    printf "\n|E|= %d" (size x');
    ;[%expect {|
    nodes : [ 1;2;3 ]
    arrows : [ (1,s,3,1);(1,c,3,5);(1,c,2,4);(1,c,1,3);(2,c,3,8);(2,c,2,7);(2,c,1,6);(3,c,3,11);(3,s,2,2);(3,c,2,10);(3,c,1,9) ]
    |E|= 11
    nodes : [ 1;2;3 ]
    arrows : [ (1,s,3,1);(1,c,3,5);(1,c,2,4);(1,s,2,13);(1,c,1,3);(1,s,1,12);(2,c,3,8);(2,s,3,16);(2,c,2,7);(2,s,2,15);(2,c,1,6);(2,s,1,14);(3,c,3,11);(3,s,3,18);(3,s,2,2);(3,c,2,10);(3,c,1,9);(3,s,1,17) ]
    |E|= 18
    |}]
end

module GraphSet = Set.Make(Graph)
include Graph

let find_all_arrows_satisfying_property x p =  
  let ars = arrows x |> ArrowSet.elements in
  List.filter p ars

let isCompleteSimpleGraph g ls = 
  let vs = get_node_list g  in
  let uvs = Batteries.List.cartesian_product vs vs in
  List.for_all (fun ((u,v),s)-> arrowsFromToLabeledBy g u v s |> ArrowSet.cardinal |> Int.equal 1) 
  (Batteries.List.cartesian_product uvs ls)

let%test "isCompleteSimpleGraph" = let g = fromList [1;2;3] [(1,"a",3,1);(3,"a",2,2)] in isCompleteSimpleGraph g ["a";"b"] |> not;;
let%test "isCompleteSimpleGraph" = let g = fromList [1;3] 
  [(1,"a",1,1);(1,"b",1,2);
    (1,"a",3,3);(1,"b",3,6);
    (3,"a",3,4);(3,"b",3,5);] in 
  isCompleteSimpleGraph g ["a";"b"] == false;;
let%test "isCompleteSimpleGraph" = let g = fromList [1;3] 
  [(1,"a",1,1);(1,"b",1,2);
    (1,"a",3,3);(1,"b",3,6);
    (3,"a",1,4);(3,"b",1,7);
    (3,"a",3,5);(3,"b",3,8);] in 
  isCompleteSimpleGraph g ["a";"b"];;
let hasIsolatedNode g = 
  unlabelled g |> Ulg.hasIsolatedNode