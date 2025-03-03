
(* 
#require "unix"
#require "stdio"
  *)
  (* open Base *)
  module Arrow = struct
    type t = Int.t
    let compare = Int.compare
    let equal = Int.equal;;
    let id x = x;;
    let fromInt x = x
    let toStr = string_of_int
  end

  module Node = struct
    type t = Int.t
    let compare = Int.compare
    let equal = Int.equal
    let id x = x
    let fromInt x = x
    let toStr = string_of_int
  end

  module NodeSet = Set.Make(Node)
  module NodeMap = Map.Make(Node)
  module ArrowSet = Set.Make(Arrow)
  module ArrowMap = Map.Make(Arrow)

  module Graph = struct 
    type t = {
    nodes : NodeSet.t;
    arrows : ArrowSet.t;
    src : Node.t ArrowMap.t ;
    dst : Node.t ArrowMap.t;
    }
    let compare g g' = 
      let r = NodeSet.compare g.nodes g'.nodes in
      if r <> 0 then r else
      let r = ArrowSet.compare g.arrows g'.arrows in
      if r <> 0 then r else
      let r = ArrowMap.compare Node.compare g.src g'.src in
      if r <> 0 then r else
      ArrowMap.compare Node.compare g.dst g'.dst
    let equal g g' = compare g g' = 0
  end
  include Graph
  module GraphSet = Set.Make(Graph)
  module GraphMap = Map.Make(Graph)
  let arrows g = g.arrows
  let nodes g = g.nodes
  let src g = g.src
  let dst g = g.dst
  let order g = NodeSet.cardinal (nodes g)
  let size g = ArrowSet.cardinal ( arrows g)

  (* let nodesList g = nodes g |> NodeSet.elements
  let arrowsList g =  arrows g |> ArrowSet.elements *)
(* 
  let domSrcList g = g |> src |> ArrowMap.bindings |> List.map fst 
  let domSrcSet g = g |> domSrcList |> ArrowSet.of_list

  let imgSrcList g = g |> src |> ArrowMap.bindings |> List.map snd 
  let imgSrcSet  g = g |> imgSrcList |> NodeSet.of_list

  let domDstList g = g |> dst |> ArrowMap.bindings |> List.map fst 
  let domDstSet g = g |> domSrcList |> ArrowSet.of_list

  let imgDstList g = g |> dst |> ArrowMap.bindings |> List.map snd 
  let imgDstSet  g = g |> imgSrcList |> NodeSet.of_list *)

let isGraph g = 
  let src, dst = src g, dst g in
  let domSrc, imgSrc = 
    ArrowMap.bindings src |> List.map fst |> ArrowSet.of_list, 
    ArrowMap.bindings src |> List.map snd |> NodeSet.of_list in
  let domDst, imgDst = 
    ArrowMap.bindings dst |> List.map fst |> ArrowSet.of_list, 
    ArrowMap.bindings dst |> List.map snd |> NodeSet.of_list in
  ArrowSet.equal domSrc  ( arrows g) &&
  ArrowSet.equal domDst ( arrows g) &&
  NodeSet.subset imgSrc (nodes g) &&
  NodeSet.subset imgDst (nodes g)
let isSubGraphOf sg g = 
  (NodeSet.subset (nodes sg) (nodes g)) &&
  (ArrowSet.subset (arrows sg) (arrows g)) 

  let srcOf ~g:g ar = 
    let src = src g in
    assert(ArrowMap.mem ar src);
    ArrowMap.find ar src
  
  let dstOf ~g:g ar = 
    let dst = dst g in
    assert(ArrowMap.mem ar dst);
    ArrowMap.find ar dst

  let isArrowOf g a = ArrowSet.mem a ( arrows g)

  let isNodeOf g v = NodeSet.mem v (nodes g)

  (* debug funcs begin *)
  let nodesToStr g = 
    String.concat ";" (List.map Node.toStr (nodes g |> NodeSet.elements))


  let arrowToStrNoID ~g:g a = 
    let s = String.concat "," [(srcOf ~g:g a) |> Node.toStr; dstOf ~g:g a |> Node.toStr] in
    "(" ^ s ^ ")"

  let arrowToStrWithID ~g:g a = 
    let s = String.concat "," [(srcOf ~g:g a) |> Node.toStr; dstOf ~g:g a |> Node.toStr; Arrow.toStr a] in
    "(" ^ s ^ ")"

  let arrowsOfGraphToString g = 
    let ars = arrows g |> ArrowSet.elements 
    (* *)
    |> List.sort (fun a1 a2 -> 
       let c1 = Node.compare (srcOf ~g a1) (srcOf ~g a2) in
       if c1 <> 0 then c1 
       else  Node.compare (dstOf ~g a2) (dstOf ~g a1))
    in
    String.concat ";" (List.map (arrowToStrWithID ~g:g) ars)
    
  let arrowsToStrNoID g = 
    let ars = arrows g |> ArrowSet.elements 
    (* *)
    |> List.sort (fun a1 a2 -> 
       let c1 = Node.compare (srcOf ~g a1) (srcOf ~g a2) in
       if c1 <> 0 then c1 
       else  Node.compare (dstOf ~g a1) (dstOf ~g a2))
    in
    String.concat ";" (List.map (arrowToStrNoID ~g:g) ars)
  
  let toStrNoID g = 
    let nodesStr = nodesToStr g in
    let arrowsStr = arrowsToStrNoID g in
    "nodes : [ " ^ nodesStr ^ " ]\n" ^ 
    "arrows : [ " ^ arrowsStr ^ " ]" 

  (* debug funcs end *)

  let getNonUsedNodeID g = 
    match NodeSet.max_elt_opt (nodes g) with
    |None -> 1
    |Some x -> Node.id x |> succ

  let addNewNode g = 
    assert(isGraph g);
    let id = getNonUsedNodeID g in
    let node = Node.fromInt id in
    {g with nodes = NodeSet.add node (nodes g)}
  (** add a node with identifier [id] if not exist *)
  let addNode g id = 
    assert (isGraph g);
    {g with nodes = NodeSet.add id (nodes g)}

  let empty = 
    {nodes = NodeSet.empty; arrows = ArrowSet.empty; src = ArrowMap.empty; dst  = ArrowMap.empty}

  let%expect_test _ = let g = empty in
    (* add 3 nodes *)
    g |> addNewNode |> addNewNode |> addNewNode
    (* print node-IDs *)
    |> nodesToStr |> print_string;
    [%expect{|1;2;3|}]

  let getNonUsedArrowID g = match ArrowSet.max_elt_opt ( arrows g) with
    |None -> Arrow.fromInt 1
    |Some x -> Arrow.id x |> succ |> Arrow.fromInt

  let addArrowWithID g ~ar:(s,t,id) = 
    assert(isGraph g);
    assert(isNodeOf g s && isNodeOf g t);
    (* assert(isArrowOf g a |> not); *)
    {g with arrows = ArrowSet.add id ( arrows g);
            src = ArrowMap.add id s (src g);
            dst = ArrowMap.add id t (dst g);
    }

  let addNewArrow g ~ar:(s,t) =
    assert (isGraph g && isNodeOf g s && isNodeOf g t);
    let id = getNonUsedArrowID g in
    addArrowWithID g ~ar:(s,t,id)


  let%expect_test _ = let g = empty in
    (* add 3 nodes *)
    g |> addNewNode |> addNewNode |> addNewNode
    (* add 3 arrows *)
    |> addNewArrow ~ar:(1,2)  |> addNewArrow ~ar:(2,3) |> addNewArrow ~ar:(1,3)
    (* print node-IDs *)
    |>  arrowsToStrNoID |> print_string;
    [%expect{|(1,2);(1,3);(2,3)|}]
(* 
  let fromList n ars =
    let g = empty in
    (* add nodes *)
    let ns = List.init n (fun i -> i) in
    let g = List.fold_left (fun acc _ -> addNewNode acc) g ns in
    (* all edges have extremities in vertices *)
    let ars = List.map (fun (u,v) -> Node.fromInt u, Node.fromInt v) ars in
    assert (List.for_all (fun (u,v) -> isNodeOf
    g u && isNodeOf g v) ars);
    (* add arrows *)
    List.fold_left (fun acc ar -> addNewArrow acc ~a:ar) g ars *)
  let fromList ns ars =
      (* add nodes *)
      let ns = List.map Node.fromInt ns in
      let g = List.fold_right (fun n acc -> 
        (* no repetition *)
        assert(isNodeOf acc n |> not) ; 
        (* add *)
        addNode acc n) ns empty in
      (* add arrows *)
      let ars = List.map (fun (u, v, id) -> Node.fromInt u, Node.fromInt v, Arrow.fromInt id) ars in
      List.fold_left 
      (fun acc (u, v, ar) -> 
        (* well defined arrow *)
        assert(List.mem u ns && List.mem v ns);
        (* no repetition *)
        assert(isArrowOf acc ar |> not);
        addNewArrow acc ~ar:(u,v)) g ars
let fromSetsMaps nodes arrows src dst = 
  let g = {nodes;arrows;src;dst} in assert(isGraph g); g
  let cleanSrc g = 
    {g with src = ArrowMap.filter (fun a _ -> isArrowOf g a ) (src g)} 

  let cleanDst g = 
    {g with dst = ArrowMap.filter (fun a _ -> isArrowOf g a) (dst g)} 

  let cleanArrows g = 
    {g with arrows = ArrowSet.filter   
        (fun arrow -> srcOf ~g arrow |> isNodeOf g &&
         dstOf ~g arrow |> isNodeOf g) ( arrows g)}

  let isGraphAfterCleanDstAndSrc g = 
    g |> cleanDst |> cleanSrc |> isGraph
 
  let%expect_test "" = 
    let g = fromList [1;2;3] [(1,3, 1);(3,2, 2)] in 
    g |> toStrNoID |> print_string; print_newline ();
    Printf.printf "%b\n" (isGraph g);
    let g' = {g with src = ArrowMap.add 3 1 g.src} in
    isGraph g' |> Printf.printf "%b\n";
    isGraphAfterCleanDstAndSrc g' |> Printf.printf "%b\n";
    let g'' = g' |> cleanDst |> cleanSrc in
    print_string (g'' |>toStrNoID ); print_newline ();
    [%expect{|
    nodes : [ 1;2;3 ]
    arrows : [ (1,3);(3,2) ]
    true
    false
    true
    nodes : [ 1;2;3 ]
    arrows : [ (1,3);(3,2) ]
    |}]

  let isEmpty ~g:g = 
    nodes g |> NodeSet.is_empty

  let isArrowFromTo ~g ~a s t = 
    assert(isGraph g);
    assert(isArrowOf g a);
    Node.equal (srcOf ~g a) s && Node.equal (dstOf ~g a) t
    
  let hasArrowFromTo g s t = 
    let ars =  arrows g in 
    ArrowSet.exists (fun a -> isArrowFromTo ~g ~a s t) ars

  let%test _ = try fromList [1;2;3] [(1,3,1);(3,4,2)] |> ignore; false with _ -> true;;
  
  let%test _ = let g = fromList  [1;2;3] [(1,3,1);(3,2,2)] in hasArrowFromTo g (Node.fromInt 1) (Node.fromInt 3)
  let%test _ = let g = fromList  [1;2;3] [(1,3,1);(3,2,2)] in hasArrowFromTo g (Node.fromInt 1) (Node.fromInt 2) |> not
  (* end test *) 

  let incidentArrowNode g (arrow:Arrow.t) (node:Node.t) = 
    (dstOf ~g:g arrow = node || srcOf ~g:g arrow = node)
  let incidentAndNotIncidentEdges g v = 
  let incidentEdges, notincidentEdges =
    ArrowSet.partition (fun arrow -> incidentArrowNode g arrow v) ( arrows g) in
    incidentEdges |> ArrowSet.elements, notincidentEdges |>ArrowSet.elements
  
  let hasArrowFromTo g u v : bool = 
    ArrowSet.exists (fun ar -> srcOf ~g:g ar = u && dstOf ~g:g ar = v) ( arrows g)

  let incidentAndNotIncidentVertices g v = 
    let incidentVertices, notincidentVertices = 
    NodeSet.partition (fun u -> hasArrowFromTo g u v || hasArrowFromTo g v u) (nodes g) in
    (* remove v *)
    incidentVertices |> NodeSet.remove v,
     notincidentVertices |>NodeSet.remove v

  let%expect_test _ = 
    let g = fromList  [1;2;3] [(1,3,1);(3,2,2)] in 
    let incs, nincs = incidentAndNotIncidentVertices g 3 in
    Printf.printf "%b %b\n" (NodeSet.equal incs (NodeSet.of_list [1;2])) (NodeSet.is_empty nincs);
    [%expect{|
    true true
    |}]

  let deleteArrow g ar = 
    assert(isGraph g);
    let g = {g with arrows = ArrowSet.remove ar ( arrows g)} in
    cleanDst g |> cleanSrc

  let%expect_test _ = 
    let g = fromList  [1;2;3] [(1,3,1);(3,2,2)] in 
    print_string (g |> toStrNoID); print_newline ();
    let g= deleteArrow g (Arrow.fromInt 1) in
    print_string (g |> toStrNoID); print_newline ();
    [%expect{|
    nodes : [ 1;2;3 ]
    arrows : [ (1,3);(3,2) ]
    nodes : [ 1;2;3 ]
    arrows : [ (3,2) ]
    |}]
  
  let deleteNode g v = 
    {g with nodes = NodeSet.remove v (nodes g)} 
    |> cleanArrows |> cleanSrc |> cleanDst
  
  let%expect_test "deleteNode" = 
    let g = fromList  [1;2;3] [(1,3,1);(3,2,2)] in 
    print_string (nodesToStr g); print_newline () ;
    print_string (arrowsToStrNoID g);print_newline () ;
    let g= deleteNode g (Node.fromInt 1) in
    print_string (nodesToStr g); print_newline () ;
    print_string (arrowsToStrNoID g);
    [%expect{|
    1;2;3
    (1,3);(3,2)
    2;3
    (3,2)
    |}]


  let indegre g (v:Node.t) = 
    assert(isNodeOf g v);
    ArrowSet.filter 
      (fun ar -> Node.equal (dstOf ~g:g ar) v) 
      (arrows g)
    |> ArrowSet.cardinal


  let%expect_test "indegre" = 
    let g = fromList  [1;2;3] [(1,3,1);(3,2,2)] in 
    print_endline (indegre g 1 |> string_of_int);
    print_endline (indegre g 2 |> string_of_int);
    [%expect{|
    0
    1
    |}]

  let outdegre g (v:Node.t) = 
    assert(isNodeOf g v);
    ArrowSet.filter 
      (fun ar -> Node.equal (srcOf ~g:g ar) v) 
      (arrows g)
    |> ArrowSet.cardinal

  let%expect_test "outdegre" = 
    let g = fromList  [1;2;3] [(1,3,1);(3,2,2);(1,2,3);] in 
    print_endline (outdegre g 1 |> string_of_int);
    print_endline (outdegre g 2 |> string_of_int);
    [%expect{|
    2
    0
    |}]

  let isIsolatedNode g v = 
    assert (isNodeOf g v);
  indegre g v = 0 && outdegre g v = 0

  let%expect_test "isIsolatedNode" = 
    let g = fromList  [1;2;3;4] [(1,3,1);(3,2,2);(1,2,3);] in 
    print_endline (isIsolatedNode g 1 |> string_of_bool);
    print_endline (isIsolatedNode g 4 |> string_of_bool);
    [%expect{|
    false
    true
    |}]

  let hasIsolatedNode g = 
    NodeSet.exists (fun n -> isIsolatedNode g n) (nodes g)

  let%expect_test "isIsolatedNode" = 
    let g = fromList  [1;2;3;4] [(1,3,1);(3,2,2);(1,2,3);] in 
    print_endline (hasIsolatedNode g |> string_of_bool);
    let g = deleteNode g 4 in
    print_endline (hasIsolatedNode g |> string_of_bool);
    [%expect{|
    true
    false
    |}]

  let isConnected g = 
      let rec virus us g =
        match us with 
        | [] -> g
        | v::vs -> 
        begin
          let incidentVertices, _ = incidentAndNotIncidentVertices g v in
          let g' = deleteNode g v in virus (vs @ (incidentVertices |> NodeSet.elements)) g'
        end
      in
      let g' = match (nodes g)|> NodeSet.elements with 
      |[] -> g
      |v::_ -> virus [v] g in
      if isEmpty ~g:g' then true else false 
  
  (* begin test *)
  let%test "_" = 
     let g = fromList  [1;2;3] [(1,3,1);(3,2,2)] in
      isConnected g
  let%test "_" = 
     (fromList  [1;2;3;4] [(1,3,1);(3,2,2)]) 
     |>  isConnected |> not
  (* end test *)
  
  (* let powerset = BatSet. *)
  let rec powerset = function
  | [] -> [[]]  (* Base case: powerset of an empty set is a set containing the empty set *)
  | x :: xs ->
      let rest_powerset = powerset xs in
      rest_powerset @ List.map (fun subset -> x :: subset) rest_powerset 
  (* let setProduct xs ys =  
    List.fold_left  (fun acc x -> 
      List.fold_left (fun acc' y -> (x, y)::acc') acc ys )
      [] xs *)

  let canFormSubGraph g ns ars =
    isGraph g &&
    NodeSet.for_all (fun n -> isNodeOf g n) ns &&
    ArrowSet.for_all (fun a -> isArrowOf g a) ars &&
    ArrowSet.for_all (fun a ->
    NodeSet.mem (srcOf ~g a) ns &&
    NodeSet.mem (dstOf ~g a) ns) 
           ars
  let subgraphFrom g ns ars =
    {g with nodes = ns; arrows = ars} |> cleanSrc |> cleanDst
  (* let subgraphFrom_opt ~g ns ars =
    assert(List.for_all (fun n -> isNodeOf g n) ns);
    assert(List.for_all (fun a -> isArrowOf g a) ars);
    try 
      let sg = {empty with nodes = ns |> NodeSet.of_list} in
      let sg = List.fold_left (fun acc ar -> addArrowWithID g:acc ar (srcOf ~g ar) (dstOf ~g ar)) sg ars in
      Some sg
    with _ -> None *)
  let subGraphs g = 
    let ns, ars = nodes g |> NodeSet.elements , arrows g |> ArrowSet.elements  in
    let ns_powersets, ars_powersets = powerset ns, powerset ars in
    let candidats = Base.List.cartesian_product ns_powersets ars_powersets in
    let candidats = List.map (fun (ns,ars) -> (NodeSet.of_list ns, ArrowSet.of_list ars)) candidats in
    let candidats = List.filter (fun (ns,ars) -> canFormSubGraph g ns ars) candidats in
    List.map (fun (ns,ars) -> subgraphFrom g ns ars) candidats
    (* |> GraphSet.of_list *)
  (* begin test *)
  let%expect_test "" = 
    let x = fromList [1;2;3] [(1,3,1);(3,2,2)] in
    let sgs = subGraphs x in
    Printf.printf "nb subgraphs : %d\n" (List.length sgs);
    List.iteri (fun i sg ->
      Printf.printf "sg [%d] : %s\n" i (sg |> toStrNoID))
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
    arrows : [ (3,2) ]
    sg [5] : nodes : [ 1 ]
    arrows : [  ]
    sg [6] : nodes : [ 1;3 ]
    arrows : [  ]
    sg [7] : nodes : [ 1;3 ]
    arrows : [ (1,3) ]
    sg [8] : nodes : [ 1;2 ]
    arrows : [  ]
    sg [9] : nodes : [ 1;2;3 ]
    arrows : [  ]
    sg [10] : nodes : [ 1;2;3 ]
    arrows : [ (3,2) ]
    sg [11] : nodes : [ 1;2;3 ]
    arrows : [ (1,3) ]
    sg [12] : nodes : [ 1;2;3 ]
    arrows : [ (1,3);(3,2) ]
    |}]
let unionOfSubGraphs g g' = 
  let nodes = NodeSet.union (nodes g) (nodes g') in
  let arrows = ArrowSet.union (arrows g) (arrows g') in
  let src = ArrowMap.union 
    (fun _ n1 n2 -> assert (Node.equal n1 n2); Some n1)
    (src g) (src g') in
  let dst = ArrowMap.union 
    (fun _ n1 n2 -> assert (Node.equal n1 n2); Some n1)
    (dst g) (dst g') in
  fromSetsMaps nodes arrows src dst

(* to do todo : debug *)
let intersectionOfSubGraphs g g' = 
  let nodes = NodeSet.inter (nodes g) (nodes g') in
  let arrows = ArrowSet.inter (arrows g) (arrows g') in
  let src = ArrowMap.filter 
    (fun ar _ -> ArrowSet.mem ar arrows)
    (src g) in
  let dst = ArrowMap.filter 
    (fun ar _ -> ArrowSet.mem ar arrows)
    (dst g) in
  fromSetsMaps nodes arrows src dst


  (* let generate_dot_representation g =
    let {nodes=nodes;arrows=arrows;src=_;dst=_;} = g in
    let node_to_dot n = Printf.sprintf "id:%d[label=\"id\"]" (n |> Node.id)  in
    let edge_to_dot e =
      Printf.sprintf "%d -> %d [label=\"(id:%d)\"]" (srcOf ~g e) (dstOf ~g e) (Arrow.id e)
    in
    let node_lines = List.map node_to_dot (nodes |> NodeSet.elements) in
    let edge_lines = List.map edge_to_dot (arrows |> ArrowSet.elements)  in
    let dot_lines = "digraph G {\n" :: (node_lines @ edge_lines) @ ["}\n"] in
     String.concat "\n" dot_lines
  let outputToDot dot_representation fn =
    let oc = Stdio.Out_channel.create fn in
    Out_channel.output_string 
    oc (Printf.sprintf "%s" dot_representation);
    Stdio.Out_channel.close oc
     *)

let arrowsFromTo g s t = 
  let ars = arrows g in
  ArrowSet.filter (fun a -> isArrowFromTo ~g ~a s t) ars
