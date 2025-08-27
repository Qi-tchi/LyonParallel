module Homo = GraphHomomorphism
type rulerGraph = {x : MGraph.t; fx : Homo.t option;name:string;description:string}
let aa_not_in_aca =   
  let x = MGraph.fromList [1;2;3] [(1,"a",3,1);(3,"a",2,2)] in
  let h_x_f = Homo.fromList 
    [1;2;3] [(1,"a",3,1);(3,"a",2,2)]
    [1;2;3] [(1,"a",3,1);(3,"c",3,3);(3,"a",2,2)]
    [(1,1);(2,2);(3,3)] [(1,1);(2,2)]  in
      let x = {x; 
      fx = Some h_x_f;
      name = "aa_not_in_aca";
      description="the graph X has two isolated nodes: 1 2\nthe forbidden context is the graph X with an additional edge : 1 -> 2"
      } in 
      x 
let nn_not_in_nen =
  let x = MGraph.fromList [1;2] [] in
  let f = Homo.fromList 
    [1;2] []
    [1;3] [(1,"edge",3,3);]
    [(1,1);(2,3)] [] in
    {x = x; fx = Some f;
    name = "the graph X has two isolated nodes: 1 2\nthe forbidden context is the graph X with an additional edge : 1 -> 2";
    description = "the graph X is a chain with two edges labeled 'a' : 1-a->3-a->2\n\nthe forbidden context is the graph X with an additional loop labeled 'c' : 3-c->3"
    } 

(* let ruler_graphs = [
  (nn_not_in_nen, "nn_not_in_nen","the graph X has two isolated nodes: 1 2\nthe forbidden context is the graph X with an additional edge : 1 -> 2");
  (aa_not_in_aca, "aa_not_in_aca","the graph X is a chain with two edges labeled 'a' : 1-a->3-a->2\n\nthe forbidden context is the graph X with an additional loop labeled 'c' : 3-c->3");
]
   *)
   let ruler_graphs = [
        nn_not_in_nen;
        aa_not_in_aca;
]
