module Homo = GraphHomomorphism
type rulerGraph = {x : MGraph.t; fx : Homo.t option}
let aa_not_in_aca =   
  let x = MGraph.fromList [1;2;3] [(1,"a",3,1);(3,"a",2,2)] in
  let h_x_f = Homo.fromList 
    [1;2;3] [(1,"a",3,1);(3,"a",2,2)]
    [1;2;3] [(1,"a",3,1);(3,"c",3,3);(3,"a",2,2)]
    [(1,1);(2,2);(3,3)] [(1,1);(2,2)]  in
      let x = {x; 
      fx = Some h_x_f } in 
      x 
let nn_not_in_nen =
  let x = MGraph.fromList [1;2] [] in
  let h_x_f = Homo.fromList 
    [1;2] []
    [1;3] [(1,"edge",3,3);]
    [(1,1);(2,3)] [] in
  let x = {x = x; fx = Some h_x_f } in 
    x 

let ruler_graphs = [
  (aa_not_in_aca, "aa_not_in_aca","the graph X is a chain with two edges labeled 'a' : 1-a->3-a->2\n\nthe forbidden context is the graph X with an additional loop labeled 'c' : 3-c->3");
  (nn_not_in_nen, "nn_not_in_nen","the graph X has two isolated nodes: 1 2\nthe forbidden context is the graph X with an additional edge : 1 -> 2");
]
