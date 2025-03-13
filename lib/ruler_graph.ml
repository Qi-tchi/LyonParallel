module Homo = GraphHomomorphism
type rulerGraph = {x : MGraph.t; fx : Homo.t option}
let aa_not_in_aca =   
  let h_x_f = Homo.fromList 
    [1;2;3] [(1,"a",3,1);(3,"a",2,2)]
    [1;2;3] [(1,"a",3,1);(3,"c",3,3);(3,"a",2,2)]
    [(1,1);(2,2);(3,3)] [(1,1);(2,2)]  in
      let x = {x = MGraph.fromList [1;2;3] [(1,"a",3,1);(3,"a",2,2)]; 
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
  (aa_not_in_aca, "aa_not_in_aca","the interface consists of two nodes : 1 and 2 with no edges\nthe left hand side is a chain with two edges labeled 'a' : 1-a->3-a->2\nthe right hand side is the left hand side graph with an additional loop labeled 'c' : 3-c->3");
  (nn_not_in_nen, "nn_not_in_nen","the interface is a singleton : 1\nthe left hand side consists only two nodes with no edge : 1 2\nthe right hand side graph consists of two nodes and a unique edge between them : 1 -> 3");
]
