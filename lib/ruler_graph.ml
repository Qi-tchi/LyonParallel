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
  let x = MGraph.fromList [1;2] [(1,"node",1,1);(2,"node",2,2)] in
  let h_x_f = Homo.fromList 
    [1;2] [(1,"node",1,1);(2,"node",2,2)]
    [1;3] [(1,"node",1,1);(3,"node",3,2);(1,"edge",3,3);]
    [(1,1);(2,3)] [(1,1);(2,2)] in
  let x = {x = x; fx = Some h_x_f } in 
    x 
