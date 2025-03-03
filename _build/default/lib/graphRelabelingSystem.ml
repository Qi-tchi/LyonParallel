module Graph = MGraph
module Ugraph = UnlabelledDirectedMultGraph
module Homo = GraphHomomorphism
module Rule = struct
  type t = {
    lhs : Graph.t;
    rhs : Graph.t;
  }
  let fromLists ns es ns' es' = 
    let lhs = Graph.fromList ns es in
    let rhs = Graph.fromList ns' es' in
    {lhs;rhs}

  let getLabels rl = 
    let llabels = MGraph.labels rl.lhs in
    let rlabels = MGraph.labels rl.rhs in 
    llabels |> MGraph.LabelSet.union rlabels
end

type t = {
  rules : Rule.t list;
  labels : Graph.LabelSet.t;
  labels_init : Graph.LabelSet.t
}
let fromLists rules labels labels_init = 
  let labelsInRules = List.fold_right (fun rl acc -> MGraph.LabelSet.union (Rule.getLabels rl) acc) rules MGraph.LabelSet.empty in
  let labels = labels |> Graph.LabelSet.of_list in
  if MGraph.LabelSet.diff labelsInRules labels |> MGraph.LabelSet.is_empty |> not then raise (Invalid_argument "some labels are not declared");
  if MGraph.LabelSet.diff labels labelsInRules |> MGraph.LabelSet.is_empty |> not then raise (Invalid_argument "some labels are not used");
  let labels_init = labels_init |> Graph.LabelSet.of_list in
  if MGraph.LabelSet.diff labels_init labels |> MGraph.LabelSet.is_empty |> not then raise (Invalid_argument "some initial labels are not declared");
  {rules; labels_init; labels}



