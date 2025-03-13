module Homo = GraphHomomorphism
let mk_span_with_monos (f1,g1) =
  assert (Homo.isSpan f1 g1);
  assert (Homo.isInj f1);
  assert (Homo.isInj g1);
  (f1,g1)
let _ = mk_span_with_monos
(** [mk_cospan_with_monos left right] *)
let mk_span_with_monos (f2,g2) =
  assert (Homo.isCospan f2 g2);
  assert (Homo.isInj f2);
  assert (Homo.isInj g2);
  (f2,g2)
(** pb object will be a sub graph of [codom(g2)]*)
let pullback_cospan_monos (f2,g2) =
  assert (Homo.isInj f2 && Homo.isInj g2);
  let l, r = (Homo.imgOf f2), (Homo.imgOf g2) in
  let intersection = MGraph.intersectionOfSubGraphs l r in
  let f1s = Homo.homSet intersection l in
  let g1s = Homo.homSet intersection r in
  let f1f2s = Core.List.cartesian_product f1s g1s in
   match Core.List.find f1f2s ~f:(fun (f1,g1) -> Homo.isCommutative [f1;f2] [g1;g2]) with
  |None -> assert false
  |Some x -> x

(** A -f-> B -g-> C*)
let pushoutComplementOfInjHomosWithGraphs f g =
  let fg = Homo.composition f g in
  let a = Homo.imgOf fg in
  let b = Homo.imgOf g in
  let c = Homo.codom g in 
  Homo.existPushoutComplementOfInjHomos a b c


