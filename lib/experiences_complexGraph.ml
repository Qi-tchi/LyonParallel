(* module Homo=GraphHomomorphism
module Grs=GraphRewritingSystem
module Example=ConcretGraphRewritingSystems
module Termination=Termination

let solutionTimeApprox ~grs n =
  let times = List.init n (fun _ -> let ts = Unix.gettimeofday () in Termination.isTerminating grs |> ignore; Unix.gettimeofday () -. ts) in
  (List.fold_left (+.) 0. times) /. (Float.of_int n)
let nbStep (pb : Termination.problem) = List.length pb.witnesses

(* example 6 endrullis 2023  *)
  

(* endrullis ex 6.2 *)
let grs_6d2_terminating () = Termination.isTerminating Example.endrullis_2023_ex6_2
let grs_6d2_terminating_time k = solutionTimeApprox ~grs:Example.endrullis_2023_ex6_2 k  
(* 10000tests time= 0.001s *)


(* endrullis ex 6.3 *)
let grs_6_3_res () = Termination.isTerminating Example.endrullis_2023_ex6_3
let grs_6_3_res_time k = solutionTimeApprox ~grs:Example.endrullis_2023_ex6_3 k  (* 100 tests  time = 0.032 *)

(* endrullis ex 6.4 *)
(*!!!!!!!!!!!!!!!! SG  and non Mono a droite !!!!!!!!!!!!!!!!!!!!*)
(* let grs_6_4_res () = Termination.isTerminating Example.endrullis_2023_ex6_4
let grs_6_4_res_time () = solutionTimeApprox ~grs:Example.endrullis_2023_ex6_4 1000 *)

(* endrullis ex 6.8 *)
(* !!!!!!!!!!!!!!  failed !!!!!!!!!!!!!!!!!!!*)
let endrullis202368_res () = Termination.isTerminating Example.endrullis202368
let endrullis202368_res_time () = solutionTimeApprox ~grs:Example.endrullis202368 1000 

(* plump 2018 3 *)
(* *******   !!!!failed!!!! ********)
let plump20183_res () = Termination.isTerminating Example.plump20183
let plump20183_res_time () = solutionTimeApprox ~grs:Example.plump20183 1000 

(* plump 2018 fig 10 *)
(* *******   !!!!failed!!!! ********)
let plump2018fig10_res () = Termination.isTerminating Example.plump2018fig10
let plump2018fig10_res_time () = solutionTimeApprox ~grs:Example.plump2018fig10 100  

(* bruggink_2014_example_4 *)
let bruggink_2014_example_4_res () = Termination.isTerminating Example.bruggink_2014_example_4 ;;
let bruggink_2014_example_4_time k = solutionTimeApprox ~grs:Example.bruggink_2014_example_4 k;; 
(* 100 tests time = 0.160 *)



(* endrullis ex 6.9 *)
let grs_ex69_time () = solutionTimeApprox ~grs:Example.grs_ex69 1000;; 
(* 100 tests time = 0.487s *)

(* endrullis ex 6.9 variant *)
let grs_ex69_variant_time k = solutionTimeApprox ~grs:Example.grs_ex69 k;; 
(* 100 tests time 0.447s*)

(* bonfante_2023_main_example  *)
(*!!!!!!!!!!!  failed !!!!!!!!!*)
let bonfante_2023_main_example_res () = Termination.isTerminatingBool Example.bonfante_2023_main_example
let bonfante_2023_main_example_time k = solutionTimeApprox ~grs:Example.bonfante_2023_main_example k


 *)
