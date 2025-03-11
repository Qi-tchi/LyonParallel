module Grs = GraphRewritingSystem
module Homo = GraphHomomorphism

type named_grs = { 
  grs : Grs.t list;
  name : string;
  monic_matching : bool;  
}

let named_grs_to_problem s = 
  Termination.pbFromList s.grs

let fromRulesListAndName ?(monic_matching=false) rls name  = 
  {grs=rls; name; monic_matching}
let fromRulesSetAndName ?(monic_matching=false) rls name = 
  {grs=rls; name; monic_matching}
(* type rule_material_t = {
  kvs:int list;
  kes:(int*int*string*int) list;
  lvs:int list;
  les:(int*int*string*int) list; 
  rvs:int list;
  res:(int*int*string*int) list; 
  lhv:(int*int) list;
  lhe:((int*int*string*int) *(int*int*string*int)) list;
  rhv:(int*int) list;
  rhe:((int*int*string*int) *(int*int*string*int)) list;
}  *) 
 
(*********************
  Endrullis_2024_ex_6.2
*****************************)

let r1l = 
  Homo.fromList   
  [1;2] [] 
  [1;2] [(1,"e",1,1)]
  [(1,1);(2,2)] []
let r1r = 
  Homo.fromList   
  [1;2] [] 
  [1;2] [(1,"e",2,1)]
  [(1,1);(2,2)] []
let r1 = Grs.fromHomos r1l r1r
let endrullis_2024_ex6_2 = fromRulesListAndName [r1] "endrullis_2024_ex6_2" ~monic_matching:true
 let endrullis_2024_ex6_2_problem = Termination.pbFromList [r1] 
(*********************
  Endrullis_2023_ex_6.3
*****************************)

let kvs = [1;2]
let kes = []

let lvs = [1;2;3]
let les = [( 1,"e",2,1);(2,"e",3,2);(3,"e",2,3)]

let lhv = [(1,1);(2,2)]
let lhe = []

let rvs = [1;2;4]
let res =  [(1,"e",2,1);(2,"e",4,2);(4,"e",1,3)]
let rhv = [(1,1);(2,2)]
let rhe = []

let endrullis_2023_ex6_3_rule1 = Grs.fromLists kvs kes lvs les rvs res lhv lhe rhv rhe
let endrullis_2024_ex6_3 = fromRulesListAndName [endrullis_2023_ex6_3_rule1] "endrullis_2024_ex6_3" ~monic_matching:true
let endrullis_2023_ex6_3 =Termination.pbFromList [endrullis_2023_ex6_3_rule1]

  
 (*********************
  Endrullis_2023_ex_6.4   SIMPLE GRAPH NOT SUPPORTED
*****************************)
(* let kvs = [1;2]
let kes = []

let lvs = [1;2]
let les = [(1,"",2,1)]

let lhv = [(1,1);(2,2)]
let lhe = []

let rvs = [1;2;3;4]
let res =  [(1,"",1,1)]

let rhv = [(1,1);(2,2)]
let rhe = []

let endrullis_2023_ex6_4_rule1 = Grs.fromLists kvs kes lvs les rvs res lhv lhe rhv rhe
let endrullis_2023_ex6_4 =Termination.pbFromList [endrullis_2023_ex6_4_rule1] 
(* let endrullis_2024_ex6_4 = fromRulesListAndName [endrullis_2023_ex6_4_rule1] "endrullis_2024_ex6_4_not_supported" ~monic_matching:true *)
  *)

(*********************
  endrullis_2024_exd3
*****************************)
let r1l = 
  Homo.fromList   
  [1] [] 
  [1;2] [(1,"node",1,1);(2,"node",2,2)]
  [(1,1)] []
let r1r = 
  Homo.fromList   
  [1] [] 
  [1;2] [(1,"e",2,3);(1,"node",1,1);(2,"node",2,2)]
  [(1,1)] []
let r1 = Grs.fromHomos r1l r1r

let endrullis_2024_exd3_problem =Termination.pbFromList [r1] 
let endrullis_2024_exd3 = fromRulesListAndName [r1] "endrullis_2024_exd3" ~monic_matching:false


(*********************
  overbeek_2024_ex5d3
*****************************)
let r1l = 
  Homo.fromList   
  [1] [] 
  [1;2] [(1,"e",1,1)]
  [(1,1)] []
let r1r = 
  Homo.fromList   
  [1] [] 
  [1;2] []
  [(1,1)] []
let r1 = Grs.fromHomos r1l r1r

let r2l = 
  Homo.fromList   
  [1;2] [] 
  [1;2] [(1,"e",2,1)]
  [(1,1);(2,2)] []
let r2r = 
  Homo.fromList   
  [1;2] [] 
  [1;2;3] []
  [(1,1);(2,2)] []
let r2 = Grs.fromHomos r2l r2r

let overbeek_2024_ex5d3 = fromRulesListAndName [r1;r2] "overbeek_2024_ex5d3" ~monic_matching:true 


(*********************
  overbeek_2024_ex5d5
  *****************************)

let kvs = [1;2]
let kes = [(1,"e",2,1)]

let lvs = [1;2;3]
let les = [( 1,"e",2,1);(2,"e",3,2);(3,"e",2,3)]

let lhv = [(1,1);(2,2)]
let lhe = [(1,1)]

let rvs = [1;2;4]
let res =  [(1,"e",2,1);(2,"e",4,2);(4,"e",1,3)]
let rhv = [(1,1);(2,2)]
let rhe = [(1,1)]

let overbeek_2024_ex5d5_rule = Grs.fromLists kvs kes lvs les rvs res lhv lhe rhv rhe
let overbeek_2024_ex5d5 = fromRulesListAndName [overbeek_2024_ex5d5_rule] "overbeek_2024_ex5d5" ~monic_matching:true
(* 

(*********************
  overbeek_2024_ex5d5
  *****************************)

let kvs = [1;2]
let kes = [(1,"e",2,1)]

let lvs = [1;2;3]
let les = [( 1,"e",2,1);(2,"e",3,2);(3,"e",2,3)]

let lhv = [(1,1);(2,2)]
let lhe = [(1,1)]

let rvs = [1;2;4]
let res =  [(1,"e",2,1);(2,"e",4,2);(4,"e",1,3)]
let rhv = [(1,1);(2,2)]
let rhe = [(1,1)]

let overbeek_2024_ex5d5_rule = Grs.fromLists kvs kes lvs les rvs res lhv lhe rhv rhe
let overbeek_2024_ex5d5 = fromRulesListAndName [overbeek_2024_ex5d5_rule] "overbeek_2024_ex5d5" ~monic_matching:true *)




(*********************
  overbeek_2024_ex5d6
*****************************)


let r1l = 
  Homo.fromList   
  [] [] 
  [1;2] [(1,"a",1,1);(2,"a",2,2)]
  [] [] 
let r1r = 
  Homo.fromList   
  [] [] 
  [2;3;1] [(1,"b",1,1);(2,"b",2,2);(3,"b",3,3)]
  [] [] 
let r1 = Grs.fromHomos r1l r1r


let r2l = 
  Homo.fromList   
  [] [] 
  [2;3;1] [(1,"b",1,1);(2,"b",2,2);]
  [] [] 
let r2r = 
  Homo.fromList   
  [] [] 
  [1] [(1,"a",1,1)]
  [] [] 
let r2 = Grs.fromHomos r2l r2r

let overbeek_2024_ex5d6 =  fromRulesListAndName [
  r1;
  r2
  ] "overbeek_2024_ex5d6"


(*********************
  plump_2018_ex_3        plump_1995_ex3.8
*****************************)


let r1l = 
  Homo.fromList   
  [1;2] [] 
  [2;3;1] [(1,"a",3,1);(3,"b",2,2)]
  [(1,1);(2,2)] []
let r1r = 
  Homo.fromList   
  [1;2] [] 
  [2;3;1] [(1,"a",3,1);(3,"c",2,2)]
  [(1,1);(2,2)] []
let r1 = Grs.fromHomos r1l r1r


let r2l = 
  Homo.fromList   
  [1;2] [] 
  [2;3;1] [(1,"c",3,1);(3,"d",2,2)]
  [(1,1);(2,2)] []
let r2r = 
  Homo.fromList   
  [1;2] [] 
  [2;3;1] [(1,"d",3,1);(3,"b",2,2)]
  [(1,1);(2,2)] []
let r2 = Grs.fromHomos r2l r2r

let plump20183r2 = Grs.fromLists kvs kes lvs les rvs res lhv lhe rhv rhe
(* let plump20183 =Termination.pbFromList [r1; r2] *)
let plump_1995_ex3_8 =  fromRulesListAndName [
  r1;
  r2
  ] "plump_1995_ex3_8"

let plump_2018_ex3 =  fromRulesListAndName [
  r1;
  r2
  ] "plump_2018_ex3"
let endrullis_2024_exd1 =  fromRulesListAndName [
  r1;
  r2
  ] "endrullis_2024_exd1"

let overbeek_2024_ex5d8 =  fromRulesListAndName [
  r1;
  r2
  ] "overbeek_2024_ex5d8"
  
(*********************
  plump_1995_ex4_1     
*****************************)


let r1l = 
  Homo.fromList   
  [1;2;3;4] [(2,"a",2,4);(3,"b",3,5)] 
  [1;2;3;4] [(1,"f",2,1);(1,"f",3,2);(1,"f",4,3);(2,"a",2,4);(3,"b",3,5)]
  [(1,1);(2,2);(3,3);(4,4)] [(4,4);(5,5)]
let r1r = 
  Homo.fromList   
  [1;2;3;4] [(2,"a",2,4);(3,"b",3,5)] 
  [1;2;3;4] [(1,"f",4,1);(1,"f",4,2);(1,"f",4,3);(2,"a",2,4);(3,"b",3,5)]
  [(1,1);(2,2);(3,3);(4,4)] [(4,4);(5,5)]
let r1 = Grs.fromHomos r1l r1r


let r2l = 
  Homo.fromList   
  [1] [] 
  [1] [(1,"b",1,1)]
  [(1,1)] []
let r2r = 
  Homo.fromList   
  [1] [] 
  [1] [(1,"a",1,1)]
  [(1,1)] []
let r2 = Grs.fromHomos r2l r2r

let plump_1995_ex4_1 =  fromRulesListAndName [
  r1;
  r2
  ] "plump_1995_ex4_1"
  ~monic_matching:true

let plump_1995_ex4_1_problem = Termination.pbFromList [
  r1;
  r2
  ]
  
(*********************
  plump_2018_fig10
*****************************)

let lp1 =
  Homo.fromList   
  [1;2] [] 
  [1;2] [(1,"r",1,1);(1,"edge",2,2);(2,"white",2,3)]
  [(1,1);(2,2)] []
let rp1 = 
  Homo.fromList   
  [1;2] [] 
  [1;2] [(1,"r",1,1);(1,"edge",2,2);(2,"b",2,3)]
  [(1,1);(2,2)] []
let r1 = Grs.fromHomos lp1 rp1

let lp2 =
  Homo.fromList   
  [1;2] [] 
  [1;2] [(1,"white",1,1);(1,"edge",2,2);(2,"r",2,3)]
  [(1,1);(2,2)] []
let rp2 = 
  Homo.fromList   
  [1;2] [] 
  [1;2] [(1,"b",1,1);(1,"edge",2,2);(2,"r",2,3)]
  [(1,1);(2,2)] []
let r2 = Grs.fromHomos lp2 rp2

let lp3 =
  Homo.fromList   
  [1;2] [] 
  [1;2] [(1,"b",1,1);(1,"edge",2,2);(2,"white",2,3)]
  [(1,1);(2,2)] []
let rp3 = 
  Homo.fromList   
  [1;2] [] 
  [1;2] [(1,"b",1,1);(1,"edge",2,2);(2,"r",2,3)]
  [(1,1);(2,2)] []
let r3 = Grs.fromHomos lp3 rp3

let lp4 =
  Homo.fromList   
  [1;2] [] 
  [1;2] [(1,"white",1,1);(1,"edge",2,2);(2,"b",2,3)]
  [(1,1);(2,2)] []
let rp4 = 
  Homo.fromList   
  [1;2] [] 
  [1;2] [(1,"r",1,1);(1,"edge",2,2);(2,"b",2,3)]
  [(1,1);(2,2)] []
let r4 = Grs.fromHomos lp4 rp4

let lp5 =
  Homo.fromList   
  [1;2] [] 
  [1;2] [(1,"r",1,1);(1,"edge",2,2);(2,"r",2,3)]
  [(1,1);(2,2)] []
let rp5 = 
  Homo.fromList   
  [1;2] [] 
  [1;2] [(1,"black",1,1);(1,"edge",2,2);(2,"black",2,3)]
  [(1,1);(2,2)] []
let r5 = Grs.fromHomos lp5 rp5


let lp6 =
  Homo.fromList   
  [1;2] [] 
  [1;2] [(1,"b",1,1);(1,"edge",2,2);(2,"b",2,3)]
  [(1,1);(2,2)] []
let rp6 = 
  Homo.fromList   
  [1;2] [] 
  [1;2] [(1,"black",1,1);(1,"edge",2,2);(2,"black",2,3)]
  [(1,1);(2,2)] []
let r6 = Grs.fromHomos lp6 rp6

let lp7 =
  Homo.fromList   
  [1;2] [] 
  [1;2] [(1,"black",1,1);(2,"r",2,3)]
  [(1,1);(2,2)] []
let rp7 = 
  Homo.fromList   
  [1;2] [] 
  [1;2] [(1,"black",1,1);(2,"black",2,3)]
  [(1,1);(2,2)] []
let r7 = Grs.fromHomos lp7 rp7

let lp8 =
  Homo.fromList   
  [1;2] [] 
  [1;2] [(1,"black",1,1);(2,"b",2,3)]
  [(1,1);(2,2)] []
let rp8 = 
  Homo.fromList   
  [1;2] [] 
  [1;2] [(1,"black",1,1);(2,"black",2,3)]
  [(1,1);(2,2)] []
let r8 = Grs.fromHomos lp8 rp8

let lp9 =
  Homo.fromList   
  [1;2] [] 
  [1;2] [(1,"black",1,1);(2,"white",2,3)]
  [(1,1);(2,2)] []
let rp9 = 
  Homo.fromList   
  [1;2] [] 
  [1;2] [(1,"black",1,1);(2,"black",2,3)]
  [(1,1);(2,2)] []
let r9 = Grs.fromHomos lp9 rp9

let plump_2018_fig10_problem =Termination.pbFromList [r1;r2;r3;r4;r5;r6;r7;r8;r9 ] 
let plump_2018_fig10 = fromRulesListAndName [r1;r2;r3;r4;r5;r6;r7;r8;r9 ] "plump_2018_fig10"
let plump_2018_ex5 = fromRulesListAndName [r1;r2;r3;r4;r5;r6;r7;r8;r9 ] "plump_2018_ex5"
(*********************
  bruggink_2015_ex4
*****************************)

let lp1 =
  Homo.fromList   
  [1;2] [] 
  [2;3;1] [(2,"count",3,1);(3,"incr",3,2);(3,"0",1,3)]
  [(1,1);(2,2)] []
  
let rp1 = 
  Homo.fromList   
  [1;2] [] 
  [2;3;1] [(2,"count",3,1);(3,"1",1,2)]
  [(1,1);(2,2)] []

let lp2 = 
  Homo.fromList   
  [1;2] [] 
  [1;2;3] [(2,"count",1,1);(3,"incr",3,2);(3,"1",1,3)]
  [(1,1);(2,2)] []
  
let rp2 = 
  Homo.fromList   
  [1;2] [] 
  [2;3;1] [(2,"count",3,1);(3,"c",1,2)]
  [(1,1);(2,2)] []
  

let lp3 = 
  Homo.fromList   
  [1;2] [] 
  [2;3;1] [(2,"c",3,1);(3,"0",1,2)]
  [(1,1);(2,2)] []
  
let rp3 =
  Homo.fromList   
  [1;2] [] 
  [2;3;1] [(2,"0",3,1);(3,"1",1,2)]
  [(1,1);(2,2)] [] 

let lp4 = 
  Homo.fromList   
  [1;2] [] 
  [2;3;1] [(2,"c",3,1);(3,"1",1,2)]
  [(1,1);(2,2)] []
let rp4 = 
  Homo.fromList   
  [1;2] [] 
  [2;3;1] [(2,"0",3,1);(3,"c",1,2)]
  [(1,1);(2,2)] []
  
let r1 = Grs.fromHomos lp1 rp1
let r2 = Grs.fromHomos lp2 rp2
let r3 = Grs.fromHomos lp3 rp3
let r4 = Grs.fromHomos lp4 rp4
let bruggink_2015_ex4_problem = Termination.pbFromList [r1;r2;r3;r4]
let bruggink_2015_ex4 = fromRulesListAndName [r1;r2;r3;r4]"bruggink_2015_ex4"
let bruggink_2015_ex4_rules_2_3_4 =  fromRulesListAndName  [r2;r3;r4] "bruggink_2015_ex4_r234"
let bruggink_2015_ex4_r34 =  fromRulesListAndName  [r3;r4]  "bruggink_2015_ex4_r34"



(*********************
  bruggink_2015_ex5
*****************************)

let lp1 =
  Homo.fromList   
  [1;2] [] 
  [2;3;1] [(2,"count",3,1);(3,"0",1,3)]
  [(1,1);(2,2)] []
  
let rp1 = 
  Homo.fromList   
  [1;2] [] 
  [2;3;1] [(2,"count",3,1);(3,"1",1,2)]
  [(1,1);(2,2)] []
let lp2 = 
  Homo.fromList   
  [1;2] [] 
  [1;2;3] [(2,"count",3,1);(3,"1",1,3)]
  [(1,1);(2,2)] []
  
let rp2 = 
  Homo.fromList   
  [1;2] [] 
  [2;3;1] [(2,"count",3,1);(3,"c",1,2)]
  [(1,1);(2,2)] []
  

let lp3 = 
  Homo.fromList   
  [1;2] [] 
  [2;3;1] [(2,"c",3,1);(3,"0",1,2)]
  [(1,1);(2,2)] []
  
let rp3 =
  Homo.fromList   
  [1;2] [] 
  [2;3;1] [(2,"0",3,1);(3,"1",1,2)]
  [(1,1);(2,2)] [] 

let lp4 = 
  Homo.fromList   
  [1;2] [] 
  [2;3;1] [(2,"c",3,1);(3,"1",1,2)]
  [(1,1);(2,2)] []
let rp4 = 
  Homo.fromList   
  [1;2] [] 
  [2;3;1] [(2,"0",3,1);(3,"c",1,2)]
  [(1,1);(2,2)] []
  
let r1 = Grs.fromHomos lp1 rp1
let r2 = Grs.fromHomos lp2 rp2
let r3 = Grs.fromHomos lp3 rp3
let r4 = Grs.fromHomos lp4 rp4
let bruggink_2015_ex5_problem = Termination.pbFromList [r1;r2;r3;r4]  
let bruggink_2015_ex5 =  fromRulesListAndName  [r1;r2;r3;r4]  "bruggink_2015_ex5"
let bruggink_2015_ex5_rules_3_4 =  fromRulesListAndName  [r3;r4] "bruggink_2015_ex5_r34"


(*********************
  bruggink_2015_ex6
*****************************)
 

let lp1 =
  Homo.fromList   
  [1] [] 
  [2;1] [(2,"0",1,1)]
  [(1,1)] []
  
let rp1 = 
  Homo.fromList   
  [1] [] 
  [2;1] [(2,"1",1,1)]
  [(1,1)] []

let lp2 =
  Homo.fromList   
  [1] [] 
  [2;1] [(2,"1",1,1)]
  [(1,1)] []
  
let rp2 = 
  Homo.fromList   
  [1] [] 
  [2;1] [(2,"c",1,1)]
  [(1,1)] []
  
let lp3 = 
  Homo.fromList   
  [1;2;3] [] 
  [2;3;1;4] [(4,"0",2,1);
             (4,"0",1,2);(3,"c",4,3);]
  [(1,1);(2,2);(3,3)] []
  
let rp3 =
  Homo.fromList   
  [1;2;3] []
  [2;3;1;4] [(4,"0",2,1);
             (4,"1",1,2);(3,"0",4,3);]
  [(1,1);(2,2);(3,3)] [] 

let lp4 = 
  Homo.fromList   
  [1;2;3] [] 
  [2;3;1;4] [(4,"1",2,1);
             (4,"0",1,2);(3,"c",4,3);]
  [(1,1);(2,2);(3,3)] []
  
let rp4 =
  Homo.fromList   
  [1;2;3] []
  [2;3;1;4] [(4,"1",2,1);
             (4,"1",1,2);(3,"0",4,3);]
  [(1,1);(2,2);(3,3)] [] 

let lp5 = 
  Homo.fromList   
  [1;2;3] [] 
  [2;3;1;4] [(4,"0",2,1);
             (4,"1",1,2);(3,"c",4,3);]
  [(1,1);(2,2);(3,3)] []
  
let rp5 =
  Homo.fromList   
  [1;2;3] []
  [2;3;1;4] [(4,"0",2,1);
             (4,"c",1,2);(3,"0",4,3);]
  [(1,1);(2,2);(3,3)] [] 

let lp6 = 
  Homo.fromList   
  [1;2;3] [] 
  [2;3;1;4] [(4,"1",2,1);
             (4,"1",1,2);(3,"c",4,3);]
  [(1,1);(2,2);(3,3)] []
  
let rp6 =
  Homo.fromList   
  [1;2;3] [] 
  [2;3;1;4] [(4,"1",2,1);
             (4,"c",1,2);(3,"0",4,3);]
  [(1,1);(2,2);(3,3)] [] 
  
let r1 = Grs.fromHomos lp1 rp1
let r2 = Grs.fromHomos lp2 rp2
let r3 = Grs.fromHomos lp3 rp3
let r4 = Grs.fromHomos lp4 rp4
let r5 = Grs.fromHomos lp5 rp5
let r6 = Grs.fromHomos lp6 rp6
let bruggink_2015_ex6_problem = Termination.pbFromList [r1;r2;r3;r4;r5;r6] 
let bruggink_2015_ex6 =  fromRulesListAndName  [r1;r2;r3;r4;r5;r6] "bruggink_2015_ex6"
let endrullis_2024_exd2 =  fromRulesListAndName  [r1;r2;r3;r4;r5;r6] "endrullis_2024_exd2"
let bruggink_2015_ex6_rules_2_3_4_5_6 =  fromRulesListAndName  [r2;r3;r4;r5;r6] "bruggink_2015_ex6_r23456"

let lp0 =
  Homo.fromList   
  [1] [] 
  [2;1] [(2,"0",1,1)]
  [(1,1)] []
  
let rp0 = 
  Homo.fromList   
  [1] [] 
  [2;1;3] [(2,"c",1,1);(3,"1",1,2)]
  [(1,1)] [] 

let r0 = Grs.fromHomos lp0 rp0

let bruggink_2015_ex6_modified =   fromRulesListAndName  [r0;r1;r2;r3;r4;r5;r6] "bruggink_2015_ex6_modified"

(*********************
  bruggink_2014_ex_1
*****************************)
let l1 = Homo.fromList
  [1;2] [] 
  [1;2;3] [(1,"a",3,1);(3,"a",2,2)]
  [(1,1);(2,2)] []
let r1 =  Homo.fromList
  [1;2] [] 
  [1;2;3] [(1,"a",3,1);(3,"c",3,3);(3,"a",2,2)]
  [(1,1);(2,2)] []
let bruggink_2014_ex1_rl = Grs.fromHomos l1 r1

let bruggink_2014_ex1 =  fromRulesListAndName [bruggink_2014_ex1_rl]"bruggink_2014_ex1"

(*********************
  bruggink_2014_ex_4
*****************************)
let bruggink_2014_ex_4_l = Homo.fromList
  [1;2] [] 
  [1;2;3] [(1,"a",3,1);(3,"a",2,2)]
  [(1,1);(2,2)] []
let bruggink_2014_ex_4_r = Homo.fromList
  [1;2] []
  [1;2;3;4] [(1,"a",3,1);(3,"b",4,2);(4,"a",2,3);]
  [(1,1);(2,2)] []
let bruggink_2014_ex_4 = Grs.fromHomos bruggink_2014_ex_4_l bruggink_2014_ex_4_r
let bruggink_2014_ex_4_rl_1 = Grs.fromHomos bruggink_2014_ex_4_l bruggink_2014_ex_4_r
let bruggink_2014_ex6 =  fromRulesListAndName [bruggink_2014_ex_4] "bruggink_2014_ex_4_and_6"
let bruggink_2015_ex2 =  fromRulesListAndName [bruggink_2014_ex_4] "bruggink_2015_ex2"
let bruggink_2014_ex4_problem = Termination.pbFromList [bruggink_2014_ex_4]
(*********************
  bruggink_2014_ex_5
*****************************)
let l1 =  Homo.fromList 
  [1;2] []  
  [1;3;2] [(1,"0",3,1);(3,"L",2,2);
          (* (1,"n",1,4);(2,"n",2,8);(3,"n",3,5); *)
        ]
  [(1,1);(2,2)] 
  []
let r1 =    
  Homo.fromList 
  [1;2] []  
  [1;2;3;4] [(1,"L",3,1);(3,"1",4,2);(4,"1",2,3)
          (* ;(1,"n",1,4);(2,"n",2,8);(3,"n",3,5); (4,"n",4,6) *)
          ]
  [(1,1);(2,2)] 
  []
let l2 =  Homo.fromList
  [1;2] []  
  [1;3;2]  [(1,"R",3,1);(3,"1",2,2)
        (* ;(1,"n",1,4);(2,"n",2,8);(3,"n",3,5); *)
        ]
  [(1,1);(2,2)] 
  []
let r2 =  Homo.fromList
  [1;2] []  
  [1;3;2] [(1,"0",3,1);(3,"R",2,2)
    (* ;(1,"n",1,4);(2,"n",2,8);(3,"n",3,5); *)
  ]
  [(1,1);(2,2)] 
  []
let l3 =   Homo.fromList
  [1;2] []  
  [1;3;2] [(1,"B",3,1);(3,"L",2,2)
      (* ;(1,"n",1,4);(2,"n",2,8);(3,"n",3,5); *)
      ]
  [(1,1);(2,2)] 
  []
let r3 =  Homo.fromList
  [1;2] []  
  [1;2] [(1,"R",2,1);
  (* (1,"n",1,4);(2,"n",2,8); *)
  ]
  [(1,1);(2,2)] 
  []
let l4 =  Homo.fromList
  [1;2] []  
  [1;3;2] [(1,"R",3,1);(3,"B",2,2);
  (* (1,"n",1,4);(2,"n",2,8);(3,"n",3,5); *)
  ]
  [(1,1);(2,2)] 
  []
let r4 =  Homo.fromList
  [1;2] []  
  [1;3;2] [(1,"L",3,1);(3,"B",2,2)
  (* ; (1,"n",1,4);(2,"n",2,8);(3,"n",3,5); *)
  ]
  [(1,1);(2,2)] 
  []

let bruggink_2014_ex_5_rl1 = Grs.fromHomos l1 r1
let bruggink_2014_ex_5_rl2 = Grs.fromHomos l2 r2
let bruggink_2014_ex_5_rl3 = Grs.fromHomos l3 r3
let bruggink_2014_ex_5_rl4 = Grs.fromHomos l4 r4
(* let bruggink_2014_ex_5 = 
  [
    bruggink_2014_ex_5_rl1;
    bruggink_2014_ex_5_rl2;
    bruggink_2014_ex_5_rl3;
    bruggink_2014_ex_5_rl4
    ] *)
let bruggink_2014_ex5_problem = Termination.pbFromList [  bruggink_2014_ex_5_rl1;
bruggink_2014_ex_5_rl2;
bruggink_2014_ex_5_rl3;
bruggink_2014_ex_5_rl4
];;
let bruggink_2014_ex5 = fromRulesListAndName [
  bruggink_2014_ex_5_rl1;
  bruggink_2014_ex_5_rl2;
  bruggink_2014_ex_5_rl3;
  bruggink_2014_ex_5_rl4
  ]
   "bruggink_2014_ex5"
let bruggink_2014_ex5_rule_1_and_2_only = fromRulesListAndName [
    bruggink_2014_ex_5_rl1;
    bruggink_2014_ex_5_rl2;
    ]
   "bruggink_2014_ex5_r12"
  
let plump_2018_ex4 =  fromRulesListAndName [
  bruggink_2014_ex_5_rl1;
  bruggink_2014_ex_5_rl2;
  bruggink_2014_ex_5_rl3;
  bruggink_2014_ex_5_rl4
  ]
   "plump_2018_ex4"
(*********************
  bruggink_2014_ex_6 ??? quelle est la diff avec ex 4
*****************************)


(*********************
exemple  : ad-hoc routing protocol
*****************************)
(* let sml = 
  [(1,"M",1); (1,"C",2);(2,"U",2)]@[(1,"node",1);(2,"node",2)];;
let smr = [(1,"C",2);(2,"M",2)]@[(1,"node",1);(2,"node",2)];;
let arl = [(1,"S",1); (1,"C",2);(2,"S",2)]@[(1,"node",1);(2,"node",2)];;
let arr = [(1,"S",1);(1,"C",3);(3,"R",3);(3,"U",3);(3,"C",2);(2,"S",2)]
          @[(1,"node",1);(2,"node",2);(3,"node",3)];;
let cil = [(2,"S",2);(2,"U",2)]@[(1,"node",1);(2,"node",2)];;
let cir = [(1,"C",2);(2,"S",2);(2,"U",2)]@[(1,"node",1);(2,"node",2)];; *)
let sml = Homo.fromList
  [1;2] []  
  [1;2] [(1,"M",1,1); (1,"C",2,2);(2,"U",2,3)]
  [(1,1);(2,2)] 
  []
let smr = Homo.fromList
  [1;2] []  
  [1;2] [(1,"C",2,2);(2,"M",2,3)]
  [(1,1);(2,2)] 
  []
let arl = Homo.fromList
  [1;2] []  
  [1;2] [(1,"S",1,1); (1,"C",2,2);(2,"S",2,3)]
  [(1,1);(2,2)] 
  []
let arr = Homo.fromList
  [1;2] []  
  [1;3;2] [(1,"S",1,1);(1,"C",3,2);(3,"R",3,3);(3,"U",3,4);(3,"C",2,5);(2,"S",2,6)]
  [(1,1);(2,2)] 
  []
let cil = Homo.fromList
  [1] []  
  [1;2] [(2,"S",2,1);(2,"U",2,2)]
  [(1,1)] 
  []
let cir = Homo.fromList
  [1] []  
  [1;2] [(1,"C",2,1);(2,"S",2,2);(2,"U",2,3)]
  [(1,1)] 
  []

let sm = Grs.fromHomos sml smr
let ar = Grs.fromHomos arl arr
let ci = Grs.fromHomos cil cir
let bruggink_2014_ad_hoc_routing_protocol_problem = Termination.pbFromList  [sm;ar;ci]
let bruggink_2014_ad_hoc_routing_protocol = fromRulesListAndName [sm;ar;ci] "bruggink_2014_ad_hoc_routing_protocol"
let bruggink_2014_ad_hoc_routing_protocol_rules_sm_ar_only = fromRulesListAndName [sm;ar] "bruggink_2014_ad_hoc_routing_protocol_rules_ar_ci_only"

(*********************
exemple  : bonfante_2023_main_ex_follow
*****************************)
let kvs = [1;2;3]
let kes = []

let lvs = [1;2;3]
let les = [(1,"T",2,1);(2,"a",3,2)]

let lhv = [(1,1);(2,2);(3,3)]
let lhe = []

let rvs = [1;2;3]
let res = [(1,"T",3,1);(2,"a",3,2)]

let rhv = [(1,1);(2,2);(3,3)]
let rhe = []

let bonfante_2023_main_ex_follow = Grs.fromLists kvs kes lvs les rvs res lhv lhe rhv rhe
let bonfante_2023_main_ex =Termination.pbFromList [bonfante_2023_main_ex_follow]  

(* endrullis ex 6.9 *)
let r1_r = Homo.fromList 
  [1;2;3] [(1,"s",3,1);(3,"0",3,2)]
  [1;2;3;4] [(1,"s",3,1);(3,"0",3,2); (2,"s",4,3); (4,"0",4,4)]
  [(1,1);(2,2);(3,3)] 
  [(1,1); (2,2)]
 
let r1_l = Homo.fromList 
  [1;2;3] [(1,"s",3,1);(3,"0",3,2)]
  [1;2;3] [(1,"s",3,1);(3,"0",3,2); (2,"s",3,3)]
  [(1,1);(2,2);(3,3)] 
  [(1,1); (2,2)]

let plump_2018_ex6_r1 = Grs.fromHomos r1_l r1_r
let plump_2018_ex6_problem = Termination.pbFromList [plump_2018_ex6_r1]
let plump_2018_ex6 = fromRulesListAndName [plump_2018_ex6_r1] "plump_2018_ex6"

(* endrullis ex 6.9 variant *)

let r1_l = Homo.fromList 
  [1;2;3] []
  [1;2;3] [(1,"s",3,1);(3,"0",3,2); (2,"s",3,3)]
  [(1,1);(2,2);(3,3)] 
  []
let r1_r = Homo.fromList 
  [1;2;3] []
  [1;2;3;4] [(1,"s",3,1);(3,"0",3,2); (2,"s",4,3); (4,"0",4,4)]
  [(1,1);(2,2);(3,3)] 
  [] 

let plump_2018_ex6_variant_r1 = Grs.fromHomos r1_l r1_r
(* let plump_2018_ex6_variant_problem = Termination.pbFromList [plump_2018_ex6_variant_r1] *)
let plump_2018_ex6_variant = fromRulesListAndName [plump_2018_ex6_variant_r1] "plump_2018_ex6_discret_interface"
let plump_2018_ex6_variant_monic = fromRulesListAndName ~monic_matching:true [plump_2018_ex6_variant_r1] "plump_2018_ex6_variant_monic"


(* Example 45 *)

let r1_l = Homo.fromList 
  [1;2;3] []
  [1;2;3] [(1,"s",3,1);(3,"0",3,2); (2,"s",3,3)]
  [(1,1);(2,2);(3,3)] 
  []
let r1_r = Homo.fromList 
  [1;2;3] []
  [1;2;3;4;5] 
  [(1,"s",3,1);(3,"0",3,2); (2,"s",4,3); (4,"0",4,4);
  (5,"0",5,5);(5,"0",5,6);(5,"0",5,7);]
  [(1,1);(2,2);(3,3)] 
  [] 
let my_rule = Grs.fromHomos r1_l r1_r
let my_ex45 = fromRulesListAndName ~monic_matching:true [my_rule] "my_ex45"


(**************)
  
let r1l = Homo.fromList 
[1;2] []
[1;2] [(1,"A",1,1);(1,"0",2,2);(2,"X",2,3)] 
[(1,1);(2,2)] []
let r1r = Homo.fromList 
[1;2] []
[1;2] [(1,"A",1,1);(1,"1",2,2);(2,"a",2,3)]
[(1,1);(2,2)] []
let _r1 = Grs.fromHomos r1l r1r
let r2l = Homo.fromList 
  [1;2] []
  [1;2] [(1,"a",1,1);(1,"0",2,2);(2,"X",2,3)] 
  [(1,1);(2,2)] []
let r2r = Homo.fromList 
  [1;2] []
  [1;2] [(1,"a",1,1);(1,"1",2,2);(2,"a",2,3)]
  [(1,1);(2,2)] []
let _r2 = Grs.fromHomos r2l r2r
let r5l = Homo.fromList 
  [1;2] []
  [1;2] [(1,"a",1,1);(1,"1",2,2);(2,"axi",2,3)] 
  [(1,1);(2,2)] []
let r5r = Homo.fromList 
  [1;2] []
  [1;2] [(1,"axi",1,1);(1,"1",2,2);(2,"axi",2,3)]
  [(1,1);(2,2)] []
let r5 = Grs.fromHomos r5l r5r
let r7l = Homo.fromList 
  [1;2] []
  [1;2] [(1,"ax",1,1);(1,"1",2,2);(2,"axi",2,3)] 
  [(1,1);(2,2)] []
let r7r = Homo.fromList 
  [1;2] []
  [1;2] [(1,"ax",1,1);(1,"1",2,2);(2,"ax",2,3)]
  [(1,1);(2,2)] []
let r7 = Grs.fromHomos r7l r7r
let r8l = Homo.fromList 
  [1;2] []
  [1;2;3] [(1,"ax",1,1);(1,"1",3,2);(3,"ax",3,3);(3,"1",2,4);(2,"BB",2,5)] 
  [(1,1);(2,2)] []
let r8r = Homo.fromList 
  [1;2] []
  [1;2;3] 
  [(1,"ax",1,1);(1,"1",3,2);(3,"BB",3,3);(3,"0",2,4);(2,"X",2,5)]
  [(1,1);(2,2)] []
let r8 = Grs.fromHomos r8l r8r

let metivier_1995_majAB_rules_2_5_7_8_only_bis_monic = fromRulesListAndName [
    (* _r1; *)
    _r2;
    r5;
    r7;
    r8
    ] "metivier_1995_majAB_rules_2_5_7_8_only_bis_monic" ~monic_matching:true

let metivier_1995_majAB_rules_2_5_7_8_only_bis = fromRulesListAndName [
    (* _r1; *)
    _r2;
    r5;
    r7;
    r8
    ] "metivier_1995_majAB_rules_2_5_7_8_only_bis"

let r1l = Homo.fromList 
[1;2] []
[1;2;3] [(1,"A",1,1);(3,"0",3,2);(2,"X",2,3);(1,"e",3,4);(2,"e",3,5);] 
[(1,1);(2,2)] []
let r1r = Homo.fromList 
[1;2] []
[1;2;3] [(1,"A",1,1);(3,"1",3,2);(2,"a",2,3);(1,"e",3,4);(2,"e",3,5);] 
[(1,1);(2,2)] []
let _r1 = Grs.fromHomos r1l r1r
let r2l = Homo.fromList 
  [1;2] []
  [1;2;3] [(1,"a",1,1);(3,"0",3,2);(2,"X",2,3);(1,"e",3,4);(2,"e",3,5);]
  [(1,1);(2,2)] []
let r2r = Homo.fromList 
  [1;2] []
  [1;2;3] [(1,"a",1,1);(3,"1",3,2);(2,"a",2,3);(1,"e",3,4);(2,"e",3,5);]
  [(1,1);(2,2)] []
let _r2 = Grs.fromHomos r2l r2r

let r3l = Homo.fromList 
  [1;2] []
  [1;2;3] [(1,"A",1,1);(3,"0",3,2);(2,"B",2,3);(1,"e",3,4);(2,"e",3,5);]
  [(1,1);(2,2)] []
let r3r = Homo.fromList 
  [1;2] []
  [1;2;3] [(1,"AX",1,1);(3,"0",3,2);(2,"X",2,3);(1,"e",3,4);(2,"e",3,5);]
  [(1,1);(2,2)] []
let _r3 = Grs.fromHomos r3l r3r
let r4l = Homo.fromList 
  [1;2] []
  [1;2;3] [(1,"a",1,1);(3,"0",3,2);(2,"B",2,3);(1,"e",3,4);(2,"e",3,5);]
  [(1,1);(2,2)] []
let r4r = Homo.fromList 
  [1;2] []
  [1;2;3] [(1,"axw",1,1);(3,"1",3,2);(2,"BB",2,3);(1,"e",3,4);(2,"e",3,5);]
  [(1,1);(2,2)] []
let _r4 = Grs.fromHomos r4l r4r
let r5l = Homo.fromList 
  [1;2] []
  [1;2;3] [(1,"a",1,1);(3,"1",3,2);(2,"axw",2,3);(1,"e",3,4);(2,"e",3,5);]
  [(1,1);(2,2)] []
let r5r = Homo.fromList 
  [1;2] []
  [1;2;3] [(1,"axw",1,1);(3,"1",3,2);(2,"axw",2,3);(1,"e",3,4);(2,"e",3,5);]
  [(1,1);(2,2)] []
let _r5 = Grs.fromHomos r5l r5r
let r6l = Homo.fromList 
  [1;2] []
  [1;2;3] [(1,"A",1,1);(3,"1",3,2);(2,"axw",2,3);(1,"e",3,4);(2,"e",3,5);]
  [(1,1);(2,2)] []
let r6r = Homo.fromList 
  [1;2] []
  [1;2;3] [(1,"AB",1,1);(3,"1",3,2);(2,"ax",2,3);(1,"e",3,4);(2,"e",3,5);]
  [(1,1);(2,2)] []
let _r6 = Grs.fromHomos r6l r6r
let r7l = Homo.fromList 
  [1;2] []
  [1;2;3] [(1,"ax",1,1);(3,"1",3,2);(2,"axw",2,3);(1,"e",3,4);(2,"e",3,5);]
  [(1,1);(2,2)] []
let r7r = Homo.fromList 
  [1;2] []
  [1;2;3] [(1,"ax",1,1);(3,"1",3,2);(2,"ax",2,3);(1,"e",3,4);(2,"e",3,5);]
  [(1,1);(2,2)] []
let _r7 = Grs.fromHomos r7l r7r
let r8l = Homo.fromList 
  [1;2] []
  [1;2;3;4;5] [(1,"ax",1,1);(2,"1",2,2);(3,"ax",3,3);(4,"1",4,4);(5,"BB",5,5);
                (1,"e",2,6);(3,"e",2,7);(3,"e",4,8);(5,"e",4,9) ]
  [(1,1);(2,5)] []
let r8r = Homo.fromList 
  [1;2] []
  [1;2;3;4;5] [(1,"ax",1,1);(2,"1",2,2);(3,"BB",3,3);(4,"0",4,4);(5,"X",5,5);
                (1,"e",2,6);(3,"e",2,7);(3,"e",4,8);(5,"e",4,9) ]
  [(1,1);(2,5)] []
let _r8 = Grs.fromHomos r8l r8r
let r9l = Homo.fromList 
  [1;2] []
  [1;2;3;4;5] [(1,"AB",1,1);(2,"1",2,2);(3,"ax",3,3);(4,"1",4,4);(5,"BB",5,5);
                (1,"e",2,6);(3,"e",2,7);(3,"e",4,8);(5,"e",4,9) ]
  [(1,1);(2,5)] []
let r9r = Homo.fromList 
  [1;2] []
  [1;2;3;4;5] [(1,"AX",1,1);(2,"0",2,2);(3,"X",3,3);(4,"0",4,4);(5,"X",5,5);
                (1,"e",2,6);(3,"e",2,7);(3,"e",4,8);(5,"e",4,9) ]
  [(1,1);(2,5)] []
let _r9 = Grs.fromHomos r9l r9r
let r10l = Homo.fromList 
  [1;2] []
  [1;2;3] [(1,"a",1,1);(3,"1",3,2);(2,"AX",2,3);(1,"e",3,4);(2,"e",3,5);]
  [(1,1);(2,2)] []
let r10r = Homo.fromList 
  [1;2] []
  [1;2;3] [(1,"AX",1,1);(3,"1",3,2);(2,"XB",2,3);(1,"e",3,4);(2,"e",3,5);]
  [(1,1);(2,2)] []
let _r10 = Grs.fromHomos r10l r10r
let r11l = Homo.fromList 
  [1;2] []
  [1;2;3] [(1,"axw",1,1);(3,"1",3,2);(2,"AX",2,3);(1,"e",3,4);(2,"e",3,5);]
  [(1,1);(2,2)] []
let r11r = Homo.fromList 
  [1;2] []
  [1;2;3] [(1,"AX",1,1);(3,"1",3,2);(2,"XB",2,3);(1,"e",3,4);(2,"e",3,5);]
  [(1,1);(2,2)] []
let _r11 = Grs.fromHomos r11l r11r
let r12l = Homo.fromList 
  [1;2] []
  [1;2;3] [(1,"BB",1,1);(3,"1",3,2);(2,"AX",2,3);(1,"e",3,4);(2,"e",3,5);]
  [(1,1);(2,2)] []
let r12r = Homo.fromList 
  [1;2] []
  [1;2;3] [(1,"B",1,1);(3,"0",3,2);(2,"AXB",2,3);(1,"e",3,4);(2,"e",3,5);]
  [(1,1);(2,2)] []
let _r12 = Grs.fromHomos r12l r12r
let r13l = Homo.fromList 
  [1] []
  [1] [(1,"AX",1,1)] 
  [(1,1)] []
let r13r = Homo.fromList 
  [1] []
  [1] [(1,"AXB",1,1)] 
  [(1,1)] []
let _r13 = Grs.fromHomos r13l r13r
let r14l = Homo.fromList 
  [1;2] []
  [1;2;3] [(1,"AXB",1,1);(3,"1",3,2);(2,"XB",2,3);(1,"e",3,4);(2,"e",3,5);]
  [(1,1);(2,2)] []
let r14r = Homo.fromList 
  [1;2] []
  [1;2;3] [(1,"X",1,1);(3,"0",3,2);(2,"AXB",2,3);(1,"e",3,4);(2,"e",3,5);]
  [(1,1);(2,2)] []
let _r14 = Grs.fromHomos r14l r14r
let r15l = Homo.fromList 
  [1] []
  [1] [(1,"AXB",1,1)]
  [(1,1)] []
let r15r = Homo.fromList 
  [1] []
  [1] [(1,"X",1,1)]
  [(1,1)] []
let _r15 = Grs.fromHomos r15l r15r  
let metivier_1995_majAB_rules_1_2_5_7_8_only = fromRulesListAndName [
    (* _r1; *)
    _r2;_r5;_r7;_r8
    ] "metivier_1995_majAB_rules_1_2_5_7_8_only" ~monic_matching:true
let metivier_1995_majAB = fromRulesListAndName [
  _r1;_r2;_r3;_r4;_r5;_r6;_r7;_r8;_r9;_r10;_r11;_r12;_r13;_r14;_r15
  ] "mametivier_1995_majAB" ~monic_matching:true
(*********************
  simple relabeling 
*****************************)
let l = Homo.fromList
  [1;2] [] 
  [1;2] [(1,"a",2,1)] 
  [(1,1);(2,2)] []
let r = Homo.fromList
  [1;2] []
  [1;2] [(1,"b",2,1)] 
  [(1,1);(2,2)] []
let relabeling = Grs.fromHomos l r
let relabeling =fromRulesListAndName [relabeling] "relabeling"
(* nonwf n = 4 *)
let r1l = Homo.fromList
  [1;2] [] 
  [1;2] [(1,"a",2,1)] 
  [(1,1);(2,2)] []
let r1r = Homo.fromList
  [1;2] [] 
  [1;2] [(1,"b",2,1);(1,"b",2,2); (1,"b",2,3)] 
  [(1,1);(2,2)] []

let r2l = Homo.fromList
  [1;2] [] 
  [1;2] [(1,"b",2,1)] 
  [(1,1);(2,2)] []
let r2r = Homo.fromList
  [1;2] [] 
  [1;2] [(1,"c",2,1);(1,"c",2,2);(1,"c",2,3)] 
  [(1,1);(2,2)] []

let r4l = Homo.fromList
  [1;2] [] 
  [1;2] [(1,"c",2,1)] 
  [(1,1);(2,2)] []
let r4r = Homo.fromList
  [1;2] [] 
  [1;2] [(1,"d",2,1);(1,"d",2,2);(1,"d",2,3)] 
  [(1,1);(2,2)] []

let r4 = Grs.fromHomos r4l r4r

let r3l = Homo.fromList
  [1;2] [] 
  [1;2] (List.init 28 (fun i -> (1,"d",2,i+1)))
  [(1,1);(2,2)] []
let r3r = Homo.fromList
  [1;2] [] 
  [1;2] [(1,"a",2,1)] 
  [(1,1);(2,2)] []

(* il faut max weight = 4 pour resoudre *)
let r1 = Grs.fromHomos r1l r1r
let r2 = Grs.fromHomos r2l r2r
let r3 = Grs.fromHomos r3l r3r
let nonwf_n3_cube = fromRulesListAndName [r1;r2;r3;r4] "nonwf_n3_cube"



(* nonwf n = 3*)
let r1l = Homo.fromList
  [1;2] [] 
  [1;2] [(1,"a",2,1)] 
  [(1,1);(2,2)] []
let r1r = Homo.fromList
  [1;2] [] 
  [1;2] [(1,"b",2,1);(1,"b",2,2); (1,"b",2,3)] 
  [(1,1);(2,2)] []

let r2l = Homo.fromList
  [1;2] [] 
  [1;2] [(1,"b",2,1)] 
  [(1,1);(2,2)] []
let r2r = Homo.fromList
  [1;2] [] 
  [1;2] [(1,"c",2,1);(1,"c",2,2);(1,"c",2,3)] 
  [(1,1);(2,2)] []

let r3l = Homo.fromList
  [1;2] [] 
  [1;2] (List.init 10 (fun i -> (1,"c",2,i+1)))
  [(1,1);(2,2)] []
let r3r = Homo.fromList
  [1;2] [] 
  [1;2] [(1,"a",2,1)] 
  [(1,1);(2,2)] []




(* il faut max weight = 4 pour resoudre *)
let r1 = Grs.fromHomos r1l r1r
let r2 = Grs.fromHomos r2l r2r
let r3 = Grs.fromHomos r3l r3r
let nonwf_n3 = fromRulesListAndName [r1;r2;r3] "nonwf_n3"
let nonwf_n3_rules_1_2_only = fromRulesListAndName [r1;r2] "nonwf_n3_rules_1_2_only"



let r4l = Homo.fromList
  [1;2] [] 
  [1;2;3] [(1,"a",3,1);(3,"a",2,2)]
  [(1,1);(2,2)] []
let r4r = Homo.fromList
  [1;2] [] 
  [1;2;3;4] [(1,"a",3,1);(3,"b",4,2);(4,"a",2,3)] 
  [(1,1);(2,2)] []
let r4 = Grs.fromHomos r4l r4r
let r5l = Homo.fromList
  [1;2] [] 
  [1;2;3] [(1,"b",3,1);(3,"b",2,2)]
  [(1,1);(2,2)] []
let r5r = Homo.fromList
  [1;2] [] 
  [1;2;3;4] [(1,"b",3,1);(3,"c",4,2);(4,"b",2,3)] 
  [(1,1);(2,2)] []
let r5 = Grs.fromHomos r5l r5r
let r6l = Homo.fromList
  [1;2] [] 
  [1;2;3] [(1,"a",3,1);(3,"a",2,2)]
  [(1,1);(2,2)] []
let r6r = Homo.fromList
  [1;2] [] 
  [1;2;3;4] [(1,"a",3,1);(3,"c",4,2);(4,"a",2,3)] 
  [(1,1);(2,2)] []
let r6 = Grs.fromHomos r6l r6r
let nonwf_n3_modified = fromRulesListAndName [r1;r2;r3;r4;r5;r6] "nonwf_n3_modified"

(* 

let r4l = Homo.fromList
  [1;2] [] 
  [1;2;3] [(1,"a",3,1);(3,"a",2,2)]
  [(1,1);(2,2)] []
let r4r = Homo.fromList
  [1;2] [] 
  [1;2;3;4] [(1,"a",3,1);(3,"b",4,2);(4,"a",2,3)] 
  [(1,1);(2,2)] []
let r4 = Grs.fromHomos r4l r4r
let r5l = Homo.fromList
  [1;2] [] 
  [1;2;3] [(1,"b",3,1);(3,"b",2,2)]
  [(1,1);(2,2)] []
let r5r = Homo.fromList
  [1;2] [] 
  [1;2;3;4] [(1,"b",3,1);(3,"c",4,2);(4,"b",2,3)] 
  [(1,1);(2,2)] []
let r5 = Grs.fromHomos r5l r5r
let r6l = Homo.fromList
  [1;2] [] 
  [1;2;3] [(1,"a",3,1);(3,"a",2,2)]
  [(1,1);(2,2)] []
let r6r = Homo.fromList
  [1;2] [] 
  [1;2;3;4] [(1,"a",3,1);(3,"c",4,2);(4,"a",2,3)] 
  [(1,1);(2,2)] []
let r6 = Grs.fromHomos r6l r6r
let nonwf_n3_modified = fromRulesListAndName [r1;r2;r3;r4;r5;r6] "nonwf_n3_modified" *)


let grss =  
  [bruggink_2014_ex1;
  bruggink_2014_ex5; 
  bruggink_2014_ex5_rule_1_and_2_only; 
  bruggink_2014_ex6;
  bruggink_2014_ad_hoc_routing_protocol;
  bruggink_2014_ad_hoc_routing_protocol_rules_sm_ar_only;
  ] @ [
    bruggink_2015_ex2;
  bruggink_2015_ex4;
  bruggink_2015_ex4_rules_2_3_4;
  bruggink_2015_ex4_r34;
  bruggink_2015_ex5;
  bruggink_2015_ex5_rules_3_4;
  bruggink_2015_ex6;
  bruggink_2015_ex6_rules_2_3_4_5_6;
  bruggink_2015_ex6_modified;
  ] @ [
  endrullis_2024_ex6_2;
  endrullis_2024_ex6_3;
  (* endrullis_2023_ex6_4;  SIMPLE GRAPH *)
  endrullis_2024_exd1;
  endrullis_2024_exd2;
  endrullis_2024_exd3;
] @ [
  plump_1995_ex4_1
] @[
  plump_1995_ex3_8;
  plump_2018_ex3;
  plump_2018_ex4;
  plump_2018_ex5;
  plump_2018_ex6;
  plump_2018_ex6_variant;
  plump_2018_fig10;
  plump_2018_ex6_variant_monic
] @ [  
  metivier_1995_majAB;
  metivier_1995_majAB_rules_1_2_5_7_8_only;
  metivier_1995_majAB_rules_2_5_7_8_only_bis;
  metivier_1995_majAB_rules_2_5_7_8_only_bis_monic
] @[
  nonwf_n3_cube;
  nonwf_n3;
  nonwf_n3_rules_1_2_only;
  nonwf_n3_modified
] @ [
  overbeek_2024_ex5d3 ;
  overbeek_2024_ex5d5;
  overbeek_2024_ex5d6;
  overbeek_2024_ex5d8
] @ [
  my_ex45
]