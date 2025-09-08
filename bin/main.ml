open LyonParallel
(* File-: simple_repl.ml *)
let time = ref 0.
let nb_successful_simplifications = ref 0
let traces = ref ""
let (log:(GraphRewritingSystem.t list
* string
* Semiring.semiring_t
* bool) 
list ref) = ref []
module StringSet = Set.Make(String)
let systems = ConcretGraphRewritingSystems.available_graph_rewriting_systems 
let (approach:Parallel.meta_stragety_t list ref) = ref []
let (timeout : float option ref) = ref None
let (system : ConcretGraphRewritingSystems.named_grs option ref) = ref None
let ruler_graph = ref None
let (system_current : ConcretGraphRewritingSystems.named_grs option ref) = ref None
let (ran:bool ref) = ref false
let reset_sol_file = ref true
(* Function to handle user commands *)
let undefined_command_msg cmd = 
   (Printf.sprintf "Undefined command [%s].\n" cmd)
let help_msg () = (Printf.sprintf "Type 'help' for help.")

let reset_all () =
  time := 0.;
  nb_successful_simplifications := 0;
  traces := "";
  (* log := []; *)
  (* approach := []; *)
  timeout := None;
  system := None;
  system_current := None
  (* ran := false *)
  (* reset_sol_file := true; *)
  (* Printf.printf "All reset.\n" *)
let cmd_select_processing n cmd = 
  try 
    let res = `System (n|> int_of_string) in
    reset_sol_file := true; 
    res
  with _ -> `Undefined (undefined_command_msg cmd)

let cmd_select_system_of_name_processing name cmd = 
  try 
    let res = `Select_system_of_name name in
    reset_sol_file := true; 
    res
  with _ -> `Undefined (undefined_command_msg cmd)

let cmd_select_ruler_graph_processing name = 
  `select_ruler_graph name

let cmd_reset_strategies () = 
  approach := [];
  Printf.printf "Strategies reset.\n"
  let cmd_recap () = 
    Printf.printf "
      Original System: %s\n
      Remaining Rules: %s\n
      Terminating : %s\n
      Total Resolution Time : %f\n
      Traces : %s\n
      " 
    (* original system *)
    (match !system with
    | None -> "no system selected" 
    | Some grs -> grs.name) 
    (* remaind rules *)
    (match !system, !system_current with
    |Some grs, Some grs_current -> 
      let indices_of_remaining_rules = (List.mapi 
        (fun i r ->
          if List.mem r grs_current.grs then i else -1
        )
      grs.grs) 
      |> List.filter (fun x -> x >= 0) in
      if List.length indices_of_remaining_rules > 0 then
        indices_of_remaining_rules |> List.map (fun x ->Printf.sprintf " rule %s " (Int.to_string x))|> String.concat ";"
      else "none"
    |None, None -> "[]"
    |_ -> failwith __LOC__)
    (* log *)
    (* (match !system with
    | None -> ""
    | Some grs -> List.map 
      (fun (eliminated_rules, filename, _, _) ->
        Printf.sprintf "    rules %s eliminated by %s"
        (List.mapi 
          (fun i r -> if List.mem r eliminated_rules then i else -1) 
          grs.grs
        |> List.filter (fun x -> x <> -1) 
        |> List.map string_of_int
        |> String.concat ";")
        filename)
      !log
    |> String.concat "\n"
    |> Printf.sprintf "\n%s") *)
    (* involed strategies *)
    (* (List.map (fun (_, _, semiring, integer) ->
      match semiring with
      |Semiring.Arctic -> if integer then "a" else "A"
      |Semiring.Tropical ->if integer then "t" else "T"
      |Semiring.Arithmetic -> if integer then "n" else "N"
    )
    !log 
    |> StringSet.of_list
    |> StringSet.elements
    |> String.concat "") *)
    (* Strategies *)
    (* (List.map Parallel.meta_stragety_to_str !approach
    |> String.concat " || "
    |> Printf.sprintf "[%s]") *)
    (* termination *)
    (match !system_current with
     | None -> "unknown"
     | Some grs -> if List.length grs.grs = 0 then "yes" else
      "unknown")
    (* reset solution file *)
    (* !reset_sol_file *)
    (* resolution time *)
    !time 
    (* traces *)
    !traces
let cmd_run () = 
  begin
    match !system_current, !approach, !timeout with
    |_,[],_ -> Printf.printf "You need to add some strategies before\nType 'help' for help.\n"; 
    |None,_,_ -> Printf.printf "You need to select a rewriting system before\nType 'help' for help.\n"; 
    |Some grs, metas, Some t -> 
      begin
        let start_time = Unix.gettimeofday () in
        ran := true;
        begin
          match Parallel.parallel_solving_with_meta_strategy ~grs:(ref grs) ~metas 
          ~timeout:t ~reset_sol_file:!reset_sol_file with
          | grs, log_local ->
            system_current := Some grs;
            log := !log @ log_local 
        end;
        reset_sol_file := false;
        time := !time +. (Unix.gettimeofday () -. start_time);
      end;
    (* cmd_recap () *)
    | _ -> 
      begin 
        Printf.printf "Something is wrong\n"; 
        print_endline (help_msg ());
      end
    end
let cmd_timeout f =
  timeout := Some f  
let cmd_add_strategy s =
  approach := s :: !approach; 
  Printf.printf "Approach %s selected.\n" (s |> Parallel.meta_stragety_to_str); 
  Printf.printf "timeout is set to %f seconds.\n" (Option.get !timeout)

let cmd_select_system n =
  (* to do updated *)
  system := Some (List.nth systems n);
  system_current := Some (List.nth systems n);
  Printf.printf "System %d.%s selected.\n" n (List.nth systems n).name
  ;time := 0.;
  log := []

let cmd_select_system_of_name name =
  let s = match List.find_opt (fun x -> String.equal name (ConcretGraphRewritingSystems.get_name x)) systems with
    |None -> failwith (Printf.sprintf "No system named %s" name)
    |Some x -> Some x in
      begin 
        reset_all ();
        system := s;
        system_current := s;
        Printf.printf "System \"%s\" selected.\n" name
        ;time := 0.;
        log := []
      end

let cmd_select_ruler_graph name =
  let rg = match List.find_opt (fun x -> String.equal name (x |> Ruler_graph.get_name)) Ruler_graph.ruler_graphs with
        |None -> failwith (Printf.sprintf "No system named %s" name)
        |Some x -> Some x in 
  ruler_graph := rg;
  Printf.printf "Ruler-graph \"%s\" selected.\n" name

let cmd_systems () = 
  let sys_names = List.mapi (fun i (s:ConcretGraphRewritingSystems.named_grs) -> Printf.sprintf "%d.%s" i s.name) systems in
    let s = String.concat "\n" sys_names in
    print_endline s
    let cmd_show_ruler_graphs () =
      List.iteri 
        (fun i (rulergraph:Ruler_graph.rulerGraph) ->
          Printf.sprintf "ruler graph %d : \ngraph: %s\n forbidden context: %s\nname: %s\ndescription: %s\n\n"
          i 
          (MGraph.toStr (rulergraph.x))
          (MGraph.toStr (rulergraph.fx |> Option.get|>GraphHomomorphism.codom))
          rulergraph.name
          rulergraph.description 
          |> print_endline
        )  
        Ruler_graph.ruler_graphs
let cmd_try_type_graph_processing system auto_defaut_strategies timeout =
  try
    let system = int_of_string system in
    let strategies = List.map 
    (fun s ->
      (* if List.mem s auto_defaut_strategies then *)
      match s with
      (* | 'a' -> Some Parallel.Auto_total_int_arctic  
      | 'n' -> Some Auto_total_int_arithmetic  
      | 't' -> Some Auto_total_int_tropical 
      | 'A' -> Some Auto_total_real_arctic 
      | 'N' -> Some Auto_total_real_arithmetic  
      | 'T' -> Some Auto_total_real_tropical   *)
      | "A" -> Parallel.Auto_total_int_arctic  
      | "N" ->  Auto_total_int_arithmetic  
      | "T" -> Auto_total_int_tropical 
      | "a" ->  Auto_total_real_arctic 
      | "n" -> Auto_total_real_arithmetic  
      | "t" ->  Auto_total_real_tropical  
      | _ -> failwith __LOC__
      (* else assert false *)
    )
    (* ['a';'n';'t';'N';'A';'T'] in *)
    auto_defaut_strategies  in
    let timeout = float_of_string timeout in
    `try_type_graph (system,strategies,timeout) (* auto_defaut_strategies is a word from {a,n,t,A,N,T}*, ex: ant,ANt,Ta *)
  with _ -> failwith __LOC__

let cmd_type_graph_processing auto_defaut_strategies timeout =
  try
    let strategies = List.map 
    (fun s ->
      (* if List.mem s auto_defaut_strategies then *)
      match s with
      (* | 'a' -> Some Parallel.Auto_total_int_arctic  
      | 'n' -> Some Auto_total_int_arithmetic  
      | 't' -> Some Auto_total_int_tropical 
      | 'A' -> Some Auto_total_real_arctic 
      | 'N' -> Some Auto_total_real_arithmetic  
      | 'T' -> Some Auto_total_real_tropical   *)
      | "A" -> Parallel.Auto_total_int_arctic  
      | "N" ->  Auto_total_int_arithmetic  
      | "T" -> Auto_total_int_tropical 
      | "a" ->  Auto_total_real_arctic 
      | "n" -> Auto_total_real_arithmetic  
      | "t" ->  Auto_total_real_tropical  
      | _ -> failwith __LOC__
      (* else assert false *)
    )
    (* ['a';'n';'t';'N';'A';'T'] in *)
    auto_defaut_strategies  in
    let timeout = float_of_string timeout in
    `type_graph (strategies,timeout) (* auto_defaut_strategies is a word from {a,n,t,A,N,T}*, ex: ant,ANt,Ta *)
  with _ -> failwith __LOC__

let cmd_try_type_graph_no_auto_processing system nb_smr smrs =
  try
    let system = int_of_string system in
    let nb_smr = int_of_string nb_smr in
    let smrs_info = ref [] in
    for i = 0 to nb_smr - 1 do
      smrs_info := 
      (
        Semiring.of_string (List.nth smrs (i+ nb_smr * 1)),    (* semiring *)
        int_of_string ( List.nth smrs (i+ nb_smr * 0) ),    (* graph dimension *)
        bool_of_string ( List.nth smrs (i + nb_smr * 2) )   (* intergerOrNot*)
        (* int_of_string ( List.nth smrs (i + nb_smr * 3) ),    *)
        (* bool_of_string ( List.nth smrs (i + nb_smr * 4) )  opt *)
        ):: !smrs_info
    done;
    let timeout = 200.0 in
    `try_type_graph_no_auto (system,!smrs_info,timeout) 
  with _ -> failwith __LOC__

let cmd_showme () = 
  match !ran with
  | true -> Sys.command "cat tmp/sol.sol" |> ignore
  | false ->
    print_endline "try some methods before.\n"
  
let cmd_try_type_graph system auto_defaut_strategies time =
  cmd_select_system system;
  cmd_timeout time;
  cmd_reset_strategies ();
  List.iter cmd_add_strategy auto_defaut_strategies;
  cmd_run ();
  (* cmd_showme (); *)
;;
(*iterative version of cmd_try_type_graph*)
let cmd_type_graph auto_defaut_strategies userdefined_timeout =
  cmd_timeout userdefined_timeout;
  cmd_reset_strategies ();
  List.iter cmd_add_strategy auto_defaut_strategies;
  begin
    match !system_current, !approach, !timeout with
    |_,[],_ -> Printf.printf "You need to add some strategies before\nType 'help' for help.\n"; 
    |None,_,_ -> Printf.printf "You need to select a rewriting system before\nType 'help' for help.\n"; 
    |Some grs, metas, Some t -> 
      begin
        let start_time = Unix.gettimeofday () in
        ran := true;
        begin
          match Parallel.parallel_solving_with_meta_strategy ~grs:(ref grs) ~metas 
          ~timeout:t ~reset_sol_file:!reset_sol_file with
          | grs, log_local ->
            system_current := Some grs;
            log := !log @ log_local 
        end;
        reset_sol_file := false;
        (*below : trace generation *)
        (* let pb = ConcretGraphRewritingSystems.named_grs_to_problem grs in *)
                    (* let all_rules = ConcretGraphRewritingSystems.rules_of_problem pb in *)
                    (* let indices_of_remaining_rules, indices_of_removed_rules = List.partition
                          (fun i -> 
                            List.mem (List.nth all_rules i) grs.grs
                          ) (List.init (List.length all_rules) (fun x -> x)) in *)
                    (* let str_remaining_rules = if List.is_empty indices_of_remaining_rules then "None" else (indices_of_remaining_rules |> List.map string_of_int |> String.concat ";") in
                    let str_removed_rules = if List.is_empty indices_of_removed_rules then "None" else (indices_of_removed_rules |> List.map string_of_int |> String.concat ";") in *)
                     traces := Printf.sprintf 
                    "%s\n  ======== successful simplifications : number %d  ==========\n  Method: Type graph Method \n  %s\n  Resolution time: %f seconds\n
                  "
                  !traces 
                  (nb_successful_simplifications := !nb_successful_simplifications + 1;!nb_successful_simplifications)
                   (
                    let ic = open_in "tmp/sol.sol" in
                    In_channel.input_all ic
                    )
                (* (indices_of_removed_rules |> List.map string_of_int |> String.concat ";"); *)
                  (let resol_time = Unix.gettimeofday () -. start_time in 
                      time := !time +. resol_time
                      ; resol_time)
      end;
    (* cmd_recap () *)
    | _ -> 
      begin 
        Printf.printf "Something is wrong\n Loc %s" __LOC__; 
      end
    end
  
  (* cmd_showme (); *)
;;

let cmd_try_type_graph_no_auto system smrs_info timeout =
  cmd_select_system system;
  cmd_timeout timeout;
  cmd_reset_strategies ();
  List.iter (fun (s,n,integerOrNot) -> cmd_add_strategy (Parallel.User 
    (Parallel.Strat (s,n,integerOrNot,0,false))))
    (* Semiring.semiring_t * size_t * integerOrNot * maxWeight_t * optimizedTypegraph_t -> strategy_t)  *)
    smrs_info;
  cmd_run ();
  (* cmd_showme (); *)
;;

let cmd_try_subgraph_counting_no_forbidden_context system =
  (* todo : unify two systems *)
  let system = List.nth systems system in
  let pb = ConcretGraphRewritingSystems.named_grs_to_problem system in
  let _, res = Termination.isTerminating pb in
  let _ = Termination.interpret res in
  ()
;;
let cmd_subgraph_counting_no_forbidden_context () =
  (* todo : unify two systems *)
   match !system_current with
  | None -> failwith "No system selected"
  | Some system ->
    begin
      let start_time = Unix.gettimeofday () in
      let pb = ConcretGraphRewritingSystems.named_grs_to_problem system in
      let ruler_graph, res = Termination.isTerminating pb in
      (* system_current := Some (ConcretGraphRewritingSystems.fromRulesListAndName (ConcretGraphRewritingSystems.rules_of_problem res) system.name); *)
      let all_rules = ConcretGraphRewritingSystems.rules_of_problem pb in
      let remaining_rules = (ConcretGraphRewritingSystems.rules_of_problem res) in
      system_current := Some (ConcretGraphRewritingSystems.fromRulesListAndName remaining_rules system.name);
      let indices_of_remaining_rules, indices_of_removed_rules = List.partition
        (fun i -> 
          List.mem (List.nth all_rules i) remaining_rules
        ) (List.init (List.length all_rules) (fun x -> x)) in
      let str_remaining_rules = if List.is_empty indices_of_remaining_rules then "None" else (indices_of_remaining_rules |> List.map string_of_int |> String.concat ";") in
      let str_removed_rules = if List.is_empty indices_of_removed_rules then "None" else (indices_of_removed_rules |> List.map string_of_int |> String.concat ";") in
      (* let remaining_rules = ConcretGraphRewritingSystems.rules_of_problem res in
      let indices_of_removed_rules_opt = List.mapi
        (fun i r ->
          if List.mem r all_rules then Some i else None
        ) remaining_rules in 
      let indices_of_removed_rules = List.filter_map 
        (fun x -> if Option.is_some x then x else None) 
        indices_of_removed_rules_opt in *)
      system_current := Some (ConcretGraphRewritingSystems.fromRulesListAndName (ConcretGraphRewritingSystems.rules_of_problem res) system.name);
      match ruler_graph with
        | None -> ()
        | Some rg -> begin
          traces := Printf.sprintf 
            "%s\n
            ======== successful simplifications : number %d ==========\n  Method: Subgraph counting without forbidden context\n  rule graph : %s\n  Removed rules indices: %s\n  Remaining rules indices: %s\n  Resolution time: %f seconds\n
          "
          !traces  
          (nb_successful_simplifications := !nb_successful_simplifications + 1;!nb_successful_simplifications)
          (* this method use ruler-graph without forbidden context *)
          ( 
            MGraph.toStr (rg |> Ruler_graph.get_x)
          )
          (* (MGraph.toStr (Option.get !ruler_graph |> Ruler_graph.get_x)) *)
          str_removed_rules 
          str_remaining_rules
        (* (indices_of_removed_rules |> List.map string_of_int |> String.concat ";"); *)
          (let resol_time = Unix.gettimeofday () -. start_time in 
              time := !time +. resol_time
              ; resol_time)
      end;
  end
;; 

let cmd_try_subgraph_counting_one_forbidden_context (system,rulergraph) =
  (* todo : unify two systems *)
  let system = List.nth systems system in
  let rulergraph = List.nth Ruler_graph.ruler_graphs rulergraph in 
  match Subgraph_counting_forbidden_contexts.terminating_counting_subgraph_with_forbidden_context rulergraph system with
  | true, report,_ -> Printf.sprintf "  *** Termination proved ! *** \n %s\ndescription of the ruler-graph: %s" report rulergraph.description |> print_endline
  | false, report,_ -> Printf.sprintf "  *** Termination Unknown ! *** \n %s\n" report |> print_endline
(* ;;
let cmd_subgraph_counting_one_forbidden_context (name_of_rulergraph) =
  (* todo : unify two systems *)
  match !system_current with
  | None -> failwith "No system selected"
  | Some system -> 
  let rulergraph = 
    match List.find_opt (fun (x:Ruler_graph.rulerGraph) -> String.equal name_of_rulergraph x.name) (Ruler_graph.ruler_graphs:Ruler_graph.rulerGraph list) with
          |None -> failwith (Printf.sprintf "No ruler-graph named %s" name_of_rulergraph)
          |Some x -> x in   
  (* let (rulergraph,_,_) = List.nth Ruler_graph.ruler_graphs rulergraph in *)
  match Subgraph_counting_forbidden_contexts.terminating_counting_subgraph_with_forbidden_context rulergraph system with
  | true, _, remained_rules -> 
    begin
      (* Printf.sprintf "  *** Termination proved ! *** \n %s\ndescription of the ruler-graph: %s" report description |> print_endline *)
      system_current := Some ( ConcretGraphRewritingSystems.fromRulesListAndName remained_rules (Option.get !system_current).name);
    end 
  | false, report,_ -> Printf.sprintf "  *** Termination Unknown ! *** \n %s\n" report |> print_endline
;; *)

let cmd_subgraph_counting_one_forbidden_context () =
  (* todo : unify two systems *)
  match !system_current with
  | None -> failwith "No system selected"
  | Some system -> 
    begin
      match !ruler_graph with
            |None -> failwith (Printf.sprintf "Select a ruler-graph first")
            |Some ruler_graph -> 
              begin
                let start_time = Unix.gettimeofday () in
                (* let (rulergraph,_,_) = List.nth Ruler_graph.ruler_graphs rulergraph in *)
                match Subgraph_counting_forbidden_contexts.terminating_counting_subgraph_with_forbidden_context ruler_graph system with
                | true, _, remaining_rules -> 
                  begin 
                    system_current := Some ( ConcretGraphRewritingSystems.fromRulesListAndName remaining_rules (Option.get !system_current).name);
                    (* below : generation of trace *)
                    let pb = ConcretGraphRewritingSystems.named_grs_to_problem system in
                    let all_rules = ConcretGraphRewritingSystems.rules_of_problem pb in
                    let indices_of_remaining_rules, indices_of_removed_rules = List.partition
                          (fun i -> 
                            List.mem (List.nth all_rules i) remaining_rules
                          ) (List.init (List.length all_rules) (fun x -> x)) in
                    let str_remaining_rules = if List.is_empty indices_of_remaining_rules then "None" else (indices_of_remaining_rules |> List.map string_of_int |> String.concat ";") in
                    let str_removed_rules = if List.is_empty indices_of_removed_rules then "None" else (indices_of_removed_rules |> List.map string_of_int |> String.concat ";") in
                     traces := Printf.sprintf 
                    "%s\n  ======== successful simplifications : number %d ==========\n  Method: Subgraph counting with one forbidden context\n  rule graph : %s\n  Removed rules indices: %s\n  Remaining rules indices: %s\n  Resolution time: %f seconds\n
                  "
                  !traces  
                  (nb_successful_simplifications := !nb_successful_simplifications + 1;!nb_successful_simplifications)
                  (* this method use ruler-graph without forbidden context *)
                  ( 
                    Ruler_graph.to_str ruler_graph
                  )
                  (* (MGraph.toStr (Option.get !ruler_graph |> Ruler_graph.get_x)) *)
                  str_removed_rules 
                  str_remaining_rules
                (* (indices_of_removed_rules |> List.map string_of_int |> String.concat ";"); *)
                  (let resol_time = Unix.gettimeofday () -. start_time in 
                      time := !time +. resol_time
                      ; resol_time)
                  end 
                | false, report,_ -> Printf.sprintf "  *** failed ! *** \n %s\n" report |> print_endline
              end
  end
;;

let handle_command cmd =
  let parts = Str.(split (regexp " +") cmd) in
  if List.is_empty parts then `Continue else
  match parts with
  | ["exit"] -> `Exit
  | ["timeout"; t] -> `timeout (float_of_string t)
  | ["systems"] -> `Systems
  | ["rulergraphs"] -> `show_ruler_graphs
  | ["select"; n] -> cmd_select_processing n cmd
  | ["select_system_by_name"; name] -> cmd_select_system_of_name_processing name cmd
  | ["select_ruler_graph"; name] -> cmd_select_ruler_graph_processing name
  | ["reset_strategies"] -> `Reset_strategies 
  | ["showme"] -> `show_certificat
  | ["run"] -> `run
  | "try_type_graph" :: system :: timeout :: auto_defaut_strategies -> cmd_try_type_graph_processing system auto_defaut_strategies timeout
  (* iterative version *)
  | "type_graph" :: timeout :: auto_defaut_strategies -> cmd_type_graph_processing auto_defaut_strategies timeout
  | "try_type_graph_no_auto" :: nb_smr :: system :: smrs ->
  cmd_try_type_graph_no_auto_processing system nb_smr smrs
  | "try_subgraph_counting_no_forbidden_context" :: system :: []-> `try_subgraph_counting_no_forbidden_context (int_of_string system)
  | "subgraph_counting_no_forbidden_context" :: [] -> 
    `subgraph_counting_no_forbidden_context
  | "try_subgraph_counting_one_forbidden_context" :: system :: [rg]-> `try_subgraph_counting_one_forbidden_context (int_of_string system, int_of_string rg)
  (* iterative version *)
  | "subgraph_counting_one_forbidden_context" :: []-> `subgraph_counting_one_forbidden_context
  | ["recap"] -> `recap 
  | ["help"] ->
    `Print_help_msg 
    "to do ...
  "
  | "add_parallel_strategy_auto" :: coefficient :: semiring :: maxSize :: maxWeight :: optimized :: [] -> 
    begin  
      try
        let maxSize = int_of_string maxSize in
        let maxWeight = int_of_string maxWeight in
        let optimized = bool_of_string optimized in
        let semiring = Semiring.of_string semiring in
        match coefficient with 
        |"int" -> `Method (Parallel.Auto_int (semiring, maxSize, maxWeight, optimized))
        |"float" -> `Method (Parallel.Auto_real (semiring, maxSize, optimized))
        | _ -> raise (Failure "unsupported coefficient type")
      with Failure _ ->
        `Undefined (undefined_command_msg cmd) 
      end
  | "add_parallel_strategy_auto:Auto_total" :: [] -> 
    begin 
     `Method (Parallel.Auto_total)
    end
  | "add_parallel_strategy_auto:Auto_total_int" :: [] -> 
    begin 
    (* let timeout = timeout |> float_of_string in *)
      `Method (Parallel.Auto_total_int) 
    end
  | "add_parallel_strategy_auto:Auto_total_int_tropical"  :: [] -> 
    begin 
    (* let timeout = timeout |> float_of_string in *)
      `Method (Parallel.Auto_total_int_tropical) 
    end 
  | "add_parallel_strategy_auto:Auto_total_int_arctic" :: [] -> 
    begin 
    (* let timeout = timeout |> float_of_string in *)
      `Method (Parallel.Auto_total_int_arctic) 
    end
  | "add_parallel_strategy_auto:Auto_total_int_arithmetic" :: [] -> 
    begin 
    (* let timeout = timeout |> float_of_string in *)
      `Method (Parallel.Auto_total_int_arithmetic) 
    end
  | "add_parallel_strategy_auto:Auto_total_real" :: [] -> 
    begin 
    (* let timeout = timeout |> float_of_string in *)
      `Method (Parallel.Auto_total_real)  
    end 
  | "add_parallel_strategy_auto:Auto_total_real_tropical" :: [] -> 
    begin 
    (* let timeout = timeout |> float_of_string in *)
      `Method (Parallel.Auto_total_real_tropical) 
    end 
  | "add_parallel_strategy_auto:Auto_total_real_arctic" :: [] -> 
    begin 
    (* let timeout = timeout |> float_of_string in *)
      `Method (Parallel.Auto_total_real_arctic) 
    end
  | "add_parallel_strategy_auto:Auto_total_real_arithmetic" :: [] -> 
    begin 
    (* let timeout = timeout |> float_of_string in *)
      `Method (Parallel.Auto_total_real_arithmetic) 
    end
  | _ -> `Undefined (undefined_command_msg cmd)

(* REPL function *)
let rec repl () =
  begin 
    (* cmd_systems (); *)
    print_string ">> ";  (* Display prompt *)
    flush stdout;        (* Ensure the prompt appears immediately *)
    try
      let line = read_line () in
      match handle_command line with
      | `Continue -> ()
      | `Exit ->
          print_endline "Goodbye!"
      | `Systems -> cmd_systems ()
      | `show_ruler_graphs -> cmd_show_ruler_graphs ()
      | `System n -> cmd_select_system n
      | `Select_system_of_name name -> cmd_select_system_of_name name
      | `select_ruler_graph name -> cmd_select_ruler_graph name
      | `show_certificat -> cmd_showme () 
      | `run -> cmd_run ()
      |`try_type_graph (system,auto_defaut_strategies,timeout) -> 
        cmd_try_type_graph system auto_defaut_strategies timeout
      (*iterative version of try_type_graph*)
      |`type_graph (auto_defaut_strategies,timeout) -> 
        cmd_type_graph auto_defaut_strategies timeout
      |`try_type_graph_no_auto (system,smrs_info,timeout) ->
        cmd_try_type_graph_no_auto system smrs_info timeout 
      | `Print_help_msg msg -> print_endline msg;
      | `Undefined msg -> print_endline msg;
      | `Reset_strategies -> cmd_reset_strategies ()
      | `timeout f -> cmd_timeout f
      | `Method app ->
        cmd_add_strategy app
      | `recap -> cmd_recap ()
      | `try_subgraph_counting_no_forbidden_context system -> cmd_try_subgraph_counting_no_forbidden_context system
      (* iterative *)
      | `subgraph_counting_no_forbidden_context ->  cmd_subgraph_counting_no_forbidden_context ()
      | `try_subgraph_counting_one_forbidden_context args -> cmd_try_subgraph_counting_one_forbidden_context args
      (* iterative *)
      (* | `subgraph_counting_one_forbidden_context args -> cmd_subgraph_counting_one_forbidden_context args *)
      | `subgraph_counting_one_forbidden_context -> cmd_subgraph_counting_one_forbidden_context ()
      
      
    with
    (* Handle Ctrl+D (end of input) gracefully *)
    | End_of_file -> print_endline "\nGoodbye!"; exit 0 
    | e -> Printf.printf "Error: %s\n" (Printexc.to_string e);
  end;
  flush stdout;  
  repl ()

(* Entry point of the program *)
let () =
  print_endline "Type 'help' for a list of commands.";
  repl ()




(****  subgraph counting 2024 02 09  *****)
[@@@warning "-33"]

open LyonParallel.ConcretGraphRewritingSystems
open LyonParallel.Termination
[@@@warning "-33"]
(*********)