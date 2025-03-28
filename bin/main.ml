open LyonParallel
(* File-: simple_repl.ml *)
let time = ref 0.
let (log:(GraphRewritingSystem.t list
* string
* Semiring.semiring_t
* bool) 
list ref) = ref []
module StringSet = Set.Make(String)
let systems = ConcretGraphRewritingSystems.grss 
let (approach:Parallel.meta_stragety_t list ref) = ref []
let (timeout : float option ref) = ref None
let (system : ConcretGraphRewritingSystems.named_grs option ref) = ref None
let (system_current : ConcretGraphRewritingSystems.named_grs option ref) = ref None
let (ran:bool ref) = ref false
let reset_sol_file = ref true
(* Function to handle user commands *)
let undefined_command_msg cmd = 
   (Printf.sprintf "Undefined command [%s].\n" cmd)
let help_msg () = (Printf.sprintf "Type 'help' for help.")

let cmd_select_processing n cmd = 
  try 
    let res = `System (n|> int_of_string) in
    reset_sol_file := true; res
  with _ -> `Undefined (undefined_command_msg cmd)


let cmd_reset_strategies () = 
  approach := [];
  Printf.printf "Strategies reset.\n"
  let cmd_recap () = 
    Printf.printf "Original System: %s\nRules remained: %s\nLog:%s\nInvolved Strategies:%s\nStrategies: %s\nTerminating: %s\nReset_solution_file_next_run: %b\nResolution Time: %f\n" 
    (* original system *)
    (match !system with
    | None -> "None" 
    | Some grs -> grs.name) 
    (* remaind rules *)
    (match !system, !system_current with
    |Some grs, Some grs_current -> 
      (List.mapi 
      (fun i r ->
        if List.mem r grs_current.grs then i else -1
      )
      grs.grs)
      |> List.filter (fun x -> x >= 0)
      |> List.map Int.to_string |> String.concat ";"
    |None, None -> "[]"
    |_ -> failwith __LOC__)
    (* log *)
    (match !system with
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
    |> Printf.sprintf "\n%s")
    (* involed strategies *)
    (List.map (fun (_, _, semiring, integer) ->
      match semiring with
      |Semiring.Arctic -> if integer then "a" else "A"
      |Semiring.Tropical ->if integer then "t" else "T"
      |Semiring.Arithmetic -> if integer then "n" else "N"
    )
    !log 
    |> StringSet.of_list
    |> StringSet.elements
    |> String.concat "")
    (* Strategies *)
    (List.map Parallel.meta_stragety_to_str !approach
    |> String.concat " || "
    |> Printf.sprintf "[%s]")
    (* termination *)
    (match !system_current with
     | None -> "unknown"
     | Some grs -> if List.length grs.grs = 0 then "yes" else
      "unknown")
    (* reset solution file *)
    !reset_sol_file
    (* resolution time *)
    !time 
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
    cmd_recap ()
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
  system := Some (List.nth systems n);
  system_current := Some (List.nth systems n);
  Printf.printf "System %d.%s selected.\n" n (List.nth systems n).name
  ;time := 0.;
  log := []
let cmd_systems () = 
  let sys_names = List.mapi (fun i (s:ConcretGraphRewritingSystems.named_grs) -> Printf.sprintf "%d.%s" i s.name) systems in
    let s = String.concat "\n" sys_names in
    print_endline s
let cmd_show_ruler_graphs () =
  List.iteri 
    (fun i ((rulergraph:Ruler_graph.rulerGraph), name,description) ->
      Printf.sprintf "ruler graph %d : \ngraph: %s\n forbidden context: %s\nname: %s\ndescription: %s\n\n"
      i 
      (MGraph.toStr (rulergraph.x))
      (MGraph.toStr (rulergraph.fx |> Option.get|>GraphHomomorphism.codom))
      name
      description 
      |> print_endline
    ) 
    Ruler_graph.ruler_graphs
let cmd_try_typegraph_processing system auto_defaut_strategies timeout =
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
    `try_typegraph (system,strategies,timeout) (* auto_defaut_strategies is a word from {a,n,t,A,N,T}*, ex: ant,ANt,Ta *)
  with _ -> failwith __LOC__
let cmd_showme () = 
  match !ran with
  | true -> Sys.command "cat tmp/sol.sol" |> ignore
  | false ->
    print_endline "try some methods before.\n"
  
let cmd_try_typegraph system auto_defaut_strategies time =
  cmd_select_system system;
  cmd_timeout time;
  cmd_reset_strategies ();
  List.iter cmd_add_strategy auto_defaut_strategies;
  cmd_run ();
  cmd_showme ();
;;

let cmd_try_subgraph_counting_no_forbidden_context system =
  (* todo : unify two systems *)
  let system = List.nth systems system in
  let pb = ConcretGraphRewritingSystems.named_grs_to_problem system in
  let res = Termination.isTerminating pb in
  let _ = Termination.interpret res in
  ()
;;

let cmd_try_subgraph_counting_one_forbidden_context (system,rulergraph) =
  (* todo : unify two systems *)
  let system = List.nth systems system in
  let (rulergraph,_,description) = List.nth Ruler_graph.ruler_graphs rulergraph in
  match Subgraph_counting_forbidden_contexts.terminating_counting_subgraph_with_forbidden_context rulergraph system with
  | true, report -> Printf.sprintf "  *** Termination proved ! *** \n %s\ndescription of the ruler-graph: %s" report description |> print_endline
  | false, report -> Printf.sprintf "  *** Termination Unknown ! *** \n %s\n" report |> print_endline
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
  | ["reset_strategies"] -> `Reset_strategies 
  | ["showme"] -> `show_certificat
  | ["run"] -> `run
  | "try_type_graph" :: system :: timeout :: auto_defaut_strategies -> cmd_try_typegraph_processing system auto_defaut_strategies timeout
  | "try_subgraph_counting_no_forbidden_context" :: system :: []-> `try_subgraph_counting_no_forbidden_context (int_of_string system)
  | "try_subgraph_counting_one_forbidden_context" :: system :: [rg]-> `try_subgraph_counting_one_forbidden_context (int_of_string system, int_of_string rg)
  | ["recap"] -> `recap 
  | ["help"] ->
    `Print_help_msg 
    "GRAPH REWRITING SYSTEM TERMINATION PROVER (REPL)
───────────────────────────────────────────────────

CORE COMMANDS
  systems               - List all available graph rewriting systems
  select <N>            - Select system by ID (e.g., `select 0`)
  run                   - Execute added strategies on the selected system
  recap                 - Show system status, rules left, and strategies used
  reset_strategies      - Clear all selected strategies
  timeout <SECONDS>     - Set max execution time (e.g., `timeout 60`)
  showme                - Display the latest termination certificate
  exit                  - Quit the REPL

STRATEGY COMMANDS
Add automated strategies for proving termination:

1. Predefined Strategies (Shortcuts):
   add_parallel_strategy_auto:<NAME>
   ────────────────────────────────────────
   Auto_total                 - Fully automatic strategy
   Auto_total_int             - Integer coefficients (auto semiring)
   Auto_total_int_arctic      - Integer + Arctic semiring
   Auto_total_int_tropical    - Integer + Tropical semiring
   Auto_total_int_arithmetic  - Integer + Arithmetic semiring
   Auto_total_real            - Real coefficients (auto semiring)
   Auto_total_real_arctic     - Real + Arctic semiring
   Auto_total_real_tropical   - Real + Tropical semiring
   Auto_total_real_arithmetic - Real + Arithmetic semiring

   Example:
   >> add_parallel_strategy_auto:Auto_total_int_arctic

2. Custom Strategies (Advanced):
   add_parallel_strategy_auto <TYPE> <SEMIRING> <MAX_SIZE> <MAX_WEIGHT> <OPTIMIZED>
   ────────────────────────────────────────────────────────────────────────────────
   <TYPE>       : int (discrete) | float (real numbers)
   <SEMIRING>   : arctic | tropical | arithmetic
   <MAX_SIZE>   : Max graph size to analyze (e.g., 10)
   <MAX_WEIGHT> : Max weight allowed (e.g., 100)
   <OPTIMIZED>  : true/false (enable optimizations)

   Example:
   >> add_parallel_strategy_auto int arctic 10 100 true

QUICK-TEST COMMANDS
  try_type_graph <SYS_ID> <STRATS> <TIMEOUT>  
   - Test type graph method with semiring combo (e.g., `try_type_graph 2 ant 60`)
   - <STRATS>: Letter combo (a=Real Arctic, A=Int Arctic, t/T= Tropical, n/N=Arithmetic)

  try_subgraph_counting_no_forbidden_context <SYS_ID>  
   - Test subgraph counting method (e.g., `try_subgraph_counting_no_forbidden_context 0`)

EXAMPLES
  1. Prove termination for system 0 with Arctic int:
     >> select 0
     >> add_parallel_strategy_auto:Auto_total_int_arctic
     >> timeout 30
     >> run

  2. Try multiple semirings quickly:
     >> try_type_graph 3 120 A N T  # Arctic(int) + Tropical(int) + Arithmetic(int)
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
      | `show_certificat -> cmd_showme ()
      | `run -> cmd_run ()
      |`try_typegraph (system,auto_defaut_strategies,timeout) -> 
        cmd_try_typegraph system auto_defaut_strategies timeout
      | `Print_help_msg msg -> print_endline msg;
      | `Undefined msg -> print_endline msg;
      | `Reset_strategies -> cmd_reset_strategies ()
      | `timeout f -> cmd_timeout f
      | `Method app ->
        cmd_add_strategy app
      | `recap -> cmd_recap ()
      | `try_subgraph_counting_no_forbidden_context system -> cmd_try_subgraph_counting_no_forbidden_context system
      | `try_subgraph_counting_one_forbidden_context args -> cmd_try_subgraph_counting_one_forbidden_context args
      
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