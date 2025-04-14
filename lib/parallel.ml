(* let stop_all_threads = Atomic.make false *)
let debug = true
let clear = true
(* open Unix *)
let tmp_dir = "tmp/"



let domain_table = Hashtbl.create 100 
let next_id = ref 0  
let get_or_assign_id domain =
  match Hashtbl.find_opt domain_table domain with
  | Some id -> id
  | None ->
      let id = !next_id in
      incr next_id;
      Hashtbl.add domain_table domain id;
      id

let domain_id_to_str () =
  let current_domain = Domain.self () in
  let id = get_or_assign_id current_domain in
  Printf.sprintf "%d" id


let run_command_with_timeout args timeout stop_all_threads 
  nb_process_spawn_for_z3 
nb_process_spawn_for_z3_tropical
nb_process_spawn_for_z3_arctic
nb_process_spawn_for_z3_arithmetic 
 (module P:TypeGraph.Parm) start_time 
 =
  let st = Unix.gettimeofday () in
  (* Use the shell to run the command 'c' *)
  let input_file = args.(0) in
  let output_file = args.(1) in
  (* Open the output file for writing *)
  let oc = open_out output_file in
  let fd_out = Unix.descr_of_out_channel oc in

(* Run z3 with the given input file. The first argument in the array after the executable name
   should be the input file. We'll redirect stdout to fd_out. *)
   let pid =
    Unix.create_process
      "z3"                               (* The program to run. Ensure it's in PATH or specify full path *)
      [| "z3"; input_file |]             (* Arguments: "z3" followed by the input file *)
      Unix.stdin                         (* Inherit standard input *)
      fd_out                             (* Redirect standard output to our opened file *)
      Unix.stderr                        (* Inherit standard error *)
  in

  (* let pid =
    create_process "z3" [
      stdin stdout stderr
  in
 *)
  if debug then begin
    Atomic.incr nb_process_spawn_for_z3;
    begin
    match P.semiring with
      | Semiring.Arctic -> Atomic.incr nb_process_spawn_for_z3_arctic 
      | Semiring.Tropical -> Atomic.incr nb_process_spawn_for_z3_tropical 
      | Semiring.Arithmetic -> Atomic.incr nb_process_spawn_for_z3_arithmetic
    end;
    Printf.printf "domain [%s] => spawned process [%d] => %s. Toal %d Tropical %d Arctic %d Arith %d .\n" (domain_id_to_str ()) pid P.file_name
    (Atomic.get nb_process_spawn_for_z3) 
    (Atomic.get nb_process_spawn_for_z3_tropical) 
    (Atomic.get nb_process_spawn_for_z3_arctic) 
    (Atomic.get nb_process_spawn_for_z3_arithmetic);
    flush Stdio.stdout;
  end; 

  My_unix.monitor_loop pid timeout stop_all_threads start_time (module P:TypeGraph.Parm); 
 
  close_out oc;
  print_string (Printf.sprintf "\n\n\n****\n\n*** time : %f \n \n\n\n****\n\n*** \n\n\n****\n\n*** " (Unix.gettimeofday () -. st));
  flush Stdio.stdout;
  (* Wait for the process to finish *)
  if debug then begin
    let _ = Atomic.fetch_and_add nb_process_spawn_for_z3 (-1) in
    match P.semiring with
    | Semiring.Arctic -> Atomic.fetch_and_add nb_process_spawn_for_z3_arctic (-1) |> ignore
    | Semiring.Tropical -> Atomic.fetch_and_add nb_process_spawn_for_z3_tropical (-1) |> ignore
    | Semiring.Arithmetic -> Atomic.fetch_and_add nb_process_spawn_for_z3_arithmetic (-1) |> ignore;
  end;;
  (* match !raison with
  | "timeout" ->
    if debug then begin
      begin 
        Atomic.decr nb_process_spawn_for_z3;
        match P.semiring with
        | Semiring.Arctic -> Atomic.decr nb_process_spawn_for_z3_arctic  
        | Semiring.Tropical -> Atomic.decr nb_process_spawn_for_z3_tropical 
        | Semiring.Arithmetic -> Atomic.decr nb_process_spawn_for_z3_arithmetic 
      end;
      Printf.printf "domain [%s] => killed process [%d] because stop_all [%b]  ||  time %f \n " (domain_id_to_str ()) pid  (Atomic.get stop_all_threads) (Unix.gettimeofday ()-. start_time);
      flush Stdio.stdout;
      sleepf 0.1;
    end
  |"stop_all" ->
    if debug then begin
      begin 
        Atomic.decr nb_process_spawn_for_z3;
        match P.semiring with
        | Semiring.Arctic -> Atomic.decr nb_process_spawn_for_z3_arctic  
        | Semiring.Tropical -> Atomic.decr nb_process_spawn_for_z3_tropical 
        | Semiring.Arithmetic -> Atomic.decr nb_process_spawn_for_z3_arithmetic 
      end;
      Printf.printf "domain [%s] => killed process [%d] because timeout %f >  %f \n " (domain_id_to_str ()) pid (Unix.gettimeofday () -. start_time) timeout;
      flush Stdio.stdout;
    end;
    |"terminated" ->  
      if debug then Printf.printf "domain [%s]: process [%d] terminated || time %f \n " (domain_id_to_str ()) pid (gettimeofday () -. start_time);
      flush Stdio.stdout;
      sleepf 0.1;
    |_ -> assert false *)
  
let stop_all_threads = Atomic.make false

let nb_process_spawn_for_z3 = Atomic.make 0
let nb_process_spawn_for_z3_tropical = Atomic.make 0
let nb_process_spawn_for_z3_arctic = Atomic.make 0
let nb_process_spawn_for_z3_arithmetic = Atomic.make 0

let (solution:(int list * string * Semiring.semiring_t * bool)
option Atomic.t) = Atomic.make None
let extract_ks_from_file filename =
  (* Read the entire content of the file *)
  let content =
    let ic = open_in filename in
    let n = in_channel_length ic in
    let s = really_input_string ic n in
    close_in ic;
    s
  in
  (* Regular expression to match "rule k: true" where k is a natural number *)
  let regexp = Str.regexp "rule \\([0-9]+\\): true" in
  (* Function to recursively find all matches *)
  let rec find_ks pos ks =
    try
      let _ = Str.search_forward regexp content pos in
      let k_str = Str.matched_group 1 content in
      let k = int_of_string k_str in
      find_ks (Str.match_end ()) (k :: ks)
    with Not_found ->
      List.rev ks  (* Return the list of k's in the order they appear *)
  in
  find_ks 0 []

let run_z3_command
(* ?(clear=false) *)
 (module P:TypeGraph.Parm) timeout start_time =  
  (* let approach = P.semiring |> Semiring.string_of_semiring_t in *)
  (* let originalWeights = not P.integer in   *)
  let inf, outf = Printf.sprintf "%s%s.smt2" tmp_dir (P. file_name), 
  Printf.sprintf "%s%s.out" tmp_dir (P.file_name) in
  run_command_with_timeout (Array.of_list [inf;outf]) timeout  
  stop_all_threads nb_process_spawn_for_z3 nb_process_spawn_for_z3_tropical nb_process_spawn_for_z3_arctic nb_process_spawn_for_z3_arithmetic
   (module P:TypeGraph.Parm) start_time; 
  (* let solution_found = 
    if timeout_flag then false 
    else TypeGraph.file_contains_unsat (Printf.sprintf "tmp/%s_%s.out" (P.file_name) approach) in 
  solution_found *)
  try 
    (* let oc = open_out_gen [Open_creat] 0o644 (Printf.sprintf "tmp/%s_%s.out" (P.file_name) approach) in close_out oc; *)
    (not @@ TypeGraph.file_contains "unsat" (Printf.sprintf "%s%s.out" tmp_dir (P.file_name))) &&
    (not @@ TypeGraph.file_contains "uncomplete" (Printf.sprintf "%s%s.out" tmp_dir (P.file_name))) &&
    (TypeGraph.file_contains "sat" (Printf.sprintf "%s%s.out" tmp_dir (P.file_name)))
  with _ -> failwith __LOC__

let interp_sol (module P:TypeGraph.Parm) = 
  (* let approach = P.semiring |> Semiring.string_of_semiring_t in *)
  let originalWeights = not P.integer in  
  let _ = Sys.command (Printf.sprintf "python3 lib/interp.py %s %s %s" 
  (if P.integer then "int" else "float") 
  (if originalWeights then "True" else "False")
  (P.file_name)
  ) in
  (* get removed rules' numbers *)

  let ks = 
    try 
      extract_ks_from_file (Printf.sprintf "%s%s.interp" tmp_dir (P.file_name) ) 
    with _ -> failwith __LOC__ 
  in
  (* clear *)
  (* let _ = Sys.command (Printf.sprintf "cat tmp/%s.interp" approach) in *)
  if clear && Sys.file_exists (Printf.sprintf "rm %s%s.out %s%s.interp" tmp_dir (P.file_name) tmp_dir (P.file_name)) then Sys.command (Printf.sprintf "rm %s%s.out %s%s.interp" tmp_dir (P.file_name) tmp_dir (P.file_name)) |>ignore else ();
  (* res *)
  if clear && Sys.file_exists (Printf.sprintf "rm %s%s.smt2"  tmp_dir (P.file_name)) then Sys.command (Printf.sprintf "rm %s%s.smt2"  tmp_dir (P.file_name)) |> ignore;
  Some (ks, (P.file_name), P.semiring, P.integer)


let write_to_sol result grs = 
  let oc = open_out_gen [Open_creat; Open_append; Open_text] 0o644 (Format.sprintf "%ssol.sol" tmp_dir) in
    let _ = 
    match result with 
    | Some (eliminatedRules,file_name_prefix, semiring, integer) ->
        begin  
          (* copie the type graph infomation in the .sol file *)
          let ic = open_in (Format.sprintf "%s%s.interp" tmp_dir file_name_prefix) in
          let s = really_input_string ic (in_channel_length ic) in
          Printf.fprintf oc "%s\n" s;
          let n = ((!grs:ConcretGraphRewritingSystems.named_grs).grs) |> List.length in
          let rls = List.init n (fun i -> i) in
          let remained_rls = List.filter (fun i -> List.mem i eliminatedRules |> not) rls in
          if remained_rls |> List.is_empty then
            begin
              Printf.fprintf oc "System {%s} is terminating by %s.\n"
              (Aux_functions.pp_int_list ";" eliminatedRules)
              (Printf.sprintf "type graph method over %s %s" 
              (if integer then "integer" else "real")  
              (Semiring.pp_semiring_t semiring))
            end else begin    
              Printf.fprintf oc "System {%s} is relatively terminating w.r.t. {%s} by %s.\n"
              (Aux_functions.pp_int_list ";" eliminatedRules) 
              (Aux_functions.pp_int_list ";" remained_rls)
              (Printf.sprintf "type graph method over %s %s" 
              (if integer then "integer" else "real")  
              (Semiring.pp_semiring_t semiring))
            end;
          close_in ic; 
          grs := {!grs with
          grs = List.filteri (fun i _ -> List.mem i remained_rls) !grs.grs;};
          (* flag := !flag *)
        end 
    | None ->
        begin
          let _ = Printf.fprintf oc "No solution found.\n" in ()
        end in
    close_out oc

(* strategy type *)
type integerOrNot = bool
type size_t = int
type maxWeight_t = int
type maxSize_t = int
type timeout_t = float
type optimizedTypegraph_t = bool
type strategy_t = 
| Strat :  Semiring.semiring_t * size_t * integerOrNot * maxWeight_t * optimizedTypegraph_t -> strategy_t
type meta_stragety_t =
| User of strategy_t
| Auto_total : meta_stragety_t
| Auto_total_int : meta_stragety_t
| Auto_total_real : meta_stragety_t
| Auto_total_int_tropical : meta_stragety_t
| Auto_total_int_arctic : meta_stragety_t
| Auto_total_int_arithmetic : meta_stragety_t
| Auto_total_real_tropical : meta_stragety_t
| Auto_total_real_arctic : meta_stragety_t
| Auto_total_real_arithmetic : meta_stragety_t
| Auto_real : Semiring.semiring_t * maxSize_t * optimizedTypegraph_t -> meta_stragety_t
| Auto_int : Semiring.semiring_t * maxSize_t * maxWeight_t * optimizedTypegraph_t -> meta_stragety_t  

let meta_stragety_to_str m =
  match m with
  |User _ -> "to do "
  |Auto_total -> "auto_total"
  |Auto_total_int -> "auto_total_int"
  |Auto_total_real -> "auto_total_real"
  | Auto_total_int_tropical -> "auto_total_int_tropical"
  | Auto_total_int_arctic -> "auto_total_int_arctic"
  | Auto_total_int_arithmetic -> "auto_total_int_arithmetic"
  | Auto_total_real_tropical -> "auto_total_real_tropical"
  | Auto_total_real_arctic -> "auto_total_real_arctic"
  | Auto_total_real_arithmetic -> "auto_total_real_arithmetic"
  |Auto_real (semiring, size, opt) -> Printf.sprintf "Auto_real(%s,%d,%b)" (Semiring.string_of_semiring_t semiring) size opt
  |Auto_int (semiring, size, w, opt) -> Printf.sprintf "Auto_int(%s,%d,%d,%b)" (Semiring.string_of_semiring_t semiring) size w opt

(* parameter for pre-defined strategies *)
let timeout_defaut = 777.0 
let opt_default = false  
let maxSizeTropicalReal_default = 4 
let maxSizeArcticReal_default = 4
let maxSizeArithmeticReal_default = 4  
let maxSizeTropicalInt_default = 4 
let maxSizeArcticInt_default = 4
let maxSizeArithmeticInt_default = 4 
let maxWeightTropicalInt_default = 3  
let maxWeightArcticInt_default = 3 
let maxWeightArithmeticInt_default = 3  

let interp_strategy_autoint_autoreal strategy =
  match strategy with
  | Auto_real(semiring,maxSize,opt) ->
      let res = ref [] in
      for size = 1 to maxSize do 
        let integer = false in
        let maxWeight = 
          match semiring with  
          |Semiring.Arithmetic -> 2
          |Semiring.Arctic -> 1|Semiring.Tropical -> 1
        in
        res := Strat(semiring,size,integer,maxWeight,opt) :: !res
      done;
  List.rev !res
  |Auto_int(semiring,maxSize, maxW, opt) -> 
    let res = ref [] in
    for size = 1 to maxSize do 
      for maxWeight = 1 to maxW do
        let integer = true in
        res := Strat(semiring,size,integer,maxWeight,opt) :: !res
      done
    done;
    List.rev  !res
  |_ -> raise (Invalid_argument "this function is used to interp autoint and autoreal strategies")

let gen_z3_interpretation grs (strategy : strategy_t) =
  match strategy with
  |Strat(semiring,size,integer,maxWeight,opt) -> 
    let module P = struct
      let grs = !grs
      let size = size 
      let integer = integer  
      let ub = maxWeight
      (* let monic_matching = monic_matching  *)
      let opt = opt 
      let semiring = semiring
      let file_name = TypeGraph.file_name semiring size ub integer
    end in
  let module _ = TypeGraph.Make (P) in  
  (module P : TypeGraph.Parm);;

  let sequentiel_solving_by_thread_with_strategies grs strategies timeout start_time =
    (* let start_time = Unix.gettimeofday () in *)
    let current_strategy_nb = ref 0 in
    let nb_strategies = List.length strategies in
    let res = ref None in (* no solution found by this thread *)
    while 
         not (Atomic.get stop_all_threads)  (* no solution found by any thread*)
      (* && Option.is_none !res  (* no solution found by this thread *)
       *)
      && !current_strategy_nb < nb_strategies  (* there is a strategy to try *)
      && (Unix.gettimeofday () -. start_time < timeout_defaut || Float.equal timeout 0.)  (* timeout respected *)
    do 
      let current_strategy = List.nth strategies !current_strategy_nb in
      let (module P) = gen_z3_interpretation grs current_strategy in
      let sol_found = run_z3_command (module P:TypeGraph.Parm) timeout start_time in
      if sol_found then res := interp_sol (module P:TypeGraph.Parm);
      match !res with     
      | None -> 
        (* try next strategy *)
        current_strategy_nb := !current_strategy_nb + 1
      | Some (ks,_,_,_) -> 
        assert (List.is_empty ks |> not);
        if not (Atomic.get stop_all_threads) then begin
          Atomic.set stop_all_threads true; 
          (* write_to_sol !res grs; *)
          Atomic.set solution !res
        end;
    done
    (* match !res with
    | None -> ()
    | Some _ -> Atomic.set stop_all_threads true;  (* all thread should steop ! *)
                Atomic.set solution !res *)

let interp_meta_strategies metas =
  let temp = List.map 
  (fun meta ->
      match meta with
      | Auto_int _ | Auto_real _ -> [interp_strategy_autoint_autoreal meta]
      | Auto_total_int ->
        List.map interp_strategy_autoint_autoreal [
          Auto_int(Semiring.Tropical,maxSizeTropicalInt_default,maxWeightTropicalInt_default,opt_default);
          Auto_int(Semiring.Arctic,maxSizeArcticInt_default,maxWeightArcticInt_default,opt_default);
          Auto_int(Semiring.Arithmetic,maxSizeArithmeticInt_default,maxWeightArithmeticInt_default,opt_default)
          ]
      | Auto_total_real -> 
        List.map interp_strategy_autoint_autoreal [
        Auto_real(Semiring.Tropical,maxSizeTropicalReal_default,opt_default);
        Auto_real(Semiring.Arctic,maxSizeArcticReal_default,opt_default);
        Auto_real(Semiring.Arithmetic,maxSizeArithmeticReal_default,opt_default);
        ]   
      | Auto_total -> 
        List.map interp_strategy_autoint_autoreal [
        Auto_real(Semiring.Tropical,maxSizeTropicalReal_default,opt_default);
        Auto_real(Semiring.Arctic,maxSizeArcticReal_default,opt_default);
        Auto_real(Semiring.Arithmetic,maxSizeArithmeticReal_default,opt_default);
        Auto_int(Semiring.Tropical,maxSizeTropicalInt_default,maxWeightTropicalInt_default,opt_default);
        Auto_int(Semiring.Arctic,maxSizeArcticInt_default,maxWeightArcticInt_default,opt_default);
        Auto_int(Semiring.Arithmetic,maxSizeArithmeticInt_default,maxWeightArithmeticInt_default,opt_default)
        ]
      | Auto_total_int_tropical -> List.map interp_strategy_autoint_autoreal [Auto_int(Semiring.Tropical,maxSizeTropicalInt_default,maxWeightTropicalInt_default,opt_default)]
      | Auto_total_int_arctic -> List.map interp_strategy_autoint_autoreal [Auto_int(Semiring.Arctic,maxSizeArcticInt_default,maxWeightArcticInt_default,opt_default)]
      | Auto_total_int_arithmetic -> List.map interp_strategy_autoint_autoreal [ Auto_int(Semiring.Arithmetic,maxSizeArithmeticInt_default,maxWeightArithmeticInt_default,opt_default)]
      | Auto_total_real_tropical ->  List.map interp_strategy_autoint_autoreal [Auto_real(Semiring.Tropical,maxSizeTropicalReal_default,opt_default)]
      | Auto_total_real_arctic ->  List.map interp_strategy_autoint_autoreal [Auto_real(Semiring.Arctic,maxSizeArcticReal_default,opt_default)]
      | Auto_total_real_arithmetic ->  List.map interp_strategy_autoint_autoreal [Auto_real(Semiring.Arithmetic,maxSizeArithmeticReal_default,opt_default)]
      | User s -> [[s]]   
  ) metas in
  temp |> List.flatten




(* let get_or_assign_id domain_table next_id domain =
  match Hashtbl.find_opt domain_table domain with
  | Some id -> id
  | None ->
      let id = !next_id in
      incr next_id;
      Hashtbl.add domain_table domain id;
      id

let domain_id_to_str domain_table next_id () =
  let current_domain = Domain.self () in
  let id = get_or_assign_id domain_table next_id current_domain in
  Printf.sprintf "%d" id *)

let remove_files_from_dir dir sol_include = 
  if Sys.file_exists dir |> not then
    begin
      if debug then Format.printf "tmp directory does not exist\n";
      Sys.mkdir tmp_dir 0o777;
      if debug then Format.printf "tmp directory created\n";
      flush Stdio.stdout;
    end;
  if debug then Format.printf "tmp directory exists \n";
  let cmd = Printf.sprintf "find %s -maxdepth 1 -type f %s -exec rm {} +" tmp_dir (if sol_include |> not then "! -name 'sol.sol'" else "") in
  Sys.command cmd

let parallel_solving_with_meta_strategy ~grs ~metas ~timeout ~reset_sol_file = 
  let start_time = Unix.gettimeofday () in
  (* let domain_table = Hashtbl.create 100 in
  let next_id = ref 0 in
  let domain_id_to_str = domain_id_to_str domain_table next_id in *)
  (* let nb_thread = Domain.recommended_domain_count () in *)
  let strategies_list = interp_meta_strategies metas in
  (* let nb_strategies = List.length strategies_list in *)
  (* match nb_strategies <= nb_thread with
  | false -> raise (Invalid_argument "to be optimized for nb strategies > nb of recommended domains")
  | true ->  *)
    begin
      let log = ref [] in
      let flag = ref true in
      let _ = remove_files_from_dir tmp_dir (if reset_sol_file then true else false) in (*Init*)
      let fn = (Format.sprintf "%ssol.sol" tmp_dir) in
      while 
           !flag  (* need a new round *)
        && List.is_empty ((!grs:ConcretGraphRewritingSystems.named_grs).grs) |> not (* there is some rules *)
        && not (Atomic.get stop_all_threads)  (* no solution found *)
      do
      let _ = remove_files_from_dir tmp_dir false in (*Init*)
      (* new round ; Init*)
        flag := false; (* no new round if no rule elimination *)
        let threads = 
          List.map
            (fun strategies -> Domain.spawn (fun () ->     
              Printf.printf "domain [%s] created || stop:%b  || time(%f); \n " (domain_id_to_str ())  (Atomic.get stop_all_threads) (Unix.gettimeofday () -. start_time);
              sequentiel_solving_by_thread_with_strategies grs 
              strategies timeout start_time;
              Printf.printf "domain [%s] terminated || stop:%b   || time(%f);\n " (domain_id_to_str ())  (Atomic.get stop_all_threads) (Unix.gettimeofday () -. start_time);
            ))
          strategies_list in
        (* join results *)
        List.iter (fun t -> 
          try 
            Domain.join t
          with e -> raise e) threads;
        (* let res = res |> List.filter Option.is_some in *)
        (* get result *)
        match (Atomic.get solution) with 
        | Some (eliminatedRules,file_name, semiring, integer) ->
            let oc = open_out_gen [Open_creat; Open_append; Open_text] 0o644 fn in
            begin 
              (* copie the type graph infomation in the .sol file *)
              let ic = open_in (Format.sprintf "%s%s.interp" tmp_dir file_name ) in 
              let s = really_input_string ic (in_channel_length ic) in
              Printf.fprintf oc "%s\n" s;
              close_in ic;
              let n = !grs.grs |> List.length in
              let rls = List.init n (fun i -> i) in
              let remained_rls = List.filter (fun i -> List.mem i eliminatedRules |> not) rls in
              if remained_rls |> List.is_empty then
                begin
                  (* information for users *)
                  Printf.fprintf oc "System {%s} is terminating by %s.\n"
                  (Aux_functions.pp_int_list ";" eliminatedRules)
                  (Printf.sprintf "type graph method over %s %s" 
                  (if integer then "integer" else "real")  
                  (Semiring.pp_semiring_t semiring))
                end 
              else begin    
                  (* information for users *)
                  Printf.fprintf oc "System {%s} is relatively terminating w.r.t. {%s} by %s.\n"
                  (Aux_functions.pp_int_list ";" eliminatedRules) 
                  (Aux_functions.pp_int_list ";" remained_rls)
                  (Printf.sprintf "type graph method over %s %s" 
                  (if integer then "integer" else "real")  
                  (Semiring.pp_semiring_t semiring));
                end;
              if eliminatedRules |> List.is_empty |> not then begin
                  (* log *)
                  let eliminated_rules = List.map (fun i -> List.nth !grs.grs i) eliminatedRules in
                  log := !log @ [(eliminated_rules,file_name, semiring, integer)];
                  (* update *)
                  grs := { !grs with
                    grs = List.map (fun i -> List.nth !grs.grs i) remained_rls}; (* init *) 
                  if debug then  
                    Printf.printf "\n====== %d rule(s) eliminated; %d rule(s) remaind =========\n" (List.length eliminatedRules) (List.length remained_rls);
                  if debug then  
                    Printf.printf "                stop_all [%b];  Solution =? None: %s;  flag=[%b]\n" (Atomic.get stop_all_threads) (if Option.is_none (Atomic.get solution) then "yes" else "no") !flag;
                  Atomic.set stop_all_threads false;  (* init *)
                  Atomic.set solution None (* init *);
                  flag := true;
                  if debug then 
                    Printf.printf "Initialization: stop_all [%b];  Solution =? None: %s ;  flat = [%b] \n======== new round needed : %b =======\n" (Atomic.get stop_all_threads) (if Option.is_none (Atomic.get solution) then "yes" else "no") !flag ((List.length remained_rls) = 0 |> not);
              end
            end 
            ;(* close out *)
            close_out oc;
        | None -> ()
            (* begin
              let _ = Printf.fprintf oc "No solution found.\n" in ()
            end *)
      done;
      !grs,!log
    end

     

 (* endrullis_2023 ex 6.8 Arctic real auto *) 
(* let%expect_test "test " = 
  let print_time = true in
  let st= Unix.gettimeofday () in
  let grs = ref ConcretGraphRewritingSystems.endrullis_2023_ex_6d8 in
  let monic_matching = false in 
  let opt = false in
  let timeout = 60.0 in
  let activate_methods = [
    Auto_real(Semiring.Arctic,2,opt)
    ] in
  parallel_solving_with_meta_strategy ~grs ~monic_matching ~metas:activate_methods ~timeout;
  if print_time then Printf.printf "%f" (Unix.gettimeofday () -. st);
  ;Sys.command "cat tmp/sol.sol" |> ignore
  ;[%expect {|
  y_0--node->0 : 0.0
  y_1--node->1 : 1.0/4.0
  y_0--e->0 : 0.0 *)
 
  y_0--node->0 : 0
  y_1--node->1 : 1
  y_0--e->0 : 0
 
  rules eliminated?:
  rule 0: true
 
  System {0} is terminating by type graph method over real arctic.
  ******************************
|}]  *)



(* bruggink_2015_example_5_named
    should stop in around 10s 
    integer arithmetic opt   => eliminates 1 2
  integer tropical => eliminates 3 4
*)
(* let%expect_test "test " = 
  let print_time = true in
  let _opt = false in
  let timeout = 1. in
  let grs,strategies, monic_matching = ( 
      (* grs *) 
      (* ConcretGraphRewritingSystems.plump2018_ex3_named *)
      (* ConcretGraphRewritingSystems.bruggink_2014_example_4_named_grs *)
      (* ConcretGraphRewritingSystems.bruggink_2014_example_5_named *)
      (* ConcretGraphRewritingSystems.bruggink_2014_example_1_named *)
      (* ConcretGraphRewritingSystems.bruggink_2015_example_5_named *)
      ConcretGraphRewritingSystems.bruggink_2015_example_5_named
      (* activate methods*)
      ,[ 
        Auto_int(Semiring.Tropical,2,3,_opt) ;
      (* Auto_real(Semiring.Tropical,2,_opt); *)
        (* Auto_int(Semiring.Arctic,3,3,_opt) ; *)
      (**  Auto_real(Semiring.Arctic,2,_opt,timeout);*)
      (* Auto_int(Semiring.Arithmetic,2,2,_opt) ;  *)
        Auto_real(Semiring.Arithmetic,2,_opt);
        (* Auto_total  *)
      ]
      (* monic_matching*), false 
  )
                 in
  List.iter (fun strategy ->
    let s = match strategy with
    | Auto_int(s,_,_,_) 
    | Auto_real(s,_,_) -> Semiring.string_of_semiring_t s
    | _ -> "all" in
    let st= Unix.gettimeofday () in
    let grs = ref grs in
    (* let opt = false in *)
    parallel_solving_with_meta_strategy ~grs ~monic_matching ~metas:[strategy] ~timeout;
   if print_time then Printf.printf "%s %f\n" s (Unix.gettimeofday () -. st);   
  ) strategies
  ;Sys.command "cat tmp/sol.sol" |> ignore; 
  ;[%expect {|
|}]    *)





(******
Pourquoi

+     p[36903] has been created
+      p[36903] has been created
+      p[36903] created p[36920]. Toal 1 Tropical 0 Arctic 0 Arith 1 .
+     p[36903] killed p[36920] :terminated. Toal 0 Tropical 0 Arctic 0 Arith 0 .
+     p[36903] created p[36928]. Toal 1 Tropical 0 Arctic 0 Arith 1 .
+     p[36903] killed p[36928] :terminated. Toal 0 Tropical 0 Arctic 0 Arith 0 .
+     p[36903] created p[36944]. Toal 2 Tropical 1 Arctic 0 Arith 1 .
+     p[36903] killed p[36944] :terminated. Toal 1 Tropical 1 Arctic 0 Arith 0 .
+     p[36903] created p[36952]. Toal 2 Tropical 1 Arctic 0 Arith 1 .
+     p[36903] killed p[36952] :terminated. Toal 0 Tropical 0 Arctic 0 Arith 0 .
+     p[36903] has been created
+      p[36903] has been created
+      p[36903] created p[36961]. Toal 1 Tropical 0 Arctic 0 Arith 1 .
+     p[36903] killed p[36961] :terminated. Toal 0 Tropical 0 Arctic 0 Arith 0 .
+     p[36903] created p[36978]. Toal 1 Tropical 0 Arctic 0 Arith 1 .
+     p[36903] killed p[36978] :terminated. Toal 0 Tropical 0 Arctic 0 Arith 0 .
+     p[36903] has been created
+      p[36903] has been created
+      p[36903] created p[36994]. Toal 1 Tropical 0 Arctic 0 Arith 1 .
+     p[36903] killed p[36994] :terminated. Toal 0 Tropical 0 Arctic 0 Arith 0 .
+     p[36903] created p[37003]. Toal 1 Tropical 0 Arctic 0 Arith 1 .
+     p[36903] killed p[37003] :terminated. Toal 0 Tropical 0 Arctic 0 Arith 0 .
+     p[36903] created p[37020]. Toal 1 Tropical 0 Arctic 0 Arith 1 .
+     p[36903] killed p[37020] :terminated. Toal 0 Tropical 0 Arctic 0 Arith 0 .
+     p[36903] has been created
+      p[36903] has been created
+      p[36903] created p[37036]. Toal 1 Tropical 0 Arctic 0 Arith 1 .
+     p[36903] killed p[37036] :terminated. Toal 0 Tropical 0 Arctic 0 Arith 0 .
+     p[36903] created p[37046]. Toal 1 Tropical 0 Arctic 0 Arith 1 .
+     p[36903] killed p[37046] :terminated. Toal 0 Tropical 0 Arctic 0 Arith 0 .
+     1.4080
******)