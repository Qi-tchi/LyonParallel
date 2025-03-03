open Unix;;



  (* Function to check the status of the child process *)
  let monitor pid timeout stop_all_threads start_time (module P:TypeGraph.Parm) =
    match Unix.waitpid [WNOHANG] pid with
    | 0, _ ->
        (* Child is still running *)
        let elapsed = Unix.gettimeofday () -. start_time in
        if elapsed >= timeout || Atomic.get stop_all_threads then
          begin
            if elapsed >= timeout then
              Printf.printf "Timeout of %f seconds reached. Terminating process %d...\n%!" timeout pid
            else
              Printf.printf "Atomic condition triggered. Terminating process %d...\n%!" pid;

            (try
                Printf.printf "Sending SIGKILL to process %d.\n%!" pid;
                Unix.kill pid Sys.sigkill;  (* Force kill *)
                Printf.printf "Sent SIGKILL to process %d.\n%!" pid
              with
              | Unix_error (ESRCH, _, _) ->
                  Printf.printf "Process %d does not exist.\n%!" pid
              | Unix_error (EPERM, _, _) ->
                  Printf.eprintf "Permission denied to kill process %d.\n%!" pid
              | Unix_error (err, func, arg) ->
                  Printf.eprintf "Error sending SIGKILL: (err,func,arg)=(%s,%s,%s)\n%!" (error_message err) func arg);
          (* Wait for the process to terminate *)
            (try
              let _, status = Unix.waitpid [] pid in
              Printf.printf "Process %d terminated with status: %s\n%!"
                pid
                (match status with
                 | WEXITED code -> Printf.sprintf "Exited with code %d" code
                 | WSIGNALED signal -> Printf.sprintf "Killed by signal %d" signal
                 | WSTOPPED signal -> Printf.sprintf "Stopped by signal %d" signal);
               ignore @@ Sys.command (Printf.sprintf "echo 'uncomplete' >> tmp/%s.smt2" P.file_name) 
            with
            | Unix_error (err, func, arg) ->
                Printf.eprintf "Error waiting for process: (error_message, func, arg)=(%s\n%,%s,%s)!" (error_message err) func arg
            | _ -> assert false;)
        (*  if elapsed >= timeout 
    | child_pid, status ->
        (* Child has terminated *)
        Printf.printf "Process %d terminated with status: %s\n%!"
          child_pid
          (match status with
           | WEXITED code -> Printf.sprintf "Exited with code %d; returned pid [%d]" code child_pid
           | WSIGNALED signal -> Printf.sprintf "Killed by signal %d; returned pid [%d]" signal child_pid
           | WSTOPPED signal -> Printf.sprintf "Stopped by signal %d; returned pid [%d]" signal child_pid) *)
          end;false
      | _ -> true

  (* Monitoring loop *)
  let monitor_loop pid timeout stop_all_threads start_time (module P:TypeGraph.Parm) =
    try 
        while not (monitor pid timeout stop_all_threads start_time (module P:TypeGraph.Parm)) do
          sleepf 0.5  (* Sleep for 0.5 seconds *)
        done
    with | Unix_error (ECHILD, "waitpid", "") ->
      Printf.eprintf "No such child process: %d\n%!" pid
  | Unix_error (err, func, arg) ->
      Printf.eprintf "Unix error: %s in %s with arg %s\n%!" (error_message err) func arg
  | e ->
      Printf.eprintf "Unexpected error: %s\n%!" (Printexc.to_string e)
      
    (* Check again if the process is still running after a short delay *)
    (* match Unix.waitpid [WNOHANG] pid with
    | 0, _ ->
        let elapsed = Unix.gettimeofday () -. start_time in
        if elapsed < timeout then
        begin
          sleepf 0.5;  (* Sleep for 0.5 seconds *)
          monitor_loop pid timeout stop_all_threads start_time 
        end
    | _, _ ->
        () *)
