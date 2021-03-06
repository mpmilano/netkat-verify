open NetKAT_Verify_Reachability
open NetKAT_Verify_Equivalence
open NetKAT_Types
open NetKAT_Util

type parseType = 
  | NetKAT
  | GML
  | Dot
      
type mode = 
  | Equiv
  | Reach
  | Pushbutton_Reach

let parseType = ref NetKAT
let mode = ref Reach
let parse_things = ref []
let run_name = ref []
  
let usage = "usage: verify [-f NetKAT|GML|Dot] [-m equiv|reach] [-p ] run-name [inp pol outp] [prog1 prog2]"

  
(* from http://rosettacode.org/wiki/Command-line_arguments#OCaml *)
let speclist = 
  let pushbutton () = mode := Pushbutton_Reach in
  [
  ("-f", Arg.String (fun s -> 
    parseType := match s with 
    | "NetKAT" -> NetKAT 
    | "GML" -> GML 
	| "Dot" -> Dot
    | _ -> failwith (Printf.sprintf "not supported: %s" s)
					),      ": format to expect for parsing ");
   ("-m", Arg.String    (fun s -> 
	 if (!mode) = Pushbutton_Reach then () else
     mode := match s with
     | "equiv" -> Equiv
     | "equivalence" -> Equiv
     | "reach" -> Reach
     | "reachability" -> Reach
     | _ -> failwith (Printf.sprintf "not supported: %s" s)
						),      ": algorithm to run");
   ("-p", Arg.Unit pushbutton, "enable push-button mode")
]

let read_file (fname : string) : string = 
  let lines = ref [] in
  let chan = open_in fname in 
  try 
	while true; do
	  lines := input_line chan :: 
		!lines
	done; ""
  with End_of_file -> 
	close_in chan;
	(intercalate (fun x -> x) "\n" (List.rev !lines))

let parse_program_from_file str = 
  let from_topo topo = 
	let pol = PolicyGenerator.all_pairs_shortest_paths topo in
	pol in
  match (!parseType) with 
  | NetKAT -> NetKAT_Parser.program NetKAT_Lexer.token (Lexing.from_string (read_file str))
  | GML -> from_topo (Topology.from_gmlfile str)
  | Dot -> from_topo (Topology.from_dotfile str)

let parse_predicate str = match NetKAT_Parser.program NetKAT_Lexer.token 
    (Lexing.from_string (Printf.sprintf "(filter %s)" str)) with
  | Filter (pred) -> pred
  | _ -> failwith "huh, parsing must have failed"

let parse_reach_args argl = 
  match argl with
    | [outp;pol_file;inp] -> 
		parse_predicate inp, parse_program_from_file pol_file, parse_predicate outp
    | _ -> failwith (Printf.sprintf "incorrect arguments to reachability.\n%s" usage)


let _ =
  Arg.parse 
    speclist
    (fun x -> 
      match (!run_name) with
	| [] -> run_name := [x]
	| _ -> parse_things := x::(!parse_things))
    usage; match (!mode),(!parse_things) with 
      | Equiv,[hd;tl] -> ()
      | Reach, [hd;mid;tl] -> ()
	  | Pushbutton_Reach, [pol] -> ()
      | _ -> failwith (Printf.sprintf "incorrect number of arguments supplied for selected run type:\n%s" usage)

let _ = match (!mode) with
  | Equiv -> 
    failwith "equivalence feature retired, check back later"
  | Reach -> 
    let (inp,prog,outp) = parse_reach_args (!parse_things) in
    Printf.printf "Input: %s\nOutput: %s\n" (NetKAT_Pretty.string_of_pred inp) (NetKAT_Pretty.string_of_pred outp);
    if fst(check_reachability (List.hd (!run_name)) inp prog outp (Some true))
    then Printf.printf "Sat: path found.\n"
    else Printf.printf "Unsat: path impossible.\n"
  | Pushbutton_Reach ->
	  let prog = List.hd (List.map parse_program_from_file (!parse_things)) in
	  if check_reachability_pushbutton (List.hd (!run_name)) prog 
	  then Printf.printf "sat\n" 
	  else Printf.printf "unsat\n"
