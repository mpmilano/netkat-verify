
open SDN_Types
open NetKAT_Types
open VInt
open NetKAT_Verify_Reachability
open NetKAT_Dehop_Graph
open NetKAT_Sat.Sat_Utils

let make_vint v = VInt.Int64 (Int64.of_int v)

let verify (description: string) (initial_state: pred) (program: policy) 
    (final_state: pred) (desired_outcome: bool) : bool = 
  let kat_loc = Printf.sprintf "%s%sdebug-%s.kat" 
	  (Filename.get_temp_dir_name ()) Filename.dir_sep description in
  let preamble_loc = Printf.sprintf "%s%sdebug-%s.verify" 
	  (Filename.get_temp_dir_name ()) Filename.dir_sep description in
  let oc = open_out kat_loc in
  let oc2 = open_out preamble_loc in
  Printf.fprintf oc "%s" (NetKAT_Pretty.string_of_policy program);
  Printf.fprintf oc2 "Name:%s\nInput:%s\nProgram:%s\nOutput:%s\nResult:%b\n" 
    description
    (NetKAT_Pretty.string_of_pred initial_state)
    kat_loc
    (NetKAT_Pretty.string_of_pred final_state)
    desired_outcome; close_out oc; close_out oc2;
  fst(check description initial_state program final_state (Some desired_outcome))

let verify_waypoint str inp pol outp waypt ok = check_waypoint str inp pol outp (make_vint waypt) ok	  

(* let verify_history (description: string) (initial_state: pred) (program: policy) expr (final_state: pred) (desired_outcome: bool) : bool = 
	check_with_history expr description initial_state program final_state (Some desired_outcome)

let verify_specific_k (description: string) (initial_state: pred) (program: policy) (final_state: pred) (desired_outcome: bool) k : bool = 
	check description initial_state program final_state (Some desired_outcome) *)

let make_transition (s1, p1) (s2, p2) =  (Link (make_vint s1, make_vint p1, make_vint s2, make_vint p2))

let make_nolink_transition a b = remove_links (make_transition a b)

let make_simple_topology topo : policy = Star (Seq (Filter True, topo))

let rec combine_topologies (topo : policy list) : policy = 
  match topo with
	| (hd : policy)::[] -> hd
	| (hd : policy)::tl -> Par (hd, combine_topologies tl)
	| [] -> Filter True

let make_simple_policy pol: policy  = Star (Seq (pol, Filter True))

let starify pred (topo : policy) : policy = Star (Seq (Filter pred, topo))

(*will take a policy, a topology, and add it to the kleene-star *)
let compose_topo p t p_t_star : policy = Filter True

let rec make_packet (headers_values : (header * 'a) list ) = 
  match headers_values with
	| (hdr, valu)::[] -> Test (hdr, make_vint valu)
	| (hdr, valu)::tl -> And (Test (hdr, make_vint valu), 
							  make_packet tl)
	| [] -> True

let mk_packet a b = Printf.sprintf "(mk-packet %u %u nil)" a b

let make_packet_1 switch = 
  Test (Switch, make_vint switch)

let make_switch = make_packet_1

let make_packet_2 switch port  = 
  And (Test (Switch, make_vint switch), Test (Header SDN_Types.InPort, make_vint port))

let make_packet_3 switch port ethsrc  = 
  And ((make_packet_2 switch port), Test (Header SDN_Types.EthSrc, make_vint ethsrc))

let make_packet_4 switch port ethsrc ethdst  = 
  And ((make_packet_3 switch port ethsrc), Test (Header SDN_Types.EthDst, make_vint ethdst))

let dijkstra_test topo = longest_shortest (parse_graph (make_simple_topology topo))


(*
let no_waypoint_expr waypoint_switchnum : (zVar list -> zFormula) = 
  let ret history = 
	ZNot ((fold_pred_or (Test (Switch, make_vint waypoint_switchnum))) history)
  in 
  ret
  *)
(* let equal_fields fieldname  : (zVar list -> zFormula) = 
  (Verify.equal_single_field fieldname) *)

