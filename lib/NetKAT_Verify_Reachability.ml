open Packet
open NetKAT_Types
open NetKAT_Util
open Unix
open NetKAT_Sat

  
module Verify = struct
  module Stateless = struct
    open Sat_Syntax
    open Sat_Utils
      
      
    module Support_Code = struct
      let packet_a = "packet_a"
      let packet_b = "packet_b"
      let inhist = "inhist"
      let midhist = "midhist"
      let outhist = "outhist"
      let is_hist n x  = TApp (TVar (Printf.sprintf "is-hist-%u" n), [x])
      let hist_packet n m x = 
		TApp (TVar (Printf.sprintf "hist-%u-packet-%u" n m), [x])
      let hist_one x = TApp (TVar "hist-one", [x])
      let hist_cons hd tl = TApp (TVar "hist-cons", [hd; tl])
      let hist_head h = TApp (TVar "hist-head", [h])
      let tail_equal a b = TApp (TVar "tail-equal", [a;b])
      let hist_construct n l = TApp (TVar (Printf.sprintf "hist-%u" n), l)
      let pred_test hdr pkt v = ZEquals (encode_header hdr pkt, v)
      let pred_test_not hdr pkt v = ZNotEquals (encode_header hdr pkt, v)
      let encode_packet_equals h1 h2 f = 
		TApp (TVar 
				(Printf.sprintf "packet_equals_except_%s" 
				   (serialize_header f)), 
			  [h1;h2])
      let mod_fun f inh outh v = 
		TApp (TVar (Printf.sprintf "mod_%s" (serialize_header f)), 
			  [inh; outh; v])
      let qrule = "q"
      let declarations = [
	ZDeclareVar(inhist,SHistory);
	ZDeclareVar(midhist,SHistory);
	ZDeclareVar(outhist,SHistory);
	ZDeclareVar(packet_a,SPacket);
	ZDeclareVar(packet_b,SPacket);
	ZDeclareVar(qrule, SRelation([SHistory; SHistory]))]
      let reachability_query = ZDeclareQuery("q",[TVar inhist; TVar outhist])
    end
    open Support_Code

    let rec forwards_pred (prd : pred) (pkt : zTerm) : zFormula = 
      let forwards_pred pr : zFormula = forwards_pred pr pkt in
      let rec in_a_neg pred : zFormula = 
	match pred with
	  | Neg p -> forwards_pred p
	  | False -> ZTrue
	  | True -> ZFalse
	  | Test (hdr, v) -> pred_test_not hdr pkt (encode_vint v hdr) 
	  | And (pred1, pred2) -> ZOr [in_a_neg pred1; in_a_neg pred1]
	  | Or (pred1, pred2) -> ZAnd [in_a_neg pred1; in_a_neg pred2] in
      match prd with
	| False -> 
	  ZFalse
	| True -> 
	  ZTrue
	| Test (hdr, v) -> pred_test hdr pkt (encode_vint v hdr)
	| Neg p -> in_a_neg p
	| And (pred1, pred2) -> 
	  (ZAnd [forwards_pred pred1; 
		 forwards_pred pred2])
	| Or (pred1, pred2) -> 
	  (ZOr [forwards_pred pred1;
		forwards_pred pred2])	    

	  
    let zterm x = ZEquals(x, TVar "true")

	let int_list = 
	  let hash = Hashtbl.create 0 in
	  let rec int_list curr tot = 
	    try Hashtbl.find hash (curr,tot) 
	    with Not_found -> 
	      if curr > tot then
		[]
	      else
		curr::(int_list (curr+1) tot) in
	  int_list 1 

	let declare_packet fields = 
	  let constrs : constr_t list = 
	    (List.map
	       (fun hdr -> serialize_header hdr, header_to_zsort hdr)
	       fields) in
	  let variant : variant_t = ("packet",constrs) in
	  let variants :  variant_t list  = [variant] in
	  ZDeclareDatatype ("Packet", variants) 

	let declare_hist k = 
	  let constrs x : constr_t list = 
	    (List.map 
		   (fun y -> Printf.sprintf "hist-%d-packet-%d" x y, SPacket ) 
		   (int_list x)) in
	  let variants : variant_t list = 
	    (List.map 
		   (fun x -> Printf.sprintf "hist-%d" x, constrs x) 
		   (int_list k)) in
	  ZDeclareDatatype
	    ("Hist", variants) 

	let hist_cons_hlpr new_size old_size pkt hist : zFormula = 
	  let int_list = if new_size = old_size then 
	      (List.map (fun x -> x + 1) (int_list (new_size - 1)))
	    else 
	      (int_list (new_size - 1)) in
	  zterm (hist_construct new_size 
		   ((List.map (fun x -> hist_packet old_size x hist) int_list ) @
		       [pkt])) 
	
	let hist_head_def k = 
	  let x = "x" in 
	  let x_t = TVar x in
	  ZDefineVar ("hist-head", SMacro ([x,SHistory], SPacket), 
				  List.fold_left (fun acc n -> 
					ZIf (zterm (is_hist n x_t),
					     zterm (hist_packet n 1 x_t), acc))
					(zterm (hist_packet k 1 x_t))
					(int_list (k-1))) 

	let hist_cons_def k = 
	  let x = "x" in
	  let x_t = TVar x in
	  let p = "p" in 
	  let p_t = TVar p in
	  ZDefineVar ("hist-cons", SMacro([p, SPacket; x, SHistory], SHistory),
				  List.fold_left (fun acc n -> 
					ZIf (zterm (is_hist n x_t),
					     (hist_cons_hlpr (n + 1) n p_t x_t),
					     acc))
					(hist_cons_hlpr k k p_t x_t )
					(int_list (k-1))) 

	let tail_equal_def k = 
	  let x = "x" in
	  let x_t = TVar x in
	  let y = "y" in 
	  let y_t = TVar y in
	  ZDefineVar ("tail-equal", SMacro ([x, SHistory; y, SHistory], SBool),
		      List.fold_left (fun acc n -> 
			let fields_equal = 
			  (if n = 1 
			   then [ZFalse]
			   else (List.map 
					   (fun y -> 
						 ZEquals(hist_packet n y x_t, hist_packet n y y_t))
				   (List.map (fun x -> x + 1) (int_list (n - 1))))) in
			ZIf (zterm (is_hist n x_t),
			     ZIf (zterm (is_hist n y_t),
				  ZAnd fields_equal,
				  ZFalse),
			       acc))
			ZFalse
			(int_list k)) 

	let packet_equals_except_funs_def fields : zDeclare list = 
	  List.map (fun except -> 
	    ZDefineVar (Printf.sprintf "packet_equals_except_%s" 
					  (serialize_header except), 
			SMacro(["x", SPacket; "y", SPacket],SBool), 
			ZAnd (List.fold_left 
				(fun acc hd -> 
				  if  hd = except then 
				  acc 
				else
				    ZEquals ( (encode_header hd (TVar "x")), 
							  ( encode_header hd (TVar "y")))::acc)
				[] fields))) fields

	let mod_fun_def = (fun f -> 
	      let packet_equals_fun = 
			encode_packet_equals (TVar "x") (TVar "y") f in
	      ZDefineVar ("mod_" ^ (serialize_header f), 
					  SMacro([("x", SPacket); 
							  ("y", SPacket); 
							  ("v", (header_to_zsort f) )], 
							 SBool),
			  (
			    ZAnd [zterm packet_equals_fun;
				  ZEquals( (encode_header f (TVar "y")),  (TVar "v"))])))

	let mod_funs_def fields = List.map mod_fun_def fields

      
  end
	
  module Stateful = functor (Sat : Sat_description) -> struct
	  
      open SDN_Types
      open NetKAT_Types
      open Sat_Syntax
      open Sat_Utils
      open Stateless
		
      let all_used_fields = List.filter 
		(fun x -> (Sat.bitvec_size (header_to_zsort x)) > 0) all_fields
		
	  module SAT_Version =  struct
		module Support_Code = struct
		  open Sat
			
		  let declare_datatypes k : (zDeclare list) = 
			let open Stateless.Support_Code in
				[declare_packet all_used_fields]@
				  (packet_equals_except_funs_def all_used_fields)@
				  (mod_funs_def all_used_fields)
				
		end
		  
		let rec forwards_pol (pkt : zVar) pol pkt_out : zFormula * (zDeclare list) = 
		  let open Stateless.Support_Code in
			  match pol with
				| Filter pred -> 
				  ZAnd[forwards_pred pred (TVar pkt);
					   ZEquals(TVar pkt,TVar pkt_out)],[]
				| Mod (f,v) -> 
				  zterm 
					(mod_fun f (TVar pkt) (TVar pkt_out) (encode_vint v f)),[]
				| Par (pol1, pol2) -> 
				  let form1,decl1 = forwards_pol pkt pol1 pkt_out in
				  let form2,decl2 = forwards_pol pkt pol2 pkt_out in
				  ZOr[form1;form2],List.flatten[decl1;decl2]
				| Seq (pol1, pol2) -> 
				  let pkt_mid,decl_mid_pkt = Sat.fresh SPacket in
				  let form_in,decl_in = forwards_pol pkt pol1 pkt_mid in
				  let form_mid,decl_mid = forwards_pol pkt_mid pol2 pkt_out in
				  ZAnd[form_in;form_mid],List.flatten [decl_in;decl_mid;[decl_mid_pkt]]
				| Link (sw1, pt1, sw2, pt2) -> 
				  failwith "network is not in (p;t)* form"
				| Star _ -> failwith "star unrolling should happen earlier"
				| Choice _ -> failwith "we don't handle choice"
	  (*note: we could just treat choice like par, since we're doing
		reachability anyway *) 
				  
		let rec forwards_topo pkt pol pkt_out : zFormula * (zDeclare list) = 
		  match pol with 
			| Link (sw1, pt1, sw2, pt2) -> 
			  forwards_pol pkt 
				(Seq(Filter (Test (Switch,sw1)), 
					 Seq (Filter (Test (Header InPort,pt1)),
						  Seq (Mod(Switch,sw2),
							   Mod (Header InPort, pt2)))))
				pkt_out
			| _ -> failwith "network not in (p;t)* form"
			  
	(* maybe return all histories for which this was valid?
	   that would be a set of lists, which sounds alltogether
	   too exciting for me.  but whatever, it might be correct
	   behavior.
	*)

		let rec forwards_k k (inpt : zVar) pol topo (outp : zVar) : 
			zFormula * (zDeclare list) * (zVar list) =
		  match k with
			| 0 -> ZEquals(TVar inpt, TVar outp), [], [inpt]
			| _ -> 
			  let this_inpkt,inpkt_decl = Sat.fresh SPacket in
			  let midpkt,midpkt_decl = Sat.fresh SPacket in
			  let pol_form,pol_decl = forwards_pol this_inpkt pol midpkt in
			  let topo_form,topo_decl = forwards_topo midpkt topo outp in
			  let rest_form,rest_decl,outset = 
				forwards_k (k-1) inpt pol topo this_inpkt in
			  ZAnd[rest_form; topo_form; pol_form],
			  List.flatten [[inpkt_decl];[midpkt_decl];pol_decl;topo_decl;rest_decl],
			  (outp::outset)

		module History_Set = 
		  Set.Make( struct
			let compare = Pervasives.compare
			type t = zFormula * (zDeclare list) * (zVar list)
		  end)

		let rec forwards_star k inpt pol topo outp : 
			History_Set.t =
		  match k with 
			| 0 -> let h = forwards_k 0 inpt pol topo outp in
				   History_Set.singleton (h)
			| _ -> let h = forwards_k k inpt pol topo outp in
				   History_Set.union 
					 (forwards_star (k-1) inpt pol topo outp)
					 (History_Set.singleton (h))

					 
		let parallel_map (f : 'a -> 'b) iter : ('b list) = 
		  failwith "not implemented"

		let rec run_sat_reachability k inpt pt outp = 
		  let pol,topo = match pt with
			| Star (Seq (p,t)) -> p,t
			| _ -> failwith "error: network not in form (p;t)*" in
		  let history_sets = 
			let rec build_hists k = 
			  match k with 
				| 0 -> [forwards_k 0 inpt pol topo outp]
				| _ -> (forwards_k k inpt pol topo outp)::(build_hists (k-1))in
			build_hists k in
		  parallel_map 
			(fun x ->
			  let formu,decl,hist = x in
			  let res,exec_time = 
				Sat.solve (Sat.assemble_program 
							 ((Support_Code.declare_datatypes k) @ decl) 
							 (ZProgram [ZDeclareAssert(formu)])
							 (ZDeclareLiteral "(check-sat)")) in
			  res,hist
			)
			(fun f -> List.iter f history_sets)
			
		  
	  end

	  module Datalog_Version = struct
		  
		module Support_Code = struct
		  open Sat
			
		  let declare_datatypes k : (zDeclare list) = 
			let open Stateless.Support_Code in
				[declare_packet all_used_fields; 
				 declare_hist k; 
				 hist_head_def k; 
				 hist_cons_def k; 
				 tail_equal_def k]@
				  (packet_equals_except_funs_def all_used_fields)@
				  (mod_funs_def all_used_fields)
				
		end
		let define_relation, get_rules, get_decls = 
		  let open Sat in
		  let open Stateless.Support_Code in
		  let hashtbl = Hashtbl.create 0 in
		  let fresh_relations = ref [] in
		  (*convenience names *)
		  let inhist_t = TVar inhist in
		  let outhist_t = TVar outhist in
		  let midhist_t = TVar midhist in
		  let default_params = [inhist; outhist] in
		  
		  let rec define_relation pol = 
			try 
			  fst (Hashtbl.find hashtbl pol)
			with Not_found -> 
			  let sym,decl = fresh (SRelation [SHistory; SHistory]) in
			  fresh_relations := decl::(!fresh_relations);
			  let make_rule body = 
				ZDeclareRule (sym, default_params, body) in
			  let apply_pol pol inh outh = 
				TApp (TVar (define_relation pol), [inh; outh]) in
			  let rules = 
				ZToplevelComment (NetKAT_Pretty.string_of_policy pol)::
				  (match pol with 
					| Filter pred -> 
					  [ZToplevelComment("this is a filter");
					   make_rule (ZAnd 
									[forwards_pred pred (hist_head inhist_t);
									 ZEquals(inhist_t, outhist_t)])]
					| Mod(f,v) -> 
					  let modfn = mod_fun f in
					  [ZToplevelComment("this is a mod");
					   make_rule (ZAnd[ 
						 zterm (modfn (hist_head inhist_t) 
								  (hist_head outhist_t) 
								  (encode_vint v f));
						 zterm (tail_equal inhist_t outhist_t)])]
					| Par (pol1, pol2) -> 
					  let pol1_sym = apply_pol pol1 in 
					  let pol2_sym = apply_pol pol2 in 
 					  [ZToplevelComment("this is a par");
					   make_rule (zterm (pol1_sym inhist_t outhist_t));
					   make_rule (zterm (pol2_sym inhist_t outhist_t))]
					| Seq (pol1, pol2) -> 
					  let pol1_sym = apply_pol pol1 in 
					  let pol2_sym = apply_pol pol2 in 
 					  [ZToplevelComment("this is a seq");
					   make_rule 
						 (ZAnd[ zterm (pol1_sym inhist_t midhist_t); 
								zterm (pol2_sym midhist_t outhist_t)])]
					| Star pol1  -> 
					  let pol1_sym = apply_pol pol1 in 
					  let this_sym inh outh = TApp (TVar sym, [inh; outh]) in
					  [ZToplevelComment("this is a star");
					   make_rule 
						 (ZEquals(inhist_t, outhist_t));
					   make_rule 
						 (ZAnd[ zterm (pol1_sym inhist_t midhist_t);
								zterm (this_sym midhist_t outhist_t)])]
					| Choice _ -> 
					  failwith "I'm not rightly sure what a \"choice\" is "
					| Link (sw1, pt1, sw2, pt2) ->
					  let modsw = mod_fun Switch in
					  let modpt = mod_fun (Header SDN_Types.InPort) in
					  let packet_a_t = TVar packet_a in
					  let packet_b_t = TVar packet_b in
					  [ZToplevelComment("this is a link");
					   make_rule 
						 (ZAnd[
						   forwards_pred 
							 (Test (Switch, sw1)) 
							 (hist_head inhist_t);
						   forwards_pred 
							 (Test ((Header SDN_Types.InPort), pt1))
							 (hist_head inhist_t);
						   zterm (modsw (hist_head inhist_t) packet_a_t 
									(encode_vint sw2 Switch));
						   zterm (modpt packet_a_t packet_b_t 
									(encode_vint pt2 
									   (Header SDN_Types.InPort)));
						   ZEquals
							 (hist_cons packet_b_t inhist_t, outhist_t)])]
				  ) in
			  Hashtbl.add hashtbl pol (sym,rules); sym in
		  let get_rules () = Hashtbl.fold 
			(fun _ rules a -> snd(rules)@a ) hashtbl [] in
		  let get_decls () = (!fresh_relations) in
		  define_relation, get_rules, get_decls
			
	  end

  end  
	
end
   

(* str: name of your test (unique ID)
inp: initial packet
   pol: policy to test
outp: fully-transformed packet
oko: bool option. has to be Some. True if you think it should be satisfiable.
*)


let collect_constants inp pol outp = 
  (Sat_Utils.collect_constants (Seq (Seq (Filter inp,pol),Filter outp)))
	
let check_reachability_ints ints str inp pol outp oko =
  let module Sat = Z3Sat(struct let ints = ints end) in
  let open Verify.Stateless in
  let open Verify.Stateless.Support_Code in
  let module Stateful = Verify.Stateful(Sat) in
  let open Stateful.Datalog_Version in
  let open Sat_Syntax in
  let x = inhist in
  let x_t = TVar x in
  let y = outhist in
  let y_t = TVar y in
  let entry_sym = define_relation pol in
  let last_rule = ZDeclareRule (qrule, [x;y],
				    ZAnd[forwards_pred inp (hist_head x_t);
					     forwards_pred outp (hist_head y_t);
					     zterm (TApp (TVar entry_sym, [TVar x; TVar y]))]) in
  let prog = ZProgram 
	( List.flatten
		[declarations;
		 get_decls();
		 ZToplevelComment("rule that puts it all together\n")::
		   last_rule::
		   ZToplevelComment("syntactically-generated rules\n")::
		   (get_rules())] ) in
  let query = reachability_query in
  let assembled_program = Sat.assemble_program 
	(Support_Code.declare_datatypes 5) prog query in
  let serialize = Sat.serialize_program in
  let solve = Sat.solve in
  Sat_Utils.run_solve oko serialize solve assembled_program str

let check_reachability str inp pol outp = 
  check_reachability_ints 
	(collect_constants inp pol outp)
	str inp pol outp

let check = check_reachability


let check_reachability_pushbutton str pol = 
  let open NetKAT_Sat.Sat_Syntax in
  let ints = Sat_Utils.collect_constants pol in
  let inp = Test (Switch, (List.hd (List.rev (ints SSwitch)))) in
  let outp = Test (Switch, (List.hd (ints SSwitch))) in
  Printf.printf "Input: %s\nOutput: %s\n" 
	(NetKAT_Pretty.string_of_pred inp) 
	(NetKAT_Pretty.string_of_pred outp);
  let res,tm = 
    check_reachability_ints ints str inp pol outp (Some true) in
  let times = Unix.times() in
  let ocaml_utime = times.tms_utime in
  let ocaml_stime = times.tms_stime in
  Printf.printf 
	"Z3 execution time: %f\n
	Ocaml user execution time: %f\n
	Ocaml system execution time: %f\n"
	tm ocaml_utime ocaml_stime;
  res
