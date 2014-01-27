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
      let hist_packet n m x = TApp (TVar (Printf.sprintf "hist-%u-packet-%u" n m), [x])
      let hist_one x = TApp (TVar "hist-one", [x])
      let hist_cons hd tl = TApp (TVar "hist-cons", [hd; tl])
      let hist_head h = TApp (TVar "hist-head", [h])
      let tail_equal a b = TApp (TVar "tail-equal", [a;b])
      let hist_construct n l = TApp (TVar (Printf.sprintf "hist-%u" n), l)
      let pred_test hdr pkt v = ZEquals (encode_header hdr pkt, v)
      let pred_test_not hdr pkt v = ZNotEquals (encode_header hdr pkt, v)
      let encode_packet_equals h1 h2 f = TApp (TVar (Printf.sprintf "packet_equals_except_%s" (serialize_header f)), [h1;h2])
      let mod_fun f inh outh v = TApp (TVar (Printf.sprintf "mod_%s" (serialize_header f)), [inh; outh; v])
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

	let packet_equals_except_funs fields : zDeclare list = 
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

	let mod_fun = (fun f -> 
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

	let mod_funs fields = List.map mod_fun fields

      
  end
    
  module Stateful = functor (Sat : Sat_description) -> struct
    open SDN_Types
    open NetKAT_Types
    open Sat_Syntax
    open Sat_Utils
    open Stateless

    let all_used_fields = List.filter 
	  (fun x -> (Sat.bitvec_size (header_to_zsort x)) > 0) all_fields

    module Support_Code = struct
      open Sat

      let declare_datatypes k : (zDeclare list) = 
	let open Stateless.Support_Code in
	[declare_packet all_used_fields; 
	 declare_hist k; 
	 hist_head_def k; 
	 hist_cons_def k; 
	 tail_equal_def k]@
	  (packet_equals_except_funs all_used_fields)@
	  (mod_funs all_used_fields)

    end

    let define_relation, get_rules = 
      let open Sat in
      let open Stateless.Support_Code in
      let hashtbl = Hashtbl.create 0 in
    (*convenience names *)
      let inhist_t = TVar inhist in
      let outhist_t = TVar outhist in
      let midhist_t = TVar midhist in
      let default_params = [inhist; outhist] in

      let rec define_relation pol = 
	try 
	  fst (Hashtbl.find hashtbl pol)
	with Not_found -> 
	  let sym = fresh (SRelation [SHistory; SHistory]) in
	  let make_rule body = ZDeclareRule (sym, default_params, body) in
	  let apply_pol pol inh outh = TApp (TVar (define_relation pol), 
										 [inh; outh]) in
	  let rules = 
	    ZToplevelComment (NetKAT_Pretty.string_of_policy pol)::
	      (match pol with 
		| Filter pred -> 
		  [ZToplevelComment("this is a filter");
		   make_rule (ZAnd [forwards_pred pred (hist_head inhist_t);
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
		   make_rule (ZAnd[ zterm (pol1_sym inhist_t midhist_t); 
				    zterm (pol2_sym midhist_t outhist_t)])]
		| Star pol1  -> 
		  let pol1_sym = apply_pol pol1 in 
		  let this_sym inh outh = TApp (TVar sym, [inh; outh]) in
		  [ZToplevelComment("this is a star");
		   make_rule (ZEquals(inhist_t, outhist_t));
		   make_rule (ZAnd[ zterm (pol1_sym inhist_t midhist_t);
				    zterm (this_sym midhist_t outhist_t)])]
		| Choice _ -> failwith "I'm not rightly sure what a \"choice\" is "
		| Link (sw1, pt1, sw2, pt2) ->
		  let modsw = mod_fun Switch in
		  let modpt = mod_fun (Header SDN_Types.InPort) in
		  let packet_a_t = TVar packet_a in
		  let packet_b_t = TVar packet_b in
		  [ZToplevelComment("this is a link");
		   make_rule 
		     (ZAnd[forwards_pred (Test (Switch, sw1)) (hist_head inhist_t);
				   forwards_pred (Test ((Header SDN_Types.InPort), pt1)) 
					 (hist_head inhist_t);
			   zterm (modsw (hist_head inhist_t) packet_a_t 
						(encode_vint sw2 Switch));
			   zterm (modpt packet_a_t packet_b_t 
						(encode_vint pt2 (Header SDN_Types.InPort)));
			   ZEquals(hist_cons packet_b_t inhist_t, outhist_t)])]
	      ) in
	  Hashtbl.add hashtbl pol (sym,rules); sym in
      let get_rules () = Hashtbl.fold 
		(fun _ rules a -> snd(rules)@a ) hashtbl [] in
      define_relation, get_rules

  end

end  
    
(* str: name of your test (unique ID)
inp: initial packet
   pol: policy to test
outp: fully-transformed packet
oko: bool option. has to be Some. True if you think it should be satisfiable.
*)


let check_reachability_ints ints str inp pol outp oko =
  let module Sat = Sat(struct let ints = ints end) in
  let open Verify.Stateless in
  let open Verify.Stateless.Support_Code in
  let module Verify = Verify.Stateful(Sat) in
  let open Sat_Syntax in
  let x = inhist in
  let x_t = TVar x in
  let y = outhist in
  let y_t = TVar y in
  let entry_sym = Verify.define_relation pol in
  let last_rule = ZDeclareRule (qrule, [x;y],
				    ZAnd[forwards_pred inp (hist_head x_t);
					     forwards_pred outp (hist_head y_t);
					     zterm (TApp (TVar entry_sym, [TVar x; TVar y]))]) in
  let prog = ZProgram 
	( List.flatten
		[declarations;
		 ZToplevelComment("rule that puts it all together\n")::
		   last_rule::
		   ZToplevelComment("syntactically-generated rules\n")::
		   (Verify.get_rules())] ) in
  let query = reachability_query in
  let assembled_program = Sat.assemble_program 
	(Verify.Support_Code.declare_datatypes 5) prog query in
  let serialize = Sat.serialize_program in
  let solve = Sat.solve in
  Sat_Utils.run_solve oko serialize solve assembled_program str

let check_reachability str inp pol outp = 
  check_reachability_ints 
	(Sat_Utils.collect_constants (Seq (Seq (Filter inp,pol),Filter outp)))
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
