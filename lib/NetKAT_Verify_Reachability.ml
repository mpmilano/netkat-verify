open Packet
open NetKAT_Types
open NetKAT_Util
open Unix
open NetKAT_Sat

module type Enable_History = 
  sig 
    val enable_history : bool 
  end

module Verify = functor (Enable_History : Enable_History) -> struct

  module Stateless = struct
    open Sat_Syntax
    open Sat_Utils
      
      
    module Z3Pervasives = struct
      let startpkt = "starting_packet"
      let endpkt = "ending_packet"
      let full_hist = "full_hist"
      let inpkt = "inpkt"
      let midpkt = "midpkt"
      let outpkt = "outpkt"
      let inhist = "inhist"
      let midhist = "midhist"
      let outhist = "outhist"
      let hist_singleton = "hist-singleton"
      let histcons = "hist"
      let qrule = "q"
      let k = "k_bound"
      let declarations = List.flatten [[ZDeclareVar(startpkt, SPacket);
					ZDeclareVar(k,SLiteral "Int");
					ZDeclareVar(endpkt, SPacket);
					ZDeclareVar(inpkt, SPacket);
					ZDeclareVar(midpkt, SPacket);
					ZDeclareVar(outpkt, SPacket)];
				       (if Enable_History.enable_history
					then [
					  ZDeclareVar(full_hist, SHistory);
					  ZDeclareVar(inhist,SHistory);
					  ZDeclareVar(midhist,SHistory);
					  ZDeclareVar(outhist,SHistory);
					  ZDeclareVar(qrule, SRelation([SPacket; SPacket; SHistory]))]
					else [ZDeclareVar(qrule, SRelation([SPacket; SPacket]))])]
				       
      let reachability_query = 
	let engine_string = "
:default-relation smt_relation2
:engine PDR
:print-answer false" in
	match Enable_History.enable_history with
	  | true -> (Printf.sprintf "(query (q %s %s %s) %s)"  startpkt endpkt full_hist engine_string)
	  | false -> (Printf.sprintf "(query (q %s %s) %s)"  startpkt endpkt engine_string)
    end
      
    let zterm x = ZEquals(x, TVar "true") 
      
  end
  module Stateful = functor (Sat : Sat_description) -> struct
    open SDN_Types
    open NetKAT_Types
    open Sat_Syntax
    open Sat_Utils
    open Stateless

    let all_used_fields = List.filter (fun x -> (Sat.bitvec_size (header_to_zsort x)) > 0) all_fields

    module Z3Z3Pervasives = struct
      open Sat
      let declare_datatypes : string = 
	"
(declare-datatypes 
 () 
 ((Packet
   (packet
"^(List.fold_left
     (fun a hdr -> Printf.sprintf "(%s %s)\n%s" 
       (serialize_header hdr) 
       (serialize_sort (header_to_zsort hdr))
       a)
     "" all_used_fields)
   ^"))))
"^
if Enable_History.enable_history then
"(declare-datatypes
 ()
 ((Hist
  (hist (packet Packet) (rest-hist Hist))
  (hist-singleton (packet Packet))

)))
" 
else ""

    end
     
    
    let encode_packet_equals = 
      let open Sat in
      let hash = Hashtbl.create 0 in 
      let encode_packet_equals = 
	(fun (pkt1: zTerm) (pkt2: zTerm) (except :header)  -> 
	  (TApp (
	    (if Hashtbl.mem hash except
	     then
		Hashtbl.find hash except
	     else
		let l = 
		  List.fold_left 
		    (fun acc hd -> 
		      if  hd = except then 
			acc 
		      else
			ZEquals ( (encode_header hd "x"), ( encode_header hd "y"))::acc)
		    [] all_used_fields in 
		let new_except = (z3_macro_top ("packet_equals_except_" ^ (serialize_header except) )
				    [("x", SPacket);("y", SPacket)] SBool  
				    (ZAnd(l))) in
		Hashtbl.add hash except new_except;
		new_except), 
	    [pkt1; pkt2]))) in
      encode_packet_equals 

    let pred_test,pred_test_not = 
      let open Sat in
      let true_hashmap = Hashtbl.create 0 in
      let false_hashmap = Hashtbl.create 0 in
      let pred_test want_true f =  
	let hashmap = (if want_true then true_hashmap else false_hashmap) in
	let name_suffix = (if want_true then "-equals" else "-not-equals") in
	try (Hashtbl.find hashmap f)
	with Not_found -> 
	  let macro = 
	    z3_macro ((serialize_header f) ^ name_suffix)
	      [("x", SPacket); ("v",  (header_to_zsort f))] SBool 
	      (if want_true 
	       then
		  (ZEquals ( (encode_header f "x"),  (TVar "v")))
	       else
		  (ZNotEquals ((encode_header f "x"), (TVar "v"))))
	  in
	  Hashtbl.add hashmap f macro;
	  (Hashtbl.find hashmap f) in
      pred_test true, pred_test false 

    let rec forwards_pred (prd : pred) (pkt : zVar) : zFormula = 
      let forwards_pred pr : zFormula = forwards_pred pr pkt in
      let rec in_a_neg pred : zFormula = 
		match pred with
		| Neg p -> forwards_pred p
		| False -> ZTrue
		| True -> ZFalse
		| Test (hdr, v) -> zterm (TApp (pred_test_not hdr, [TVar pkt; encode_vint v hdr])) 
		| And (pred1, pred2) -> ZOr [in_a_neg pred1; in_a_neg pred1]
		| Or (pred1, pred2) -> ZAnd [in_a_neg pred1; in_a_neg pred2] in
      match prd with
	  | False -> 
		  ZFalse
	  | True -> 
		  ZTrue
	  | Test (hdr, v) -> zterm (TApp (pred_test hdr, [TVar pkt; encode_vint v hdr]))
	  | Neg p -> in_a_neg p
	  | And (pred1, pred2) -> 
		  (ZAnd [forwards_pred pred1; 
				 forwards_pred pred2])
	  | Or (pred1, pred2) -> 
		  (ZOr [forwards_pred pred1;
				forwards_pred pred2]) 
			
	    
    let mod_fun = 
      let open Sat in
      let hashmap = Hashtbl.create 0 in
      let mod_fun f =  
	let packet_equals_fun = encode_packet_equals (TVar "x") (TVar "y") f in
	try (Hashtbl.find hashmap packet_equals_fun)
	with Not_found -> 
	  let macro = z3_macro ("mod_" ^ (serialize_header f)) [("x", SPacket); ("y", SPacket); 
								("v", (header_to_zsort f) )] SBool
	    (
	      ZAnd [zterm packet_equals_fun;
		    ZEquals( (encode_header f "y"),  (TVar "v"))]) in
	  Hashtbl.add hashmap packet_equals_fun macro; 
	  (Hashtbl.find hashmap packet_equals_fun) in
      mod_fun 

    let define_relation, get_rules = 
      let open Sat in
      let hashtbl = Hashtbl.create 0 in
    (*convenience names *)
      let inpkt = Z3Pervasives.inpkt in
      let inpkt_t = TVar inpkt in
      let outpkt = Z3Pervasives.outpkt in
      let outpkt_t = TVar outpkt in
      let midpkt = Z3Pervasives.midpkt in
      let midpkt_t = TVar midpkt in
      let inhist = Z3Pervasives.inhist in
      let inhist_t = TVar inhist in
      let outhist = Z3Pervasives.outhist in
      let outhist_t = TVar outhist in
      let midhist = Z3Pervasives.midhist in
      let midhist_t = TVar midhist in
      let k = Z3Pervasives.k in 
      let k_t = TVar k in 

      let rec define_relation pol = 
	try 
	  fst (Hashtbl.find hashtbl pol)
	with Not_found -> 
	  let sym = fresh (if Enable_History.enable_history
	    then (SRelation [SLiteral "Int"; SPacket; SPacket; SHistory; SHistory])
	    else (SRelation [SLiteral "Int"; SPacket; SPacket]) )in
	  let open Enable_History in
	  let param_list = if enable_history then 
	      [k; inpkt; outpkt; inhist; outhist]
	    else
	      [k; inpkt; outpkt] in
	  let make_rule sort body = 
	      [ZToplevelComment(sort); 
	       ZDeclareRule (sym, param_list, body)] in
	  let rules = 
	    ZToplevelComment (NetKAT_Pretty.string_of_policy pol)::
	    (match pol with 
		| Filter pred -> 
			make_rule "this is a pred"
			  (ZAnd ([forwards_pred pred inpkt; 
					  ZEquals( inpkt_t,  outpkt_t );
					  ZLiteral(Printf.sprintf "(> %s 0)" k)] @ 
					 (if enable_history 
					 then [ZEquals(inhist_t, outhist_t)]
					 else [])))
		| Mod(f,v) -> 
			let modfn = mod_fun f in
			make_rule "this is a mod" 
			  (ZAnd([ zterm (TApp (modfn, [inpkt_t; outpkt_t; (encode_vint v f)]));
					  ZLiteral(Printf.sprintf "(> %s 0)" k)] @
					(if enable_history 
					then [ZEquals(inhist_t, outhist_t)]
					else [])))
		| Par (pol1, pol2) -> 
			let pol1_sym = TVar (define_relation pol1) in
			let pol2_sym = TVar (define_relation pol2) in
			let arg_list = if enable_history then
		      [k_t; inpkt_t; outpkt_t; inhist_t; outhist_t]
		    else
		      [k_t; inpkt_t; outpkt_t] in
			(make_rule "this is a par"
			  (ZAnd [zterm (TApp (pol1_sym, arg_list));
					 ZLiteral(Printf.sprintf "(> %s 0)" k)])) @
			(make_rule "still the same par"
			   (ZAnd[ zterm (TApp (pol2_sym, arg_list));
					  ZLiteral(Printf.sprintf "(> %s 0)" k)]))
		| Seq (pol1, pol2) -> 
			let pol1_sym = TVar (define_relation pol1) in
			let pol2_sym = TVar (define_relation pol2) in
			let arg_list_1 = if enable_history then
		      [k_t; inpkt_t; midpkt_t; inhist_t; midhist_t]
		    else
		      [k_t; inpkt_t; midpkt_t] in
			let arg_list_2 = if enable_history then
		      [k_t; midpkt_t; outpkt_t; midhist_t; outhist_t]
		    else
		      [k_t; midpkt_t; outpkt_t] in
			make_rule "this is a seq"
			  (ZAnd[ zterm (TApp (pol1_sym, arg_list_1)); 
					 zterm (TApp (pol2_sym, arg_list_2));
					 ZLiteral(Printf.sprintf "(> %s 0)" k)])
		| Star pol1  -> 
			let pol1_sym = TVar (define_relation pol1) in
			(make_rule "this is a star"
			   (ZAnd ([ZEquals (inpkt_t, outpkt_t); 
					   ZLiteral(Printf.sprintf "(> %s 0)" k)]
					  @ if enable_history then [ZEquals(inhist_t, outhist_t)]
					  else []))) @ 
			(let new_k = TLiteral (Printf.sprintf "(- %s 1)" k) in
			let arg_list_1 = if enable_history then
		      [k_t; inpkt_t; midpkt_t; inhist_t; midhist_t]
		    else
		      [k_t; inpkt_t; midpkt_t] in
			let arg_list_2 = if enable_history then 
		      [new_k; midpkt_t; outpkt_t; midhist_t; outhist_t]
		    else
		      [new_k; midpkt_t; outpkt_t] in
			make_rule "still the same star"
			  (ZAnd[ zterm (TApp (pol1_sym, arg_list_1)); 
					 zterm (TApp (TVar sym, arg_list_2));
					 ZLiteral(Printf.sprintf "(> %s 0)" k)]))
		| Choice _ -> failwith "I'm not rightly sure what a \"choice\" is "
		| Link (sw1, pt1, sw2, pt2) -> 
			let modsw = mod_fun Switch in
			let modpt = mod_fun (Header SDN_Types.InPort) in
			let hist_cons pkt hst = TApp (TVar Z3Pervasives.histcons, [pkt; hst]) in
			make_rule "this is a link"
			  (ZAnd([forwards_pred (Test (Switch, sw1)) inpkt; 
					 forwards_pred (Test ((Header SDN_Types.InPort), pt1)) inpkt;
					 zterm (TApp (modsw, [inpkt_t; midpkt_t; (encode_vint sw2 Switch)]));
					 zterm (TApp (modpt, [midpkt_t; outpkt_t; (encode_vint pt2 (Header SDN_Types.InPort))]));
					 ZLiteral(Printf.sprintf "(> %s 0)" k)]
					@ if enable_history then 
					  [ZEquals(outhist_t, hist_cons outpkt_t inhist_t)]
					else []))
	    ) in
	  Hashtbl.add hashtbl pol (sym,rules); sym in
      let get_rules () = Hashtbl.fold (fun _ rules a -> snd(rules)@a ) hashtbl [] in
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
  let module Verify = Verify(struct let enable_history = false end) in
  let open Verify.Stateless in
  let module Verify = Verify.Stateful(Sat) in
  let x = Z3Pervasives.inpkt in
  let y = Z3Pervasives.outpkt in
  let open Sat_Syntax in
  let entry_sym = Verify.define_relation pol in
  let last_rule = ZDeclareRule (Z3Pervasives.qrule, [x;y],
				    ZAnd[Verify.forwards_pred inp x;
					     Verify.forwards_pred outp y;
					     zterm (TApp (TVar entry_sym, [TLiteral "3";TVar x; TVar y]))] ) in
  let prog = ZProgram ( List.flatten
			      [Z3Pervasives.declarations;
			       ZToplevelComment("rule that puts it all together\n")::last_rule
			       ::ZToplevelComment("syntactically-generated rules\n")::(Verify.get_rules())] ) in
  let query = Z3Pervasives.reachability_query in
  Sat.run_solve oko Verify.Z3Z3Pervasives.declare_datatypes prog query  str
	
let check_reachability str inp pol outp oko = 
  let ints = (Sat_Utils.collect_constants (Seq (Seq (Filter inp,pol),Filter outp))) in
  check_reachability_ints ints str inp pol outp oko


let check = check_reachability
	
let check_reachability_pushbutton str pol = 
  let open NetKAT_Sat.Sat_Syntax in
  let ints = Sat_Utils.collect_constants pol in
  let inp = Test (Switch, (List.hd (List.rev (ints SSwitch)))) in
  let outp = Test (Switch, (List.hd (ints SSwitch))) in
  check_reachability_ints ints str inp pol outp (Some true)
  
