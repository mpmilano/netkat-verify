open Packet
open NetKAT_Types
open NetKAT_Util
open Unix
open NetKAT_Sat

  
module Verify = struct
  module Stateless = struct
    open Sat_Syntax
    open Sat_Utils
      
      
    module Pervasives = struct
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
      let declarations = [ZDeclareVar(startpkt, SPacket);
			  ZDeclareVar(endpkt, SPacket);
			  ZDeclareVar(full_hist, SHistory);
			  ZDeclareVar(inpkt, SPacket);
			  ZDeclareVar(midpkt, SPacket);
			  ZDeclareVar(outpkt, SPacket);
			  ZDeclareVar(inhist,SHistory);
			  ZDeclareVar(midhist,SHistory);
			  ZDeclareVar(outhist,SHistory);
			  ZDeclareVar(qrule, SRelation([SPacket; SPacket; SHistory]));
			  ZDeclareVar(k,SLiteral "Int")]
      let reachability_query = (Printf.sprintf "(query (q %s %s %s) 
:default-relation smt_relation2
:engine PDR
:print-answer false)
" startpkt endpkt full_hist)
    end
      
    let zterm x = ZEquals(x, TVar "true") 
      
  end
  module Stateful = functor (Sat : Sat_description) -> struct
    open SDN_Types
    open NetKAT_Types
    open Sat_Syntax
    open Sat_Utils
    open Stateless

    module Z3Pervasives = struct
      open Sat
      let declare_datatypes : string = 
	"
(declare-datatypes 
 () 
 ((Packet
   (packet
"^(if (bitvec_size SSwitch) = 0 then "" else "    (Switch "^serialize_sort SSwitch ^") ")
^(if (bitvec_size SEthDst) = 0 then "" else "    (EthDst "^serialize_sort SEthDst ^") ")
^(if (bitvec_size SEthType) = 0 then "" else "    (EthType "^serialize_sort SEthType ^") ")
^(if (bitvec_size SVlan) = 0 then "" else "    (Vlan "^serialize_sort SVlan ^") ")
^(if (bitvec_size SVlanPcp) = 0 then "" else "    (VlanPcp "^serialize_sort SVlanPcp ^") ")
^(if (bitvec_size SIPProto) = 0 then "" else "    (IPProto "^serialize_sort SIPProto ^") ")
^(if (bitvec_size SIP4Src) = 0 then "" else "    (IP4Src "^serialize_sort SIP4Src ^") ")
^(if (bitvec_size SIP4Dst) = 0 then "" else "    (IP4Dst "^serialize_sort SIP4Dst ^") ")
^(if (bitvec_size STCPSrcPort) = 0 then "" else "    (TCPSrcPort "^serialize_sort STCPSrcPort ^") ")
^(if (bitvec_size STCPDstPort) = 0 then "" else "    (TCPDstPort "^serialize_sort STCPDstPort ^") ")
^(if (bitvec_size SEthSrc) = 0 then "" else "    (EthSrc "^serialize_sort SEthSrc ^") ")
^(if (bitvec_size SInPort) = 0 then "" else "    (InPort "^serialize_sort SInPort ^"))))) ")^ " 

(declare-datatypes
 ()
 ((Hist
  (hist-singleton (packet Packet))
  (hist (packet Packet) (rest-hist Hist))
)))
" ^ "\n" 

    end
      
    let all_used_fields = List.filter (fun x -> (Sat.bitvec_size (header_to_zsort x)) > 0) all_fields
    
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
      let inpkt = Pervasives.inpkt in
      let inpkt_t = TVar inpkt in
      let outpkt = Pervasives.outpkt in
      let outpkt_t = TVar outpkt in
      let midpkt = Pervasives.midpkt in
      let midpkt_t = TVar midpkt in
      let inhist = Pervasives.inhist in
      let inhist_t = TVar inhist in
      let outhist = Pervasives.outhist in
      let outhist_t = TVar outhist in
      let midhist = Pervasives.midhist in
      let midhist_t = TVar midhist in
      let k = Pervasives.k in 
      let k_t = TVar k in 

      let rec define_relation pol = 
	try 
	  fst (Hashtbl.find hashtbl pol)
	with Not_found -> 
	  let sym = fresh (SRelation [SLiteral "Int"; SPacket; SPacket; SHistory; SHistory]) in
	  let rules = 
	    ZToplevelComment (NetKAT_Pretty.string_of_policy pol)::
	      (match pol with 
		| Filter pred -> 
		  [ZToplevelComment("this is a filter");
		   ZDeclareRule (sym, [k; inpkt; outpkt; inhist; outhist], ZAnd [forwards_pred pred inpkt; 
									      ZEquals( inpkt_t,  outpkt_t );
									      ZEquals(inhist_t, outhist_t);
									      ZLiteral(Printf.sprintf "(> %s 0)" k)])]
		| Mod(f,v) -> 
		  let modfn = mod_fun f in
		  [ZToplevelComment("this is a mod");
		   ZDeclareRule (sym, [k; inpkt; outpkt; inhist; outhist], ZAnd[ zterm (TApp (modfn, [inpkt_t; outpkt_t; (encode_vint v f)]));
									      ZEquals(inhist_t, outhist_t);
									      ZLiteral(Printf.sprintf "(> %s 0)" k)])]
		| Par (pol1, pol2) -> 
		  let pol1_sym = TVar (define_relation pol1) in
		  let pol2_sym = TVar (define_relation pol2) in
 		  [ZToplevelComment("this is a par");
		   ZDeclareRule (sym, [k; inpkt; outpkt; inhist; outhist], ZAnd [zterm (TApp (pol1_sym, [k_t; inpkt_t; outpkt_t; inhist_t; outhist_t]));
										 ZLiteral(Printf.sprintf "(> %s 0)" k)]); 
		   ZDeclareRule (sym, [k; inpkt; outpkt; inhist; outhist], ZAnd[ zterm (TApp (pol2_sym, [k_t; inpkt_t; outpkt_t; inhist_t; outhist_t]));
										 ZLiteral(Printf.sprintf "(> %s 0)" k)])]
		| Seq (pol1, pol2) -> 
		  let pol1_sym = TVar (define_relation pol1) in
		  let pol2_sym = TVar (define_relation pol2) in
 		  [ZToplevelComment("this is a seq");
		   ZDeclareRule (sym, [k; inpkt; outpkt; inhist; outhist], ZAnd[ zterm (TApp (pol1_sym, [k_t; inpkt_t; midpkt_t; inhist_t; midhist_t])); 
										 zterm (TApp (pol2_sym, [k_t; midpkt_t; outpkt_t; midhist_t; outhist_t]));
										 ZLiteral(Printf.sprintf "(> %s 0)" k)])]
		| Star pol1  -> 
		  let pol1_sym = TVar (define_relation pol1) in
		  [ZToplevelComment("this is a star");
		   ZDeclareRule (sym, [k; inpkt; outpkt; inhist; outhist], ZAnd [ZEquals (inpkt_t, outpkt_t); 
										 ZEquals(inhist_t, outhist_t);
										 ZLiteral(Printf.sprintf "(> %s 0)" k)]);
		   ZDeclareRule (sym, [k; inpkt; outpkt; inhist; outhist], ZAnd[ zterm (TApp (pol1_sym, [k_t; inpkt_t; midpkt_t; inhist_t; midhist_t]) ); 
										 zterm (TApp (TVar sym, [
										   TLiteral (Printf.sprintf "(- %s 1)" k); 
										   midpkt_t; outpkt_t; midhist_t; outhist_t]));
										 ZLiteral(Printf.sprintf "(> %s 0)" k)])]
		| Choice _ -> failwith "I'm not rightly sure what a \"choice\" is "
		| Link (sw1, pt1, sw2, pt2) -> 
		  let modsw = mod_fun Switch in
		  let modpt = mod_fun (Header SDN_Types.InPort) in
		  let hist_cons pkt hst = TApp (TVar Pervasives.histcons, [pkt; hst]) in
		  [ZToplevelComment("this is a link");
		   ZDeclareRule (sym, [k; inpkt; outpkt; inhist; outhist], 
				 ZAnd[forwards_pred (Test (Switch, sw1)) inpkt; 
				      forwards_pred (Test ((Header SDN_Types.InPort), pt1)) inpkt;
				      zterm (TApp (modsw, [inpkt_t; midpkt_t; (encode_vint sw2 Switch)]));
				      zterm (TApp (modpt, [midpkt_t; outpkt_t; (encode_vint pt2 (Header SDN_Types.InPort))]));
				      ZEquals(outhist_t, hist_cons outpkt_t inhist_t);
				      ZLiteral(Printf.sprintf "(> %s 0)" k)])]
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


let check_reachability  str inp pol outp oko =
  let ints = (Sat_Utils.collect_constants (Seq (Seq (Filter inp,pol),Filter outp))) in
  let module Sat = Sat(struct let ints = ints end) in
  let open Verify.Stateless in
  let module Verify = Verify.Stateful(Sat) in
  let x = Pervasives.inpkt in
  let y = Pervasives.outpkt in
  let hist = Pervasives.outhist in
  let open Sat_Syntax in
  let hist_singleton pkt = TApp (TVar Pervasives.hist_singleton, [pkt]) in
  let entry_sym = Verify.define_relation pol in
  let last_rule = ZDeclareRule (Pervasives.qrule, [x;y;hist],
				    ZAnd[Verify.forwards_pred inp x;
					     Verify.forwards_pred outp y;
					     zterm (TApp (TVar entry_sym, [TLiteral "3";TVar x; TVar y; hist_singleton (TVar x); TVar hist]))] ) in
  let prog = ZProgram ( List.flatten
			      [Pervasives.declarations;
			       ZToplevelComment("rule that puts it all together\n")::last_rule
			       ::ZToplevelComment("syntactically-generated rules\n")::(Verify.get_rules())] ) in
  let query = Pervasives.reachability_query in
  Sat.run_solve oko Verify.Z3Pervasives.declare_datatypes prog query  str

  let check = check_reachability
