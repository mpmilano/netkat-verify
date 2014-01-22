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
	  let the_packet_a = "the_packet_a"
	  let the_packet_b = "the_packet_b"
      let inhist = "inhist"
      let midhist = "midhist"
      let outhist = "outhist"
      let hist_one = "hist-one"
      let hist_cons = "hist-cons"
	  let hist_head = "hist-head"
	  let tail_equal = "tail-equal"
      let qrule = "q"
      let declarations = [
		ZDeclareVar(inhist,SHistory);
		ZDeclareVar(midhist,SHistory);
		ZDeclareVar(outhist,SHistory);
		ZDeclareVar(the_packet_a,SPacket);
		ZDeclareVar(the_packet_b,SPacket);
		ZDeclareVar(qrule, SRelation([SHistory; SHistory]))]
      let reachability_query = (Printf.sprintf "(query (q %s %s) 
:default-relation smt_relation2
:engine PDR
:print-answer false)
" inhist outhist)
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

    module Z3Pervasives = struct
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

(declare-datatypes
 ()
 ((Hist
  (hist-one (one-packet Packet))
  (hist-cons (head-hist Packet) (rest-hist Hist))
)))

(define-fun hist-head ((x Hist)) Packet 
	(ite (is-hist-one x) (one-packet x)
	   (head-hist x))
)

(define-fun tail-equal ((x Hist) (y Hist)) Bool
	(ite (is-hist-one x)
	   (is-hist-one y)
	   (ite (is-hist-cons y)
		  (= (rest-hist x) (rest-hist y))
		  false)))
	   

" ^ "\n" 


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

    let rec forwards_pred (prd : pred) (pkt : zTerm) : zFormula = 
      let forwards_pred pr : zFormula = forwards_pred pr pkt in
      let rec in_a_neg pred : zFormula = 
	match pred with
	  | Neg p -> forwards_pred p
	  | False -> ZTrue
	  | True -> ZFalse
	  | Test (hdr, v) -> zterm (TApp (pred_test_not hdr, [ pkt; encode_vint v hdr])) 
	  | And (pred1, pred2) -> ZOr [in_a_neg pred1; in_a_neg pred1]
	  | Or (pred1, pred2) -> ZAnd [in_a_neg pred1; in_a_neg pred2] in
      match prd with
	| False -> 
	  ZFalse
	| True -> 
	  ZTrue
	| Test (hdr, v) -> zterm (TApp (pred_test hdr, [ pkt; encode_vint v hdr]))
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
      let inhist = Pervasives.inhist in
      let inhist_t = TVar inhist in
      let outhist = Pervasives.outhist in
      let outhist_t = TVar outhist in
      let midhist = Pervasives.midhist in
      let midhist_t = TVar midhist in
	  let hist_head = TVar Pervasives.hist_head in
	  let tail_equal = TVar Pervasives.tail_equal in
	  let default_params = [inhist; outhist] in

      let rec define_relation pol = 
	try 
	  fst (Hashtbl.find hashtbl pol)
	with Not_found -> 
	  let sym = fresh (SRelation [SHistory; SHistory]) in
	  let rules = 
	    ZToplevelComment (NetKAT_Pretty.string_of_policy pol)::
	      (match pol with 
		| Filter pred -> 
		  [ZToplevelComment("this is a filter");
		   ZDeclareRule (sym, default_params, 
						 ZAnd [forwards_pred pred 
								 (TApp (hist_head, [inhist_t])); 
							   ZEquals(inhist_t, outhist_t)])]
		| Mod(f,v) -> 
		  let modfn = mod_fun f in
		  [ZToplevelComment("this is a mod");
		   ZDeclareRule (sym, default_params, ZAnd[ zterm (TApp (modfn, [TApp (hist_head, [inhist_t]); 
																		 TApp (hist_head, [outhist_t]); (encode_vint v f)]));
													zterm (TApp (tail_equal, [inhist_t; outhist_t]))])]
		| Par (pol1, pol2) -> 
		  let pol1_sym = TVar (define_relation pol1) in
		  let pol2_sym = TVar (define_relation pol2) in
 		  [ZToplevelComment("this is a par");
		   ZDeclareRule (sym, default_params, ZAnd [zterm (TApp (pol1_sym, [inhist_t; outhist_t]))]); 
		   ZDeclareRule (sym, default_params, ZAnd[ zterm (TApp (pol2_sym, [inhist_t; outhist_t]))])]
		| Seq (pol1, pol2) -> 
		  let pol1_sym = TVar (define_relation pol1) in
		  let pol2_sym = TVar (define_relation pol2) in
 		  [ZToplevelComment("this is a seq");
		   ZDeclareRule (sym, default_params, ZAnd[ zterm (TApp (pol1_sym, [inhist_t; midhist_t])); 
													zterm (TApp (pol2_sym, [midhist_t; outhist_t]))])]
		| Star pol1  -> 
		  let pol1_sym = TVar (define_relation pol1) in
		  [ZToplevelComment("this is a star");
		   ZDeclareRule (sym, default_params, ZEquals(inhist_t, outhist_t));
		   ZDeclareRule (sym, default_params, ZAnd[ zterm (TApp (pol1_sym, [inhist_t; midhist_t]));
													zterm (TApp (TVar sym, [midhist_t; outhist_t]))])]
		| Choice _ -> failwith "I'm not rightly sure what a \"choice\" is "
		| Link (sw1, pt1, sw2, pt2) ->
		  let modsw = mod_fun Switch in
		  let modpt = mod_fun (Header SDN_Types.InPort) in
		  let the_packet_a_t = TVar Pervasives.the_packet_a in
		  let the_packet_b_t = TVar Pervasives.the_packet_b in
		  let hist_cons = TVar Pervasives.hist_cons in
		  [ZToplevelComment("this is a link");
		   ZDeclareRule (sym, default_params, 
				 ZAnd[forwards_pred (Test (Switch, sw1)) (TApp (hist_head, [inhist_t]));
				      forwards_pred (Test ((Header SDN_Types.InPort), pt1)) (TApp (hist_head, [inhist_t]));
					  zterm (TApp (modsw, [TApp (hist_head, [inhist_t]); the_packet_a_t; (encode_vint sw2 Switch)]));
					  zterm (TApp (modpt, [the_packet_a_t; the_packet_b_t; (encode_vint pt2 (Header SDN_Types.InPort))]));
					  ZEquals(TApp (hist_cons, [the_packet_b_t; inhist_t]), outhist_t)])]
	      ) in
	  Hashtbl.add hashtbl pol (sym,rules); sym in
      let get_rules () = Hashtbl.fold (fun _ rules a -> snd(rules)@a ) hashtbl [] in
      define_relation, get_rules
		
(*	let unroll_star k pol = 
	  let rec unroll_star k pol = 
		match k with 
		| 0 -> Filter(True)
		| 1 -> Par(pol, Filter(True))
		| _ -> let pol' = unroll_star (k - 1) pol in 
		  Par(Seq(pol, pol'), pol') in
	  match pol with 
	  | Star p -> unroll_star k p
	  | _ -> pol
*)
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
  let open Sat_Syntax in
  let x = Pervasives.inhist in
  let x_t = TVar x in
  let y = Pervasives.outhist in
  let y_t = TVar y in
  let hist_head h= TApp (TVar Pervasives.hist_head, [h]) in
  let entry_sym = Verify.define_relation pol in
  let last_rule = ZDeclareRule (Pervasives.qrule, [x;y],
				    ZAnd[Verify.forwards_pred inp (hist_head x_t);
					     Verify.forwards_pred outp (hist_head y_t);
					     zterm (TApp (TVar entry_sym, [TVar x; TVar y]))] ) in
  let prog = ZProgram ( List.flatten
			      [Pervasives.declarations;
			       ZToplevelComment("rule that puts it all together\n")::last_rule
			       ::ZToplevelComment("syntactically-generated rules\n")::(Verify.get_rules())] ) in
  let query = Pervasives.reachability_query in
  Sat.run_solve oko Verify.Z3Pervasives.declare_datatypes prog query  str

  let check = check_reachability
