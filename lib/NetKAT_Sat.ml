open Packet
open NetKAT_Types
open NetKAT_Util
open Unix


(* The [Sat] module provides a representation of formulas in
   first-order logic, a representation of packets, and a function for
   testing their satisfiability. *)

module Sat_Syntax = struct 

    type zVar = string
	
    type zSort = 
      | SPacket
      | SHistory
      | SInt
      | SSwitch
      | SEthDst
      | SEthType
      | SVlan
      | SVlanPcp
      | SIPProto
      | SIP4Src
      | SIP4Dst
      | STCPSrcPort
      | STCPDstPort
      | SEthSrc
      | SInPort
      | SBool
      | SRelation of (zSort list)
      | SFunction of (zSort list) * zSort
      | SMacro of ((zVar * zSort) list) * zSort
      | SLiteral of string
	  
    type zTerm = 
      | TUnit 
      | TVar of zVar
      | TInt of Int64.t
      | TSwitch of Int64.t
      | TEthDst of Int64.t
      | TEthType of Int64.t
      | TVlan of Int64.t
      | TVlanPcp of Int64.t
      | TIPProto of Int64.t
      | TIP4Src of Int64.t
      | TIP4Dst of Int64.t
      | TTCPSrcPort of Int64.t
      | TTCPDstPort of Int64.t
      | TEthSrc of Int64.t
      | TInPort of Int64.t
      | TLiteral of string
      | TApp of zTerm * (zTerm list)
	  
    type zFormula =
      | ZNoop
      | ZTrue
      | ZFalse 
      | ZAnd of zFormula list
      | ZOr of zFormula list
      | ZEquals of zTerm * zTerm
      | ZNotEquals of zTerm * zTerm
      | ZComment of string * zFormula
      | ZLiteral of string (* plop the string right in *)
	  
    type zDeclare = 
      | ZDeclareRule of zVar * (zVar list) * zFormula
      | ZDeclareVar of zVar * zSort
      | ZDefineVar of zVar * zSort * zFormula
      | ZDeclareAssert of zFormula
      | ZToplevelComment of string
	  
    type zProgram = 
      | ZProgram of zDeclare list

end

module Sat_Utils = struct
  open Sat_Syntax
    (*number of bits required to represent number *)
  let number_of_bits n = 
    let rec number_of_bits n acc = 
      if (n == 0)
      then acc
      else number_of_bits (n asr 1) (acc + 1) in
    number_of_bits n 0
      
let rec remove_links (pol : 'a) : 'a = 
  let make_transition (switch1, port1) (switch2, port2) : policy =     
    Seq (Filter (And (Test (Switch, switch1), Test (Header SDN_Types.InPort, port1))), 
	 Seq (Mod (Switch , switch2) , Mod (Header SDN_Types.InPort, port2))) in
  match pol with 
    | Link (s1,p1,s2,p2) -> make_transition (s1, p1) (s2, p2)
    | Filter _ -> pol
    | Mod _ -> pol
    | Par (l, r) -> Par (remove_links l, remove_links r)
    | Seq (f, s) -> Seq (remove_links f, remove_links s)
    | Star p -> Star (remove_links p)
    | Choice _ -> failwith "choice not supported"

    open SDN_Types
    let serialize_header (header: header) : string = 
      match header with
	| Header InPort -> 
	  "InPort"
	| Header EthSrc -> 
	  "EthSrc"
	| Header EthDst -> 
	  "EthDst"
	| Header EthType ->  
	  "EthType"
	| Header Vlan ->  
	  "Vlan"
	| Header VlanPcp ->
	  "VlanPcp"
	| Header IPProto ->  
	  "IPProto"
	| Header IP4Src ->  
	  "IP4Src"
	| Header IP4Dst ->  
	  "IP4Dst"
	| Header TCPSrcPort ->  
	  "TCPSrcPort"
	| Header TCPDstPort ->  
	  "TCPDstPort"
	| Switch -> 
	  "Switch"
	    
    let serialize_comment c = 
      Printf.sprintf "%s" c
	
	    
    let all_fields =
      [ Header InPort 
      ; Header EthSrc
      ; Header EthDst
      ; Header EthType
      ; Header Vlan
      ; Header VlanPcp
      ; Header IPProto
      ; Header IP4Src
      ; Header IP4Dst
      ; Header TCPSrcPort
      ; Header TCPDstPort
      ; Switch 
      ]

    let all_fields_zsort = 
      [ SSwitch 
      ; SEthDst
      ; SEthType
      ; SVlan
      ; SVlanPcp
      ; SIPProto
      ; SIP4Src
      ; SIP4Dst
      ; STCPSrcPort
      ; STCPDstPort
      ; SEthSrc
      ; SInPort]

    let header_to_zsort  = function
	| Header InPort -> SInPort
	| Header EthSrc -> SEthSrc
	| Header EthDst -> SEthDst
	| Header EthType -> SEthType
	| Header Vlan -> SVlan
	| Header VlanPcp -> SVlanPcp
	| Header IPProto -> SIPProto
	| Header IP4Src -> SIP4Src
	| Header IP4Dst -> SIP4Dst
	| Header TCPSrcPort -> STCPSrcPort
	| Header TCPDstPort -> STCPDstPort
	| Switch -> SSwitch

	
    let encode_header (header: header) (pkt:zVar) : zTerm =
      match header with
	| Header InPort -> 
          TApp (TVar (serialize_header header), [TVar pkt])
	| Header EthSrc -> 
          TApp (TVar (serialize_header header), [TVar pkt])
	| Header EthDst -> 
          TApp (TVar (serialize_header header), [TVar pkt])
	| Header EthType ->  
          TApp (TVar (serialize_header header), [TVar pkt])
	| Header Vlan ->  
          TApp (TVar (serialize_header header), [TVar pkt])
	| Header VlanPcp ->
          TApp (TVar (serialize_header header), [TVar pkt])
	| Header IPProto ->  
          TApp (TVar (serialize_header header), [TVar pkt])
	| Header IP4Src ->  
          TApp (TVar (serialize_header header), [TVar pkt])
	| Header IP4Dst ->  
          TApp (TVar (serialize_header header), [TVar pkt])
	| Header TCPSrcPort ->  
          TApp (TVar (serialize_header header), [TVar pkt])
	| Header TCPDstPort ->  
          TApp (TVar (serialize_header header), [TVar pkt])
	| Switch -> 
          TApp (TVar (serialize_header header), [TVar pkt])

    let encode_vint (v: VInt.t) h : zTerm = 
      let v = (VInt.get_int64 v) in
      match h with 
	| Header InPort -> TInPort v
	| Header EthSrc -> TEthSrc v
	| Header EthDst -> TEthDst v
	| Header EthType -> TEthType v
	| Header Vlan -> TVlan v
	| Header VlanPcp -> TVlanPcp v
	| Header IPProto -> TIPProto v
	| Header IP4Src -> TIP4Src v
	| Header IP4Dst -> TIP4Dst v
	| Header TCPSrcPort -> TTCPSrcPort v
	| Header TCPDstPort -> TTCPDstPort v
	| Switch -> TSwitch v


  let collect_constants pol : Sat_Syntax.zSort -> (VInt.t list) = 
    let module Header_VInt_set = Set.Make(struct 
      let compare = Pervasives.compare
      type t = (Sat_Syntax.zSort * VInt.t)
    end) in
    let module VInt_set = Set.Make(struct 
      let compare = Pervasives.compare
      type t = VInt.t
    end) in
    
    let set_hash = Hashtbl.create 0 in
    let final_hash = Hashtbl.create 0 in
    let combine a b = Header_VInt_set.union a b in
    let empty = Header_VInt_set.empty in
    let single = Header_VInt_set.singleton in
    let elems l = List.fold_left (fun a x -> Header_VInt_set.add x a) empty l in
    let rec collect_constants pol = 
      let rec collect_pred_constants pred = 
	match pred with
	  | True -> empty
	  | False -> empty
	  | Test (h, v) -> single (header_to_zsort h, v)
	  | And (a,b) -> combine (collect_pred_constants a) (collect_pred_constants b)
	  | Or (a,b) -> combine (collect_pred_constants a) (collect_pred_constants b)
	  | Neg p -> collect_pred_constants p
      in
      match pol with
	| Link (s1, p1, s2, p2) -> elems [SSwitch, s1; SSwitch, s2; SInPort, p1; SInPort, p2]
	| Filter pred -> collect_pred_constants pred
	| Mod (f, v) -> single (header_to_zsort f, v)
	| Par (l, r) -> combine (collect_constants l) (collect_constants r)
	| Seq (f, s) -> combine (collect_constants f) (collect_constants s)
	| Star p -> collect_constants p
	| Choice (a, b) -> combine (collect_constants a) (collect_constants b) in
    Header_VInt_set.iter 
      (fun (a,b) -> 
	try (let old = Hashtbl.find set_hash a in
	     Hashtbl.replace set_hash a (VInt_set.add b old))
	with Not_found -> Hashtbl.add set_hash a (VInt_set.singleton b))
      (collect_constants pol);
    Hashtbl.iter (fun a b -> Hashtbl.add final_hash a (VInt_set.elements b)) set_hash;
    (fun x -> try (Hashtbl.find final_hash x) with Not_found -> [])
	    
end

module type ParameterizedOnInts = 
sig 
  val ints : Sat_Syntax.zSort -> (VInt.t list)
end

module type Sat_description = 
sig 
  val serialize_sort : Sat_Syntax.zSort -> string
  val serialize_term : Sat_Syntax.zTerm -> string
  val z3_macro_top : string -> (Sat_Syntax.zVar * Sat_Syntax.zSort) list -> 
    Sat_Syntax.zSort -> Sat_Syntax.zFormula -> Sat_Syntax.zTerm
  val z3_macro : string -> (Sat_Syntax.zVar * Sat_Syntax.zSort) list -> 
    Sat_Syntax.zSort -> Sat_Syntax.zFormula -> Sat_Syntax.zTerm
  val fresh : Sat_Syntax.zSort -> Sat_Syntax.zVar
  val bitvec_literal : Sat_Syntax.zSort -> int -> string
  val bitvec_size : Sat_Syntax.zSort -> int
end

module Sat = 
  functor (Int_List : ParameterizedOnInts) -> struct
      
    open Sat_Utils
    open Sat_Syntax

    let bitvec_size = 
      let hash = Hashtbl.create 0 in
      List.iter (fun field -> 
	let ints = Int_List.ints field in
	match ints with 
	  | [] -> Hashtbl.add hash field 0
	  | _ -> Hashtbl.add hash field (Sat_Utils.number_of_bits ((List.length ints) + 1)))
	all_fields_zsort;
      Hashtbl.find hash

	  
    (* fresh variables *)
    let fresh_cell = ref []
    let macro_list_top = ref []
    let macro_list_bottom = ref []
    
      
    let fresh s = 
      let l = !fresh_cell in  
      let n = List.length l in 
      let x = match s with
	| SPacket -> 
          Printf.sprintf "_pkt%d" n
	| SHistory ->
	  Printf.sprintf "_hist%d" n
	| SInt -> 
          Printf.sprintf "_n%d" n
	| SSwitch -> 
	  Printf.sprintf "_sw%d" n
	| SEthDst -> 
	  Printf.sprintf "_ed%d" n
	| SEthType -> 
          Printf.sprintf "_et%d" n
	| SVlan ->
	  Printf.sprintf "_vl%d" n
	| SVlanPcp -> 
	  Printf.sprintf "_vlpcp%d" n
	| SIPProto -> 
          Printf.sprintf "_ip%d" n
	| SIP4Src ->
          Printf.sprintf "_ip4src%d" n
	| SIP4Dst -> 
	  Printf.sprintf "_ip4dst%d" n
	| STCPSrcPort -> 
          Printf.sprintf "_tcpsrc%d" n
	| STCPDstPort ->
          Printf.sprintf "_tcpdst%d" n
	| SEthSrc ->
          Printf.sprintf "_ethsrc%d" n
	| SInPort ->
          Printf.sprintf "_inprt%d" n
	| SFunction _ -> 
          Printf.sprintf "_f%d" n 
	| SRelation _ -> 
	  Printf.sprintf "_r%d" n
	| _ -> failwith "not implemented in fresh" in 
      fresh_cell := ZDeclareVar(x,s)::l;
      x
	
    let rec serialize_sort = function
      | SInt -> 
	Printf.sprintf "SInt"      
      | SSwitch -> 
	Printf.sprintf "(_ BitVec %d)" (bitvec_size SSwitch)
      | SEthDst ->
	Printf.sprintf "(_ BitVec %d)" (bitvec_size SEthDst)
      | SEthType ->
	Printf.sprintf "(_ BitVec %d)" (bitvec_size SEthType)
      | SVlan ->
	Printf.sprintf "(_ BitVec %d)" (bitvec_size SVlan)
      | SVlanPcp ->
	Printf.sprintf "(_ BitVec %d)" (bitvec_size SVlanPcp)
      | SIPProto ->
	Printf.sprintf "(_ BitVec %d)" (bitvec_size SIPProto)
      | SIP4Src ->
	Printf.sprintf "(_ BitVec %d)" (bitvec_size SIP4Src)
      | SIP4Dst ->
	Printf.sprintf "(_ BitVec %d)" (bitvec_size SIP4Dst)
      | STCPSrcPort ->
	Printf.sprintf "(_ BitVec %d)" (bitvec_size STCPSrcPort)
      | STCPDstPort ->
	Printf.sprintf "(_ BitVec %d)" (bitvec_size STCPDstPort)
      | SEthSrc ->
	Printf.sprintf "(_ BitVec %d)" (bitvec_size SEthSrc)
      | SInPort -> 
	Printf.sprintf "(_ BitVec %d)" (bitvec_size SInPort)
      | SPacket -> 
	"Packet"
      | SHistory -> 
	"Hist"
      | SBool ->
	"Bool"
      | SFunction(sortlist,sort2) -> 
	Printf.sprintf "(%s) %s" 
          (intercalate serialize_sort " " sortlist)
          (serialize_sort sort2)
      | SMacro(args,ret) -> 
	let serialize_arglist args = 
	  (intercalate (fun (a, t) -> Printf.sprintf "(%s %s)" a (serialize_sort t)) " " args) in
	Printf.sprintf "(%s) %s"
	  (serialize_arglist args)
	  (serialize_sort ret)
      | SLiteral s -> s
      | SRelation (sortlist) ->
	Printf.sprintf "(%s)"
	  (intercalate serialize_sort " " sortlist)
	  
    let serialize_arglist args = 
      (intercalate (fun (a, t) -> Printf.sprintf "(%s %s)" a (serialize_sort t)) " " args)
	
    let bitvec_literal s n = 
      (Printf.sprintf "(_ bv%u %u)" n (bitvec_size s))
	
    let tInt_to_string = 
      let switch_map = Hashtbl.create 0 in
      let ethdst_map = Hashtbl.create 0 in
      let ethtype_map = Hashtbl.create 0 in
      let vlan_map = Hashtbl.create 0 in
      let vlanpcp_map = Hashtbl.create 0 in
      let ipproto_map = Hashtbl.create 0 in
      let ip4src_map = Hashtbl.create 0 in
      let ip4dst_map = Hashtbl.create 0 in
      let tcpsrcport_map = Hashtbl.create 0 in
      let tcpdstport_map = Hashtbl.create 0 in
      let ethsrc_map = Hashtbl.create 0 in
      let inport_map = Hashtbl.create 0 in
      List.iteri (fun i x -> Hashtbl.add switch_map (VInt.get_int64 x) i) (Int_List.ints SSwitch);
      List.iteri (fun i x -> Hashtbl.add ethdst_map (VInt.get_int64 x) i) (Int_List.ints SEthDst);
      List.iteri (fun i x -> Hashtbl.add ethtype_map (VInt.get_int64 x) i) (Int_List.ints SEthType);
      List.iteri (fun i x -> Hashtbl.add vlan_map (VInt.get_int64 x) i) (Int_List.ints SVlan);
      List.iteri (fun i x -> Hashtbl.add vlanpcp_map (VInt.get_int64 x) i) (Int_List.ints SVlanPcp);
      List.iteri (fun i x -> Hashtbl.add ipproto_map (VInt.get_int64 x) i) (Int_List.ints SIPProto);
      List.iteri (fun i x -> Hashtbl.add ip4src_map (VInt.get_int64 x) i) (Int_List.ints SIP4Src);
      List.iteri (fun i x -> Hashtbl.add ip4dst_map (VInt.get_int64 x) i) (Int_List.ints SIP4Dst);
      List.iteri (fun i x -> Hashtbl.add tcpsrcport_map (VInt.get_int64 x) i) (Int_List.ints STCPSrcPort);
      List.iteri (fun i x -> Hashtbl.add tcpdstport_map (VInt.get_int64 x) i) (Int_List.ints STCPDstPort);
      List.iteri (fun i x -> Hashtbl.add ethsrc_map (VInt.get_int64 x) i) (Int_List.ints SEthSrc);
      List.iteri (fun i x -> Hashtbl.add inport_map (VInt.get_int64 x) i) (Int_List.ints SInPort);
      let tInt_to_string = function
        | TSwitch n -> (Printf.sprintf "(_ bv%d %d)" (Hashtbl.find switch_map n) (bitvec_size SSwitch))
	| TEthDst n -> (Printf.sprintf "(_ bv%d %d)" (Hashtbl.find ethdst_map n) (bitvec_size SEthDst))
	| TEthType n -> (Printf.sprintf "(_ bv%d %d)" (Hashtbl.find ethtype_map n) (bitvec_size SEthType))
	| TVlan n -> (Printf.sprintf "(_ bv%d %d)" (Hashtbl.find vlan_map n) (bitvec_size SVlan))
	| TVlanPcp n -> (Printf.sprintf "(_ bv%d %d)" (Hashtbl.find vlanpcp_map n) (bitvec_size SVlanPcp))
	| TIPProto n -> (Printf.sprintf "(_ bv%d %d)" (Hashtbl.find ipproto_map n) (bitvec_size SIPProto))
	| TIP4Src n -> (Printf.sprintf "(_ bv%d %d)" (Hashtbl.find ip4src_map n) (bitvec_size SIP4Src))
	| TIP4Dst n -> (Printf.sprintf "(_ bv%d %d)" (Hashtbl.find ip4dst_map n) (bitvec_size SIP4Dst))
	| TTCPSrcPort n -> (Printf.sprintf "(_ bv%d %d)" (Hashtbl.find tcpsrcport_map n) (bitvec_size STCPSrcPort))
	| TTCPDstPort n -> (Printf.sprintf "(_ bv%d %d)" (Hashtbl.find tcpdstport_map n) (bitvec_size STCPDstPort))
	| TEthSrc n -> (Printf.sprintf "(_ bv%d %d)" (Hashtbl.find ethsrc_map n) (bitvec_size SEthSrc))
	| TInPort n -> (Printf.sprintf "(_ bv%d %d)" (Hashtbl.find inport_map n) (bitvec_size SInPort))
	| _ -> failwith "wasn't a tint" in
      tInt_to_string
	
    let rec serialize_term term : string = 
      match term with 
	| TUnit -> 
          "()"
	| TVar x -> 
	  x
	| TInt n -> 
	  Int64.to_string n
	| TLiteral s -> s
	| TApp (term1, terms) -> 
	  Printf.sprintf "(%s %s)" (serialize_term term1) (intercalate serialize_term " " terms)
	| _ -> tInt_to_string term

    let rec serialize_formula = function
      | ZNoop -> ""
      | ZTrue -> 
	Printf.sprintf "true"
      | ZFalse -> 
	Printf.sprintf "false"
      | ZEquals (t1, t2) -> 
      (*readability hack: remove "= true" case *)
	(match t1, t2 with
	  | TVar "true", t -> serialize_term t
	  | t, TVar "true" -> serialize_term t
	  | t1, t2 -> Printf.sprintf "(equals %s %s)" (serialize_term t1) (serialize_term t2))
      | ZNotEquals (t1, t2) -> 
      (*readability hack: remove "= true" case *)
	(match t1, t2 with
	  | TVar "true", t -> serialize_term t
	  | t, TVar "true" -> serialize_term t
	  | t1, t2 -> Printf.sprintf "(not (equals %s %s))" (serialize_term t1) (serialize_term t2))
      | ZAnd([]) -> 
	Printf.sprintf "true"
      | ZAnd([f]) -> 
	Printf.sprintf "%s" (serialize_formula f)
      | ZAnd(f::fs) -> 
	Printf.sprintf "(and %s %s)" (serialize_formula f) (serialize_formula (ZAnd(fs)))
      | ZOr([]) -> 
	Printf.sprintf "false"
      | ZOr([f]) -> 
	Printf.sprintf "%s" (serialize_formula f)
      | ZOr(f::fs) -> 
	Printf.sprintf "(or %s %s)" (serialize_formula f) (serialize_formula (ZOr(fs)))
      | ZComment(c, f) -> 
	Printf.sprintf "\n;%s\n%s\n; END %s\n" c (serialize_formula f) c
      | ZLiteral s -> s

    let serialize_declare d = 
      match d with 
	| ZToplevelComment(c) -> 
	  Printf.sprintf "\n;%s" (Str.global_replace (Str.regexp_string "\n") "\n;" c)
	| ZDefineVar (x, s, b) -> 
	  Printf.sprintf "(define-fun %s %s %s)" x (serialize_sort s) (serialize_formula b)
	| ZDeclareVar (x, s) ->
          (match s with 
            | SFunction _ -> Printf.sprintf "(declare-fun %s %s)" x (serialize_sort s)
	    | SRelation _ -> Printf.sprintf "(declare-rel %s %s)" x (serialize_sort s)
	    | SMacro _ -> failwith "macros should be in ZDefineVar"
	    | SPacket -> 
	      "(declare-var "^x^" "^(serialize_sort s)^")" 
            | _ -> Printf.sprintf "(declare-var %s %s)" x (serialize_sort s)
	  )
	| ZDeclareAssert(f) -> 
          Printf.sprintf "(assert %s)" (serialize_formula f)
	| ZDeclareRule(sym, vars, body) ->
	  Printf.sprintf "(rule (=> %s (%s %s)))"
	    (serialize_formula body)
	    sym
	    (intercalate (fun x -> x) " " vars)


    let serialize_program pervasives p query: string = 
      let ZProgram(ds) = p in 
      let ds' = List.flatten [!fresh_cell;
			      !macro_list_top;
			      [ZToplevelComment("end initial declarations, commence dependent declarations\n")];
			      !macro_list_bottom;
			      [ZToplevelComment("End Definitions, Commence SAT expressions\n")]; 
			      ds] in 
      Printf.sprintf "%s\n%s\n%s\n"
	pervasives
	(intercalate serialize_declare "\n" ds') 
	query


    let define_z3_macro (name : string) (arglist : (zVar * zSort) list)  (rettype : zSort) (body : zFormula)  = 
      [ZDefineVar (name, SMacro (arglist, rettype), body)]
	
    let z3_macro, z3_macro_top = 
      let z3_macro_picklocation put_at_top (name : string) (arglist : (zVar * zSort) list) 
	  (rettype : zSort)(body : zFormula) : zTerm = 
	let name = name in
	let new_macro = (define_z3_macro name arglist rettype body) in
	(if put_at_top then
	    macro_list_top := new_macro @ (!macro_list_top)
	 else
	    macro_list_bottom := new_macro @ (!macro_list_bottom));
	TVar name in      
      let z3_macro = z3_macro_picklocation false in
      let z3_macro_top = z3_macro_picklocation true in
      z3_macro, z3_macro_top


    let solve pervasives prog query: bool = 
      let s = (serialize_program pervasives prog query) in
      let z3_out,z3_in = open_process "z3 -in -smt2 -nw" in 
      let _ = output_string z3_in s in
      let _ = flush z3_in in 
      let _ = close_out z3_in in 
      let b = Buffer.create 17 in 
      (try
	 while true do
           Buffer.add_string b (input_line z3_out);
           Buffer.add_char b '\n';
	 done
       with End_of_file -> ());
      Buffer.contents b = "sat\n"

    let run_solve oko pervasives prog query str : bool =
      let file = Printf.sprintf "%s%sdebug-%s.rkt" (Filename.get_temp_dir_name ()) Filename.dir_sep str in
      let oc = open_out (file) in 
      Printf.fprintf oc "%s\n;This is the program corresponding to %s\n" (serialize_program pervasives prog query) str;
      close_out oc;
      let run_result = (
    match oko, solve pervasives prog query with
      | Some (ok : bool), (sat : bool) ->
        if ok = sat then
	  true
        else
            (Printf.printf "[Verify.check %s: expected %b got %b]\n%!" str ok sat; 
	     Printf.printf "Offending program is in %s\n" file;
	     false)
      | None, sat ->
        (Printf.printf "[Verify.check %s: %b]\n%!" str sat; false)) in
      run_result 

  end
