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
      | ZIf of zFormula * zFormula * zFormula
      | ZLiteral of string (* plop the string right in *)

    type constr_t = (zVar * zSort)
    type variant_t = zVar * (constr_t list)
	  
    type zDeclare = 
      | ZDeclareRule of zVar * (zVar list) * zFormula
      | ZDeclareQuery of zVar * (zTerm list)
      | ZDeclareDatatype of zVar * (variant_t list)
      | ZDeclareVar of zVar * zSort
      | ZDefineVar of zVar * zSort * zFormula
      | ZDeclareAssert of zFormula
      | ZToplevelComment of string
      | ZDeclareLiteral of string 
	  
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
      [ SInPort 
      ; SEthSrc
      ; SEthDst
      ; SEthType
      ; SVlan
      ; SVlanPcp
      ; SIPProto
      ; SIP4Src
      ; SIP4Dst
      ; STCPSrcPort
      ; STCPDstPort
      ; SSwitch ]

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

    let header_to_zterm = function
	| Header InPort -> (fun x -> TInPort x)
	| Header EthSrc -> (fun x -> TEthSrc x)
	| Header EthDst -> (fun x -> TEthDst x)
	| Header EthType -> (fun x -> TEthType x)
	| Header Vlan -> (fun x -> TVlan x)
	| Header VlanPcp -> (fun x -> TVlanPcp x)
	| Header IPProto -> (fun x -> TIPProto x)
	| Header IP4Src -> (fun x -> TIP4Src x)
	| Header IP4Dst -> (fun x -> TIP4Dst x)
	| Header TCPSrcPort -> (fun x -> TTCPSrcPort x)
	| Header TCPDstPort -> (fun x -> TTCPDstPort x)
	| Switch -> (fun x -> TSwitch x)

	
    let encode_header (header: header) (pkt:zTerm) : zTerm = 
      TApp (TVar (serialize_header header), [pkt])

    let encode_vint (v: VInt.t) h : zTerm = 
      let v = (VInt.get_int64 v) in
      ((header_to_zterm h) v)


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

  let define_z3_macro (name : string) (arglist : (zVar * zSort) list)  (rettype : zSort) (body : zFormula)  = 
    [ZDefineVar (name, SMacro (arglist, rettype), body)]

	  
  let printdebug_prog serialize prog str = 
    let file = Printf.sprintf "%s%sdebug-%s.rkt" (Filename.get_temp_dir_name ()) Filename.dir_sep str in
    let oc = open_out (file) in 
    Printf.fprintf oc "%s\n;This is the program corresponding to %s\n" (serialize prog) str;
    close_out oc;
	file
	

  let run_solve oko serialize solve prog str : bool * float =
	let file = printdebug_prog serialize prog str in
    let run_result = (
    match oko, (solve prog) with
      | Some (ok : bool), ((sat : bool), tm) ->
        if ok = sat then
	  true,tm
        else
          (Printf.printf "[Verify.check %s: expected %b got %b]\n%!" str ok sat; 
	   Printf.printf "Offending program is in %s" file;
	   false,tm)
      | None, (sat,tm) ->
        (Printf.printf "[Verify.check %s: %b]\n%!" str sat; false,tm)) in
    run_result 
      
end

module type Sat_Backend_Descr = 
sig 
  val ints : Sat_Syntax.zSort -> (VInt.t list)
end

module type Sat_description = 
sig 
  val serialize_sort : Sat_Syntax.zSort -> string
  val serialize_term : Sat_Syntax.zTerm -> string
  val serialize_program : Sat_Syntax.zProgram -> string
  val assemble_program : (Sat_Syntax.zDeclare list) -> Sat_Syntax.zProgram -> Sat_Syntax.zDeclare -> Sat_Syntax.zProgram
  val fresh : Sat_Syntax.zSort -> Sat_Syntax.zVar * Sat_Syntax.zDeclare
  val bitvec_literal : Sat_Syntax.zSort -> int -> string
  val bitvec_size : Sat_Syntax.zSort -> int
  val solve : Sat_Syntax.zProgram -> bool * float
end

module Z3Sat = 
  functor (Int_List : Sat_Backend_Descr) -> struct
      
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

	let fresh = 
      (* fresh variables *)
      let fresh_cell = ref [] in
      
      let fresh s : Sat_Syntax.zVar * Sat_Syntax.zDeclare = 
		let l = !fresh_cell in  
		let n = List.length l in 
		let x = match s with
		  | SMacro _ -> failwith "macros need not use fresh"
		  | SLiteral _ -> failwith "literals should not use fresh"
		  | SPacket -> 
			Printf.sprintf "_pkt%d" n
		  | SHistory ->
			Printf.sprintf "_hist%d" n
		  | SFunction _ -> 
			Printf.sprintf "_f%d" n 
		  | SRelation _ -> 
			Printf.sprintf "_r%d" n
		  | _ -> 
			Printf.sprintf "_n%d" n
		in 
		let decl = ZDeclareVar(x,s) in
		fresh_cell := decl::l;
		x,decl in
	  fresh
	
    let rec serialize_sort srt = match srt with
      | SInt -> 
	Printf.sprintf "SInt"      
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
      | _ -> Printf.sprintf "(_ BitVec %d)" (bitvec_size srt)

	  
    let serialize_arglist args = 
      (intercalate (fun (a, t) -> Printf.sprintf "(%s %s)" a (serialize_sort t)) " " args)
	
    let bitvec_literal s n = 
      (Printf.sprintf "(_ bv%u %u)" n (bitvec_size s))
	
    let tInt_to_string = 
      let hashmap = Hashtbl.create 0 in
      List.iter (fun hdr -> 
	let hdr_map = Hashtbl.create 0 in
	List.iteri (fun i x -> Hashtbl.add hdr_map (VInt.get_int64 x) i) (Int_List.ints hdr);
	Hashtbl.add hashmap hdr hdr_map) all_fields_zsort;
      let to_string n hdr = 
	(Printf.sprintf "(_ bv%d %d)" (Hashtbl.find (Hashtbl.find hashmap hdr) n) (bitvec_size hdr)) in
      let tInt_to_string = function
        | TSwitch n -> to_string n SSwitch
	| TEthDst n -> to_string n SEthDst
	| TEthType n -> to_string n SEthType
	| TVlan n -> to_string n SVlan
	| TVlanPcp n -> to_string n SVlanPcp
	| TIPProto n -> to_string n SIPProto
	| TIP4Src n -> to_string n SIP4Src
	| TIP4Dst n -> to_string n SIP4Dst
	| TTCPSrcPort n -> to_string n STCPSrcPort
	| TTCPDstPort n -> to_string n STCPDstPort
	| TEthSrc n -> to_string n SEthSrc
	| TInPort n -> to_string n SInPort
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
      | ZIf(tst,thn,els) -> 
	Printf.sprintf "(ite %s %s %s)" (serialize_formula tst) (serialize_formula thn) (serialize_formula els)
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
	| ZDeclareDatatype (name, variants) -> 
	  Printf.sprintf "(declare-datatypes\n()\n((%s %s)))" name
	    (intercalate (fun variant ->  match variant with
	      | variant_name, fields -> 
		Printf.sprintf "(%s %s)" variant_name
		  (intercalate (fun field -> match field with
		    | field_name, field_sort -> Printf.sprintf "(%s %s)" field_name (serialize_sort field_sort)
		   ) " " fields)
	     ) "\n" variants)
	| ZDeclareQuery (q,args) -> 
	  (Printf.sprintf "(query (%s %s) 
:default-relation smt_relation2
:engine PDR
:print-answer false)
" q (intercalate serialize_term " " args))

	| ZDeclareLiteral s -> s


  let assemble_program pervasives prog query = 
    let ZProgram(dcls) = prog in 
    ZProgram (List.flatten [pervasives; dcls; [query]])


  let serialize_program prog: string = 
    let ZProgram(ds) = prog in 
    (intercalate serialize_declare "\n" ds)

    let solve prog: bool * float = 
      let s = (serialize_program prog) in
      let z3_out,z3_in = open_process "z3 -in -smt2 -nw" in 
      let _ = output_string z3_in s in
      let _ = flush z3_in in 
	  let start_time = Unix.gettimeofday () in
      let _ = close_out z3_in in 
      let b = Buffer.create 17 in 
      (try
	 while true do
           Buffer.add_string b (input_line z3_out);
           Buffer.add_char b '\n';
	 done
       with End_of_file -> ());
      Buffer.contents b = "sat\n", (Unix.gettimeofday () -. start_time)

  end
