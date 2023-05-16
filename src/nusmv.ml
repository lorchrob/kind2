(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

   Licensed under the Apache License, Version 2.0 (the "License"); you
   may not use this file except in compliance with the License.  You
   may obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0 

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
   implied. See the License for the specific language governing
   permissions and limitations under the License. 

*)


(* Translator from Lustre to NuSMV input language *)

open Lib

module SVM = StateVar.StateVarMap
module SVS = StateVar.StateVarSet

let init list = list |> List.rev |> List.tl |> List.rev

let contains s1 s2 =
  let re = Str.regexp_string s2
  in
      try ignore (Str.search_forward re s1 0); true
      with Not_found -> false

let string_of_call_variable sv = (*StateVar.string_of_state_var sv *)
  let str = sv |> StateVar.string_of_state_var |> String.split_on_char '-' in
  let str = (if List.length str > 1 then 
              if contains (List.nth str (List.length str - 2)) "call_"
              then init str else str 
            else str) |> String.concat "-" in
  let str = String.split_on_char '_' str in 
  let str = (if List.length str > 2 then 
    if contains (List.nth str (List.length str - 3)) "call"
    then init str else str 
  else str) |> String.concat "_" in
  str

let first_g = ref true
let modules_printed = ref []

(* Pretty-print a symbol in NuSMV format *)
let rec pp_print_nusmv_symbol_node ppf = function

  | `TRUE -> Format.pp_print_string ppf "TRUE"
  | `FALSE -> Format.pp_print_string ppf "FALSE"
  | `NOT -> Format.pp_print_string ppf "!"
  | `IMPLIES -> Format.pp_print_string ppf "->"
  | `AND  -> Format.pp_print_string ppf "&"
  | `OR -> Format.pp_print_string ppf "|"
  | `XOR -> Format.pp_print_string ppf "xor"

  | `EQ -> Format.pp_print_string ppf "="
  (*| `DISTINCT -> Format.pp_print_string ppf ""*)
  (*| `ITE -> Format.pp_print_string ppf "" *)

  | `NUMERAL i -> Numeral.pp_print_numeral ppf i
  | `DECIMAL f -> Decimal.pp_print_decimal ppf f
  (*| `BV b -> pp_print_bitvector_b ppf b *)

  | `MINUS -> Format.pp_print_string ppf "-"
  | `PLUS -> Format.pp_print_string ppf "+"
  | `TIMES -> Format.pp_print_string ppf "*"
  | `DIV -> Format.pp_print_string ppf "/"
  | `INTDIV -> Format.pp_print_string ppf "/"
  | `MOD -> Format.pp_print_string ppf "mod"
  (*| `ABS -> Format.pp_print_string ppf ""*)

  | `LEQ -> Format.pp_print_string ppf "<="
  | `LT -> Format.pp_print_string ppf "<"
  | `GEQ -> Format.pp_print_string ppf ">="
  | `GT -> Format.pp_print_string ppf ">"
  | _ -> Format.pp_print_string ppf "!!"

and pp_print_nusmv_symbol ppf s =
  pp_print_nusmv_symbol_node ppf (Symbol.node_of_symbol s)

let string_of_state_var sv = 
  let str = StateVar.string_of_state_var sv in 
  let strs = String.split_on_char '-' str in
  let strs = ( 
    if List.length strs >= 2 && contains (List.nth strs (List.length strs - 2)) "_call"
    then strs |> List.rev |> List.tl |> List.rev 
    (*else if contains (List.nth strs (List.length strs - 1)) "_call"
          && (List.nth strs (List.length strs - 1)) |> String.split_on_char '_' |> List.length >= 3
    then strs |> List.rev |> List.tl |> List.rev*)
    else strs
  ) in 
  String.concat "-" strs
    



(* Pretty-print a type in NuSMV format *)
let rec pp_print_nusmv_type_node ppf = function

  | Type.Bool -> Format.pp_print_string ppf "boolean"

  (* NuSMV only supports bounded integers *)
  | Type.Int -> Format.pp_print_string ppf "integer"

  | Type.Real -> Format.fprintf ppf "real"                               
  
  | Type.IntRange (i, j, _) -> 
    Format.fprintf
      ppf 
      "%a .. %a" 
      Numeral.pp_print_numeral i 
      Numeral.pp_print_numeral j
  
  (*
  | Real -> Format.pp_print_string ppf "Real"

  | BV i -> 
    Format.fprintf
      ppf 
      "BitVec %a" 
      Numeral.pp_print_numeral i 
  *)
  
  | Type.Array (s, t) -> 
      Format.fprintf
      ppf 
      "array %a of %a" 
      (* need to have a range and a type, ie 'array 0..3 of boolean' *)
      pp_print_nusmv_type_node (Type.node_of_type s) (* print the integer range *)
      pp_print_nusmv_type_node (Type.node_of_type t) (* print the type *)
 
  | t -> 
      Format.fprintf
      ppf
      "unsupported type: %a\n"
      Type.pp_print_type_node t; 
      assert false;

and pp_print_nusmv_type ppf t = 
  pp_print_nusmv_type_node ppf (Type.node_of_type t)

let find_call_in_instance sv { TransSys.map_down = d; } = 
  match SVM.find_opt sv d with 
    (*| Some sv2 -> StateVar.string_of_state_var sv2 
    | _ -> match SVM.find_opt sv d with*)
    | Some sv2 -> Some sv2
    | _ -> None

let find_ret_var_from_ss in_sys sv ss =
  List.fold_left (fun acc ({TransSys.scope = s}, instances) ->
    let node = match InputSystem.get_lustre_node in_sys s with 
      | Some node -> node 
      | None -> failwith "oops"
    in
      List.fold_left (fun acc instance ->
        if acc = "not_found" then 
          let call = find_call_in_instance sv instance in 
          match call with 
            | Some call -> 
              if LustreIndex.exists (fun _ sv -> StateVar.equal_state_vars call sv) node.outputs
                then 
                StateVar.string_of_state_var call
              else "not_found"  
            | None -> "not_found"
        else 
          acc
      ) acc instances
    ) "not_found" ss


(* pretty-print a var *)
let pp_print_nusmv_var ofs ppf term =

  match Term.destruct term with 
    | Term.T.Var v when Numeral.equal ofs (Numeral.of_int 0) ->
      Format.fprintf ppf 
      "%a"
      StateVar.pp_print_state_var (Var.state_var_of_state_var_instance v)

    | Term.T.Var v when Numeral.equal ofs (Numeral.of_int 1) ->
      Format.fprintf
      ppf 
      "next(%a)"
       StateVar.pp_print_state_var (Var.state_var_of_state_var_instance v)

    | Term.T.Var _ -> failwith ("Invalid offset " ^ (Numeral.string_of_numeral ofs)) 

    | _ -> print_endline "\n Error: couldn't print term:\n"; 
           print_endline (Term.string_of_term term); 
           assert false



(* pretty-print a term in nusmv format *)
let rec pp_print_nusmv_term in_sys ss ppf term =
  match Term.destruct term with 

  | Term.T.App (s, l) when s = (Symbol.mk_symbol `PLUS) ->
 
    (match (List.map Term.mk_term (List.map Term.node_of_term l)) with
   
      | [] -> ()
   
      | h::[] ->
        Format.fprintf 
          ppf 
          "%a"
          (pp_print_nusmv_term in_sys ss) h

      | h::t ->
        Format.fprintf 
          ppf 
          "%a + %a"
          (* lhs *)
          (pp_print_nusmv_term in_sys ss) h
          (* rhs *)
          (pp_print_nusmv_term in_sys ss) (Term.mk_plus t) 
    );

  | Term.T.App (s, l) when s = (Symbol.mk_symbol `AND) ->

    (match (List.map Term.mk_term (List.rev (List.map Term.node_of_term l))) with
   
      | [] ->
        Format.fprintf
          ppf
          "%a"
          (pp_print_nusmv_term in_sys ss) (Term.mk_false ())
   
      | [t] ->
        Format.fprintf 
          ppf 
          "%a"
          (pp_print_nusmv_term in_sys ss) t
    
      | h::t ->
        Format.fprintf 
          ppf 
          "(%a & %a)"
          (pp_print_nusmv_term in_sys ss) (Term.mk_and (List.rev t))
          (pp_print_nusmv_term in_sys ss) h);

   | Term.T.App (s, l) when s = (Symbol.mk_symbol `OR) ->

    (match (List.map Term.mk_term (List.rev (List.map Term.node_of_term l))) with
    
      | [] ->
        Format.fprintf
          ppf
          "%a"
          (pp_print_nusmv_term in_sys ss) (Term.mk_false ())
    
      | [t] ->
        Format.fprintf 
          ppf 
          "%a"
          (pp_print_nusmv_term in_sys ss) t
      
      | h::t ->
        Format.fprintf 
          ppf 
          "(%a | %a)"
          (* lhs *)
          (pp_print_nusmv_term in_sys ss) h
          (* rhs *)
          (pp_print_nusmv_term in_sys ss) (Term.mk_or t));

  | Term.T.App (s, l) when s = (Symbol.mk_symbol `IMPLIES) ->
    
    (match (List.map Term.mk_term (List.map Term.node_of_term l)) with
      | [] ->
        Format.fprintf
          ppf
          "%a"
          (* Implication is a disjunction, empty implication is false *)
          (pp_print_nusmv_term in_sys ss) (Term.mk_false ())
 
      | [t] ->
        Format.fprintf 
          ppf 
          "%a"
          (* An implication without premises is true if the conclusion is true *)
          (pp_print_nusmv_term in_sys ss) t

      | h::t ->
        Format.fprintf 
          ppf 
          "(%a -> %a)"
          (* lhs *)
          (pp_print_nusmv_term in_sys ss) h
          (* rhs *)
          (pp_print_nusmv_term in_sys ss) (Term.mk_implies t) 
    );

  | Term.T.App (s, l) when s = (Symbol.mk_symbol `LEQ) ->

    (match (List.map Term.mk_term (List.map Term.node_of_term l)) with
  
      | [] -> ()
  
      | [h] ->
        Format.fprintf 
          ppf 
          "%a"
          (* lhs *)
          (pp_print_nusmv_term in_sys ss) h
  
      | h::t::[] ->
        Format.fprintf 
          ppf 
          "%a <= %a"
          (* lhs *)
          (pp_print_nusmv_term in_sys ss) h
          (* rhs *)
          (pp_print_nusmv_term in_sys ss) t 
      | h::t ->
        Format.fprintf 
          ppf 
          "%a <= %a"
          (* lhs *)
          (pp_print_nusmv_term in_sys ss) h
          (* rhs *)
          (pp_print_nusmv_term in_sys ss) (Term.mk_leq t) 
    );

  | Term.T.App (s, l) when s = (Symbol.mk_symbol `GEQ) ->

    (match (List.map Term.mk_term (List.map Term.node_of_term l)) with

      | [] -> ()

      | h::[] ->
        Format.fprintf 
          ppf 
          "%a"
          (pp_print_nusmv_term in_sys ss) h

      | h::t::[] ->
        Format.fprintf 
          ppf 
          "%a >= %a"
          (* lhs *)
          (pp_print_nusmv_term in_sys ss) h
          (* rhs *)
          (pp_print_nusmv_term in_sys ss) t 

      | h::t ->
        Format.fprintf 
          ppf 
          "%a >= %a"
          (* lhs *)
          (pp_print_nusmv_term in_sys ss) h
          (* rhs *)
          (pp_print_nusmv_term in_sys ss) (Term.mk_geq t) 
    );

  | Term.T.App (s, l) -> 

    (match (List.map Term.mk_term (List.map Term.node_of_term l)) with
     
     | [cond; cons; alt] ->
        (match (Symbol.node_of_symbol s) with 

         | `ITE ->
          (* if then else *)
          Format.fprintf 
          ppf 
          "(%a ? %a : %a)"
          (* condition *)
          (pp_print_nusmv_term in_sys ss) cond
          (* consequent *)
          (pp_print_nusmv_term in_sys ss) cons
          (* alternative *) 
          (pp_print_nusmv_term in_sys ss) alt
         
         | s ->

          Format.fprintf 
          ppf 
          "invalid symbol: %a"
          Symbol.pp_print_symbol (Symbol.mk_symbol s);
          assert false;

        );

      | [lhs; rhs] -> 
        Format.fprintf 
        ppf 
        "(%a %a %a)" 
        (* print left hand side *)
        (pp_print_nusmv_term in_sys ss) lhs
        (* print symbol *)
        pp_print_nusmv_symbol s 
        (* print right hand side *)
        (pp_print_nusmv_term in_sys ss) rhs

     | [t] -> 
        pp_print_nusmv_symbol ppf s;
        (pp_print_nusmv_term in_sys ss) ppf t
    
     | [ ] -> ()

     | _ -> ()
        (*Format.fprintf 
        ppf 
        "invalid term 1 %a" 
        Term.pp_print_term term
        assert false;*)
        
    );

  | Term.T.Const s -> pp_print_nusmv_symbol ppf s

  (*!! If the variable is a node call value, include node call return variable with dot notation !!*)
  (*!!! Make sure dot notation is a return value !!!*)
  (*!!!! Update string of call variable *)
  | Term.T.Var v when Var.is_state_var_instance v && contains ( Var.string_of_var v) "call_" -> 
    let sv = Var.state_var_of_state_var_instance v in
    let node_call_variable = find_ret_var_from_ss in_sys sv ss in
    let str = string_of_call_variable sv in

    let cond = Var.is_state_var_instance v && (Var.offset_of_state_var_instance v) == Numeral.one in
    if cond then
      Format.fprintf ppf "next(%s)" (String.concat "." [str; node_call_variable]);
    if not cond then 
      Format.fprintf ppf "%s" (String.concat "." [str; node_call_variable]);



  | Term.T.Var v when not (contains (Var.string_of_var v) "res-inst") -> 
    if Var.is_state_var_instance v then  
      pp_print_nusmv_var (Var.offset_of_state_var_instance v) ppf term
    else
      Format.fprintf ppf "%s" (Var.string_of_var v)
  | _ -> Format.fprintf ppf "TRUE"


(* Pretty-print a scope *)
let pp_print_scope ppf s =
  Format.fprintf 
    ppf
    "%a"
    (pp_print_list Ident.pp_print_ident "-")
    s

let gather_node_args_from_instance in_sys ss sv u = 
  let pairs = SVM.bindings u in 
  let svs = List.map snd pairs |> 
    (* Filter out node arguments that shouldn't be present *)
    List.filter (fun sv2 -> 
      let sv_short =  StateVar.string_of_state_var sv in 
      let sv2_short = StateVar.string_of_state_var sv2 in
      let sv_short1 = 
        if contains sv_short "_" then 
          sv_short |> String.split_on_char '_' |> init |> String.concat "_" 
        else sv_short
      in
      let sv2_short1 = 
        if contains sv2_short "_" then
          sv2_short |> String.split_on_char '_' |> init |> String.concat "_" 
        else sv2_short
      in
      let cond = 
        if contains sv_short "-" && contains sv2_short "-" then 
          let list1 = sv_short |> String.split_on_char '-' in 
          let list2 = sv2_short |> String.split_on_char '-' in 
          not (List.exists (fun word -> contains word "call_" && List.exists (fun word2 -> word2 = word) list2) list1)
        else true
      in
      let cond2 = 
        try (
          (*not (contains sv_short "call_[0-9]+" && contains sv2_short "call_[0-9]+")*)
          let _ = Str.search_forward (Str.regexp {|call_\([0-9]+\)|}) sv_short 0 in 
          let call = Str.matched_string sv_short in 
          let _ = Str.search_forward (Str.regexp {|call_\([0-9]+\)|}) sv2_short 0 in 
          let call2 = Str.matched_string sv2_short in 
          call <> call2
        )
        with | _ -> true
      in
      not (
        (contains sv_short1 "call_") &&
        (contains sv2_short1 "call_") &&
        (contains sv_short1 sv2_short1) && 
        (contains sv2_short1 sv_short1)
      ) &&
      cond && cond2 &&
      (not (contains (string_of_state_var sv) (string_of_state_var sv2)))
    ) 
  in
  let node_name = StateVar.string_of_state_var (fst (List.hd pairs)) in
  let node_name = List.hd (String.split_on_char '-' node_name) in
  let strings = List.map (fun sv -> 
    if contains (StateVar.string_of_state_var sv) "call_" then 
      let node_call_variable = find_ret_var_from_ss in_sys sv ss in
      let str = string_of_call_variable sv in
      String.concat "." [str; node_call_variable]
    else StateVar.string_of_state_var sv) svs
  in
  let strings = List.filter (fun str -> not (contains str "inst_")) strings in
  let strings = List.filter (fun str -> not (contains str "poracle")) strings in
  node_name ^ "(" ^ (String.concat ", " strings) ^ ")"

let nusmv_call_str in_sys ss sv = 
    List.fold_left (fun acc ({TransSys.scope = s}, maps) -> 
      let node = match InputSystem.get_lustre_node in_sys s with 
            | Some node -> node 
            | None -> failwith "oops"
      in
      List.fold_left (fun acc { TransSys.map_up = u; TransSys.map_down = d; } ->
      match SVM.find_opt sv d with 
        (*| Some _ -> gather_node_args_from_instance sv u
        | None -> match SVM.find_opt sv d with *)
        | Some sv2 -> 
          (*!!! Check if the returned statevar is an output variable !!!*)
          if LustreIndex.exists (fun _ sv -> StateVar.equal_state_vars sv2 sv) node.outputs
          then gather_node_args_from_instance in_sys ss sv u
          else acc
        | None -> acc 
      ) acc maps
    ) "" ss

let rec pp_print_nusmv_var_declarations decls in_sys ss ppf svs = match svs with 
  | [] -> () ;
  | sv :: svs ->
  if not (contains (StateVar.string_of_state_var sv) "call_")
    && not (contains (StateVar.string_of_state_var sv) "res-inst")
    && not (contains (StateVar.string_of_state_var sv) "init_flag")
    then (
  Format.fprintf 
    ppf 
    "\t%a : %a;\n" 
    StateVar.pp_print_state_var sv
    pp_print_nusmv_type (StateVar.type_of_state_var sv)
    );
  (*!! If sv is a node call, print the call instead of the type !!*)
  (*!!!! Update string of call variable *)
  if (contains (StateVar.string_of_state_var sv) "call_") 
    && not (contains (StateVar.string_of_state_var sv) "res-inst")
    && not (contains (StateVar.string_of_state_var sv) "init_flag")
    && not (List.mem (string_of_call_variable sv) decls)
  then (
    Format.fprintf 
    ppf 
    "\t%s : %s;\n" 
    (string_of_call_variable sv)
    (nusmv_call_str in_sys ss sv)
  );
  pp_print_nusmv_var_declarations ((string_of_call_variable sv)::decls) in_sys ss ppf svs

let rec pp_print_nusmv_invars ss ppf init = 
  match init with 

  | [] -> ()

  | h :: tl -> 
    match Term.destruct h with 
      | Term.T.App (s, l) when Symbol.equal_symbols s Symbol.s_and -> 
      (*print_endline "and call";*)
      (pp_print_nusmv_invars ss) ppf ((List.map Term.mk_term (List.map Term.node_of_term l)) @ tl)

      | Term.T.Var v when contains (Var.string_of_var v) "init_flag" -> (); 
        (pp_print_nusmv_invars ss) ppf tl
 
      | Term.T.Var v when Var.type_of_var v == Type.t_bool -> 
        let var_str = (List.hd (String.split_on_char '@' (Var.string_of_var v))) in
        Format.fprintf ppf "\tINVAR %s;\n" 
        var_str;

        (pp_print_nusmv_invars ss) ppf tl

      | _ -> (); (pp_print_nusmv_invars ss) ppf tl


let rec pp_print_nusmv_init in_sys ss ppf init = 
  match init with 

  | [] -> ()

  | h :: tl -> 
    (*print_endline ("printing init: " ^ (Term.string_of_term h));*)
    match Term.destruct h with 
      
      | Term.T.App (s, l) when Symbol.equal_symbols s Symbol.s_and -> 
        (*print_endline "and call";*)
        (pp_print_nusmv_init in_sys ss) ppf ((List.map Term.mk_term (List.map Term.node_of_term l)) @ tl)

      | Term.T.App (s, [l; r]) when Symbol.equal_symbols s (Symbol.mk_symbol `EQ) && 
                                    not (contains (Term.string_of_term l) "init_flag") -> 
        let _ = Simplify.simplify_term [] (Term.mk_term (Term.node_of_term r)) in
        (*Format.fprintf ppf "GOT PAST SIMPLIFICATION@.";*)
        Format.fprintf ppf "\tinit(%a) := %a;\n" 
          (pp_print_nusmv_var (Numeral.of_int 0)) (Term.mk_term (Term.node_of_term l)) 
          (pp_print_nusmv_term in_sys ss) (Term.mk_term (Term.node_of_term r));
        
          

        (pp_print_nusmv_init in_sys ss) ppf tl

      | Term.T.App (s, [l]) when Symbol.equal_symbols s (Symbol.mk_symbol `NOT) -> 

          Format.fprintf ppf "\tinit(%a) := %s;\n" 
            (pp_print_nusmv_var (Numeral.of_int 0)) (Term.mk_term (Term.node_of_term l)) 
            "FALSE";
          
          (pp_print_nusmv_init in_sys ss) ppf tl

      | Term.T.Var v when contains (Var.string_of_var v) "init_flag" -> 
        ();

        (pp_print_nusmv_init in_sys ss) ppf tl

      | Term.T.Var v when Var.type_of_var v == Type.t_bool -> ();
        (*let var_str = (List.hd (String.split_on_char '@' (Var.string_of_var v))) in
        Format.fprintf ppf "\tINVAR %s;\n" 
        var_str;*)

        (pp_print_nusmv_init in_sys ss) ppf tl

      | _ when (String.starts_with ~prefix:"(__node_" (Term.string_of_term h)) -> ()

      | _ -> ()
        (*Format.fprintf 
        ppf 
        "-- invalid term 2 %a" 
        Term.pp_print_term h
        assert false*)

let rec pp_print_nusmv_constr in_sys ss ppf constr = 
  match constr with 

  | [] -> ()

  | h :: tl -> 
    (*print_endline ("printing next: " ^ (Term.string_of_term h));*)
    match Term.destruct h with 
      | Term.T.App (s, l) when Symbol.equal_symbols s Symbol.s_and -> 
        (pp_print_nusmv_constr in_sys ss) ppf ((List.map Term.mk_term (List.map Term.node_of_term l)) @ tl)

      | Term.T.App (s, [l; r]) when Symbol.equal_symbols s (Symbol.mk_symbol `EQ) && 
      not (contains (Term.string_of_term l) "init_flag")-> 
        Format.fprintf ppf "\tnext(%a) := %a;\n" 
          (pp_print_nusmv_var (Numeral.of_int 0)) (Term.mk_term (Term.node_of_term l)) 
          (pp_print_nusmv_term in_sys ss) (Term.mk_term (Term.node_of_term r));
        
        (pp_print_nusmv_constr in_sys ss) ppf tl

      | Term.T.App (s, [_]) when Symbol.equal_symbols s (Symbol.mk_symbol `NOT) -> 
       ();
        (pp_print_nusmv_constr in_sys ss) ppf tl

      | Term.T.Var v when contains (Var.string_of_var v) "init_flag" -> 
        ();
        (pp_print_nusmv_constr in_sys ss) ppf tl

      | Term.T.Var v when Var.type_of_var v == Type.t_bool -> ()

      | _ when (String.starts_with ~prefix:"(__node_" (Term.string_of_term h)) -> ()

      | _ -> ()
        (*Format.fprintf 
        ppf 
        "-- invalid term 3 %a" 
        Term.pp_print_term h
        assert false*)



let pp_print_nusmv_prop in_sys ss ppf {Property.prop_term = t;} =
  (*print_endline (Term.string_of_term t);*)
  Format.fprintf
  ppf
  "@[<hv 1>(%a)@]"
  (pp_print_nusmv_term in_sys ss) t


let rec pp_print_nusmv_trans_sys in_sys first ppf { 
                                   TransSys.scope = s;
                                   TransSys.init = i; 
                                   (*TransSys.unconstrained_inputs = ui;*)
                                   TransSys.state_vars = svs;
                                   (*TransSys.constr = c; *)
                                   TransSys.trans = g; 
                                   TransSys.properties = p;
                                   TransSys.subsystems = ss;
                                   (*TransSys.invariants = pv;*)
                                   (*TransSys.props_invalid = pi*)  
                                   } =

  List.iter (pp_print_nusmv_trans_sys in_sys false ppf) (List.map fst ss);

  if (not first) && (not (List.mem s !modules_printed)) then (
    let node = match InputSystem.get_lustre_node in_sys s with 
            | Some node -> node 
            | None -> failwith "oops"
    in
    let args = 
      LustreIndex.values node.inputs
    in
    let arg_set = SVS.of_list args in
    modules_printed := s :: !modules_printed;
  (Format.fprintf 
    ppf
    "\nMODULE %a (%a)\nVAR@\n@[<v>%a@]@\nASSIGN@\n@[<v>%a@]@[<v>%a@]@[<v>%a@]@\n"
    pp_print_scope s
    (pp_print_list StateVar.pp_print_state_var ", ") args
    (pp_print_nusmv_var_declarations [] in_sys ss) (SVS.elements (SVS.diff (SVS.of_list svs) arg_set))
    (pp_print_nusmv_init in_sys ss) [i]
    (pp_print_nusmv_constr in_sys ss) [g]
    (pp_print_nusmv_invars ss) [i]
  );
  );

  if first && (not (List.mem s !modules_printed)) then (
    modules_printed := s :: !modules_printed;
    (Format.fprintf 
      ppf
      "\nMODULE %s () \nVAR@\n@[<v>%a@]@\nASSIGN@\n@[<v>%a@]@[<v>%a@]@[<v>%a@]@\n"
      "main"
      (pp_print_nusmv_var_declarations [] in_sys ss) (SVS.elements ((SVS.of_list svs)))
      (pp_print_nusmv_init in_sys ss) [i]
      (pp_print_nusmv_constr in_sys ss) [g]
      (pp_print_nusmv_invars ss) [i]
    );
  if (p <> []) then (
    Format.fprintf
      ppf 
      "INVARSPEC @\n(@[<v>%a@]);\n"
      (pp_print_list (pp_print_nusmv_prop in_sys ss) " & ") p;
    );
  );

  first_g := false;

  




(* Entry Point *)
(*
let rec parse_argv argv fn = 
  match argv with
  | h1::h2::tl ->
    (match h1 with
      | "--int-lowerbound" ->
        int_lowerbound := (int_of_string h2);
        parse_argv tl fn;
      
      | "--int-upperbound" ->
        int_upperbound := (int_of_string h2);
        parse_argv tl fn;
      
      | _                  -> 
        if (fn <> "") then (
          print_endline help_message;
          assert false;
        ) else (
          parse_argv (h2::tl) h1;
        )
    )
  
  | h::tl ->
    (match h, fn with
      | "--help", "" ->
        print_endline help_message;
        exit 0;
      | h, ""       ->
        h;
      | _, _        ->
        print_endline help_message;
        exit 1;
    )

  | [] -> fn
*)
(*
match parse_argv (Array.to_list (Array.sub Sys.argv 1 ((Array.length Sys.argv) - 1))) "" with
| "" -> 
  let ts = OldParser.of_channel stdin in
  pp_print_nusmv_trans_sys in_sys Format.std_formatter ts;
| fn ->
  let ts = OldParser.of_file fn in
  pp_print_nusmv_trans_sys in_sys Format.std_formatter ts;
*)
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
