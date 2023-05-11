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

let contains s1 s2 =
  let re = Str.regexp_string s2
  in
      try ignore (Str.search_forward re s1 0); true
      with Not_found -> false

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
  (*| `DIV -> Format.pp_print_string ppf ""*)
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
    | Some sv2 -> StateVar.string_of_state_var sv2
    | _ -> "not_found"

let find_ret_var_from_ss node_name sv instances =
  List.fold_left (fun acc instance ->
      if acc = "not_found" then 
        let call = find_call_in_instance sv instance in 
        if String.starts_with ~prefix:node_name call then 
          "not_found"
        else call  
      else 
        acc
    ) "not_found" instances


(* pretty-print a var *)
let pp_print_nusmv_var ofs ppf term =

  match Term.destruct term with 
    | Term.T.Var v when Numeral.equal ofs (Numeral.of_int 0) ->
      StateVar.pp_print_state_var ppf (Var.state_var_of_state_var_instance v)

    | Term.T.Var v when Numeral.equal ofs (Numeral.of_int 1) ->
      Format.fprintf
      ppf 
      "next(%a)"
       StateVar.pp_print_state_var (Var.state_var_of_state_var_instance v)

    | Term.T.Var _ -> failwith ("Invalid offset " ^ (Numeral.string_of_numeral ofs)) 

    (*!! If printing a node call, include node call parameters !!*)

    | _ -> print_endline "\n Error: couldn't print term:\n"; 
           print_endline (Term.string_of_term term); 
           assert false



(* pretty-print a term in nusmv format *)
let rec pp_print_nusmv_term ss ppf term =
  
  match Term.destruct term with 

  | Term.T.App (s, l) when s = (Symbol.mk_symbol `PLUS) ->
 
    (match (List.map Term.mk_term (List.map Term.node_of_term l)) with
   
      | [] -> ()
   
      | h::[] ->
        Format.fprintf 
          ppf 
          "%a"
          (pp_print_nusmv_term ss) h

      | h::t ->
        Format.fprintf 
          ppf 
          "%a + %a"
          (* lhs *)
          (pp_print_nusmv_term ss) h
          (* rhs *)
          (pp_print_nusmv_term ss) (Term.mk_plus t) 
    );

  | Term.T.App (s, l) when s = (Symbol.mk_symbol `AND) ->

    (match (List.map Term.mk_term (List.rev (List.map Term.node_of_term l))) with
   
      | [] ->
        Format.fprintf
          ppf
          "%a"
          (pp_print_nusmv_term ss) (Term.mk_false ())
   
      | [t] ->
        Format.fprintf 
          ppf 
          "%a"
          (pp_print_nusmv_term ss) t
    
      | h::t ->
        Format.fprintf 
          ppf 
          "(%a & %a)"
          (pp_print_nusmv_term ss) (Term.mk_and (List.rev t))
          (pp_print_nusmv_term ss) h);

   | Term.T.App (s, l) when s = (Symbol.mk_symbol `OR) ->

    (match (List.map Term.mk_term (List.rev (List.map Term.node_of_term l))) with
    
      | [] ->
        Format.fprintf
          ppf
          "%a"
          (pp_print_nusmv_term ss) (Term.mk_false ())
    
      | [t] ->
        Format.fprintf 
          ppf 
          "%a"
          (pp_print_nusmv_term ss) t
      
      | h::t ->
        Format.fprintf 
          ppf 
          "(%a | %a)"
          (* lhs *)
          (pp_print_nusmv_term ss) h
          (* rhs *)
          (pp_print_nusmv_term ss) (Term.mk_or t));

  | Term.T.App (s, l) when s = (Symbol.mk_symbol `IMPLIES) ->
    
    (match (List.map Term.mk_term (List.map Term.node_of_term l)) with
      | [] ->
        Format.fprintf
          ppf
          "%a"
          (* Implication is a disjunction, empty implication is false *)
          (pp_print_nusmv_term ss) (Term.mk_false ())
 
      | [t] ->
        Format.fprintf 
          ppf 
          "%a"
          (* An implication without premises is true if the conclusion is true *)
          (pp_print_nusmv_term ss) t

      | h::t ->
        Format.fprintf 
          ppf 
          "(%a -> %a)"
          (* lhs *)
          (pp_print_nusmv_term ss) h
          (* rhs *)
          (pp_print_nusmv_term ss) (Term.mk_implies t) 
    );

  | Term.T.App (s, l) when s = (Symbol.mk_symbol `LEQ) ->

    (match (List.map Term.mk_term (List.map Term.node_of_term l)) with
  
      | [] -> ()
  
      | [h] ->
        Format.fprintf 
          ppf 
          "%a"
          (* lhs *)
          (pp_print_nusmv_term ss) h
  
      | h::t::[] ->
        Format.fprintf 
          ppf 
          "%a <= %a"
          (* lhs *)
          (pp_print_nusmv_term ss) h
          (* rhs *)
          (pp_print_nusmv_term ss) t 
      | h::t ->
        Format.fprintf 
          ppf 
          "%a <= %a"
          (* lhs *)
          (pp_print_nusmv_term ss) h
          (* rhs *)
          (pp_print_nusmv_term ss) (Term.mk_leq t) 
    );

  | Term.T.App (s, l) when s = (Symbol.mk_symbol `GEQ) ->

    (match (List.map Term.mk_term (List.map Term.node_of_term l)) with

      | [] -> ()

      | h::[] ->
        Format.fprintf 
          ppf 
          "%a"
          (pp_print_nusmv_term ss) h

      | h::t::[] ->
        Format.fprintf 
          ppf 
          "%a >= %a"
          (* lhs *)
          (pp_print_nusmv_term ss) h
          (* rhs *)
          (pp_print_nusmv_term ss) t 

      | h::t ->
        Format.fprintf 
          ppf 
          "%a >= %a"
          (* lhs *)
          (pp_print_nusmv_term ss) h
          (* rhs *)
          (pp_print_nusmv_term ss) (Term.mk_leq t) 
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
          (pp_print_nusmv_term ss) cond
          (* consequent *)
          (pp_print_nusmv_term ss) cons
          (* alternative *) 
          (pp_print_nusmv_term ss) alt
         
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
        (pp_print_nusmv_term ss) lhs
        (* print symbol *)
        pp_print_nusmv_symbol s 
        (* print right hand side *)
        (pp_print_nusmv_term ss) rhs

     | [t] -> 
        pp_print_nusmv_symbol ppf s;
        (pp_print_nusmv_term ss) ppf t
    
     | [ ] -> ()

     | _ -> 
        Format.fprintf 
        ppf 
        "invalid term 1 %a" 
        Term.pp_print_term term
        (*assert false;*)
        
    );

  | Term.T.Const s -> pp_print_nusmv_symbol ppf s

  (*!! If the variable is a node call value, include node call return variable with dot notation !!*)
  | Term.T.Var v when Var.is_state_var_instance v && contains ( Var.string_of_var v) "call_" -> 
    let sv = Var.state_var_of_state_var_instance v in

    let instances = List.map snd ss |> List.flatten in
    let pairs = List.map (fun { TransSys.map_down=d; } -> SVM.bindings d) instances |> List.flatten in
    let node_name = StateVar.string_of_state_var (fst (List.hd pairs)) in
    let node_name = List.hd (String.split_on_char '-' node_name) in
    let node_call_variable = find_ret_var_from_ss node_name sv instances in
    let str = StateVar.string_of_state_var sv in
    Format.fprintf ppf "%s" (String.concat "." [str; node_call_variable])

  | Term.T.Var v -> 
    if Var.is_state_var_instance v then  
      pp_print_nusmv_var (Var.offset_of_state_var_instance v) ppf term
    else
      Var.print_var v


(* Pretty-print a scope *)
let pp_print_scope ppf s =
  Format.fprintf 
    ppf
    "%a"
    (pp_print_list Ident.pp_print_ident "-")
    s

let gather_node_args_from_instance ss sv u = 
  let pairs = SVM.bindings u in 
  let svs = List.map snd pairs |> 
    List.filter (fun sv2 -> not (contains (string_of_state_var sv) (string_of_state_var sv2))) in
    (*List.filter (fun sv2 -> sv <> sv2) in*)
  let node_name = StateVar.string_of_state_var (fst (List.hd pairs)) in
  let node_name = List.hd (String.split_on_char '-' node_name) in
  let instances = List.map snd ss |> List.flatten in
  let strings = List.map (fun sv -> 
    if contains (StateVar.string_of_state_var sv) "call_" then 
      let node_call_variable = find_ret_var_from_ss node_name sv instances in
      let str = StateVar.string_of_state_var sv in
      String.concat "." [str; node_call_variable]
    else StateVar.string_of_state_var sv) svs
  in
  let strings = List.filter (fun str -> not (contains str "inst_")) strings in
  node_name ^ "(" ^ (String.concat ", " strings) ^ ")"

let nusmv_call_str ss sv = 
    let instances = List.map snd ss |> List.flatten in
    List.fold_left (fun acc { TransSys.map_up = u; TransSys.map_down = d; } -> 
      match SVM.find_opt sv d with 
        (*| Some _ -> gather_node_args_from_instance sv u
        | None -> match SVM.find_opt sv d with *)
        | Some _ -> gather_node_args_from_instance ss sv u
        | None -> acc 
    ) "" instances

let pp_print_nusmv_var_declaration ss ppf sv =
  if not (contains (StateVar.string_of_state_var sv) "call_")
    && not (contains (StateVar.string_of_state_var sv) "res-inst")
    && not (contains (StateVar.string_of_state_var sv) "init_flag")
    then  
  Format.fprintf 
    ppf 
    "\t%a : %a;" 
    StateVar.pp_print_state_var sv
    pp_print_nusmv_type (StateVar.type_of_state_var sv);
  (*!! If sv is a node call, print the call instead of the type !!*)
  if (contains (StateVar.string_of_state_var sv) "call_") 
    && not (contains (StateVar.string_of_state_var sv) "res-inst")
    && not (contains (StateVar.string_of_state_var sv) "init_flag")
  then
    Format.fprintf 
    ppf 
    "\t%s : %s;" 
    (string_of_state_var sv)
    (nusmv_call_str ss sv)

let rec pp_print_nusmv_invars ss ppf init = 
  match init with 

  | [] -> ()

  | h :: tl -> 
    match Term.destruct h with 
      | Term.T.Var v when contains (Var.string_of_var v) "init_flag" -> (); 
        (pp_print_nusmv_invars ss) ppf tl
 
      | Term.T.Var v when Var.type_of_var v == Type.t_bool -> 
        let var_str = (List.hd (String.split_on_char '@' (Var.string_of_var v))) in
        Format.fprintf ppf "\tINVAR %s;\n" 
        var_str;

        (pp_print_nusmv_invars ss) ppf tl

      | _ -> ()

let rec pp_print_nusmv_init ss ppf init = 
  match init with 

  | [] -> ()

  | h :: tl -> 
    (*print_endline ("printing init: " ^ (Term.string_of_term h));*)
    match Term.destruct h with 
      
      | Term.T.App (s, l) when Symbol.equal_symbols s Symbol.s_and -> 
        (*print_endline "and call";*)
        (pp_print_nusmv_init ss) ppf ((List.map Term.mk_term (List.map Term.node_of_term l)) @ tl)

      | Term.T.App (s, [l; r]) when Symbol.equal_symbols s (Symbol.mk_symbol `EQ) && 
                                    not (contains (Term.string_of_term l) "init_flag") -> 

        Format.fprintf ppf "\tinit(%a) := %a;\n" 
          (pp_print_nusmv_var (Numeral.of_int 0)) (Term.mk_term (Term.node_of_term l)) 
          (pp_print_nusmv_term ss) (Term.mk_term (Term.node_of_term r));
        
        (pp_print_nusmv_init ss) ppf tl

      | Term.T.App (s, [l]) when Symbol.equal_symbols s (Symbol.mk_symbol `NOT) -> 

          Format.fprintf ppf "\tinit(%a) := %s;\n" 
            (pp_print_nusmv_var (Numeral.of_int 0)) (Term.mk_term (Term.node_of_term l)) 
            "FALSE";
          
          (pp_print_nusmv_init ss) ppf tl

      | Term.T.Var v when contains (Var.string_of_var v) "init_flag" -> 
        ();

        (pp_print_nusmv_init ss) ppf tl

      | Term.T.Var v when Var.type_of_var v == Type.t_bool -> 
        let var_str = (List.hd (String.split_on_char '@' (Var.string_of_var v))) in
        Format.fprintf ppf "\tINVAR %s;\n" 
        var_str;

        (pp_print_nusmv_init ss) ppf tl

      | _ when (String.starts_with ~prefix:"(__node_" (Term.string_of_term h)) -> ()

      | _ -> 
        Format.fprintf 
        ppf 
        "-- invalid term 2 %a" 
        Term.pp_print_term h
        (*assert false*)

let rec pp_print_nusmv_constr ss ppf constr = 
  match constr with 

  | [] -> ()

  | h :: tl -> 
    (*print_endline ("printing next: " ^ (Term.string_of_term h));*)
    match Term.destruct h with 
      | Term.T.App (s, l) when Symbol.equal_symbols s Symbol.s_and -> 
        (pp_print_nusmv_constr ss) ppf ((List.map Term.mk_term (List.map Term.node_of_term l)) @ tl)

      | Term.T.App (s, [l; r]) when Symbol.equal_symbols s (Symbol.mk_symbol `EQ) && 
      not (contains (Term.string_of_term l) "init_flag")-> 
        Format.fprintf ppf "\tnext(%a) := %a;\n" 
          (pp_print_nusmv_var (Numeral.of_int 0)) (Term.mk_term (Term.node_of_term l)) 
          (pp_print_nusmv_term ss) (Term.mk_term (Term.node_of_term r));
        
        (pp_print_nusmv_constr ss) ppf tl

      | Term.T.App (s, [l]) when Symbol.equal_symbols s (Symbol.mk_symbol `NOT) -> 

        Format.fprintf ppf "\tnext(%a) := %s;\n" 
          (pp_print_nusmv_var (Numeral.of_int 0)) (Term.mk_term (Term.node_of_term l)) 
          "FALSE";
        
        (pp_print_nusmv_constr ss) ppf tl

      | Term.T.Var v when contains (Var.string_of_var v) "init_flag" -> 
        ();

        (pp_print_nusmv_constr ss) ppf tl

      | Term.T.Var v when Var.type_of_var v == Type.t_bool -> ()

      | _ when (String.starts_with ~prefix:"(__node_" (Term.string_of_term h)) -> ()

      | _ -> 
        Format.fprintf 
        ppf 
        "-- invalid term 3 %a" 
        Term.pp_print_term h
        (*assert false*)



let pp_print_nusmv_prop ss ppf {Property.prop_term = t;} =
  (*print_endline (Term.string_of_term t);*)
  Format.fprintf
  ppf
  "@[<hv 1>(%a)@]"
  (pp_print_nusmv_term ss) t


let rec pp_print_nusmv_trans_sys first ppf { 
                                   TransSys.scope = s;
                                   TransSys.init = i; 
                                   TransSys.unconstrained_inputs = ui;
                                   TransSys.state_vars = svs;
                                   (*TransSys.constr = c; *)
                                   TransSys.trans = g; 
                                   TransSys.properties = p;
                                   TransSys.subsystems = ss;
                                   (*TransSys.invariants = pv;*)
                                   (*TransSys.props_invalid = pi*)  
                                   } =

  let ss = List.rev ss in
  List.iter (pp_print_nusmv_trans_sys false ppf) (List.map fst ss);

  if (not first) && (not (List.mem s !modules_printed)) then (
  (Format.fprintf 
    ppf
    "\nMODULE %a (%a)\nVAR@\n@[<v>%a@]@\nASSIGN@\n@[<v>%a@]@[<v>%a@]@[<v>%a@]@\n"
    pp_print_scope s
    (pp_print_list StateVar.pp_print_state_var ", ") (SVS.elements ui)
    (pp_print_list (pp_print_nusmv_var_declaration ss) "@ ") (SVS.elements (SVS.diff (SVS.of_list svs) ui))
    (pp_print_nusmv_init ss) [i]
    (pp_print_nusmv_constr ss) [g]
    (pp_print_nusmv_invars ss) [i]
  );
    modules_printed := s :: !modules_printed;
  );

  if first && (not (List.mem s !modules_printed)) then (
    (Format.fprintf 
      ppf
      "\nMODULE %s () \nVAR@\n@[<v>%a@]@\nASSIGN@\n@[<v>%a@]@[<v>%a@]@[<v>%a@]@\n"
      "main"
      (pp_print_list (pp_print_nusmv_var_declaration ss) "@ ") (SVS.elements ((SVS.of_list svs)))
      (pp_print_nusmv_init ss) [i]
      (pp_print_nusmv_constr ss) [g]
      (pp_print_nusmv_invars ss) [i]
    );

  modules_printed := s :: !modules_printed;

  if (p <> []) then (
    Format.fprintf
      ppf 
      "INVARSPEC @\n(@[<v>%a@]);\n"
      (pp_print_list (pp_print_nusmv_prop ss) " & ") p;
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
  pp_print_nusmv_trans_sys Format.std_formatter ts;
| fn ->
  let ts = OldParser.of_file fn in
  pp_print_nusmv_trans_sys Format.std_formatter ts;
*)
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
