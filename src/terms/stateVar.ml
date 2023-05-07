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

open Lib
open Lib.ReservedIds


(* ********************************************************************* *)
(* Types and hash-consing                                                *)
(* ********************************************************************* *)


(* State variable to be hash-consed

   Name of a state variable is a string with a list of strings as
   its scope *)
type state_var = string * string list 

(* A private type that cannot be constructed outside this module

   This is necessary to ensure the invariant that all subterms of a
   term are hashconsed. We can construct and thus pattern match on the
   {!state_var} type, but not on the {!state_var_node} type *)
type state_var_node = state_var


(* Properties of a state variable

   Only keep essential properties here that are shared by all
   modules. For local properties use a hashtable in the respective
   module. *)
type state_var_prop = 

  { 

    (* The type of the variable: can be changed later if we find out
       that it's not general enough (e.g. subranges) *)
    mutable var_type : Type.t;

    (* The uninterpreted symbol associated with the variable *)
    uf_symbol : UfSymbol.t;

    (* State variable is a non-deterministic input *)
    is_input : bool;

    (* State variable is constant *)
    mutable is_const : bool;

    (* Use as candidate in invariant generation *)
    mutable for_inv_gen : bool;

  }

(* A hashconsed state variable *)
type t = (state_var, state_var_prop) Hashcons.hash_consed


(* Hashing and equality on state variables *) 
module State_var_node = struct 

  (* State variable node *)
  type t = state_var_node

  (* Properties of state variable *)
  type prop = state_var_prop

  (* Hashing for state variables is hashing of strings *)
  let hash = Hashtbl.hash_param 100 100

  (* Equality of state variables is comparison of strings *)
  let equal (s1, l1) (s2, l2) =
    String.equal s1 s2 &&
    try List.for_all2 String.equal l1 l2
    with Invalid_argument _ -> false

end


(* Hashconsed state variables *)
module Hstate_var = Hashcons.Make (State_var_node)


(* Storage for state variables *)
let ht = Hstate_var.create 251

let stats () = Hstate_var.stats ht


(* ********************************************************************* *)
(* Hashtables, maps and sets                                             *)
(* ********************************************************************* *)


(* Comparison function on state variables *)
let compare_state_vars = Hashcons.compare

(* Equality function on state variables *)
let equal_state_vars = Hashcons.equal

(* Hashing function on state variables *)
let hash_state_var = Hashcons.hash 


(* Module as input to functors *)
module HashedStateVar = struct 

  (* Dummy type to prevent writing [type t = t] which is cyclic *)
  type z = t
  type t = z

  (* Compare tags of hashconsed uninterpreted symbols for equality *)
  let equal = equal_state_vars
    
  (* Use hash of uninterpreted symbol *)
  let hash = hash_state_var

end


(* Module as input to functors *)
module OrderedStateVar = struct 

  (* Dummy type to prevent writing [type t = t] which is cyclic *)
  type z = t
  type t = z

  (* Compare tags of hashconsed symbols *)
  let compare = compare_state_vars

end


(* Hashtable *)
module StateVarHashtbl = Hashtbl.Make (HashedStateVar)


(* Set *)
module StateVarSet = Set.Make (OrderedStateVar)


(* Map *)
module StateVarMap = Map.Make (OrderedStateVar)


(* State variable an uninterpreted function symbol is associated with *)
let uf_symbols_map = UfSymbol.UfSymbolHashtbl.create 41 


(* ********************************************************************* *)
(* Pretty-printing                                                       *)
(* ********************************************************************* *)

(* Pretty-print the property of a state variable *)
let pp_print_state_var_prop ppf prop =
  Format.fprintf ppf
    "{var_type:%a; uf_symbol:%a; is_input:%b; is_const:%b; for_inv_gen:%b"
    Type.pp_print_type prop.var_type
    UfSymbol.pp_print_uf_symbol prop.uf_symbol
    prop.is_input
    prop.is_const
    prop.for_inv_gen

(* Pretty-print a scoped name of a state variable *)
let pp_print_state_var_name ppf (n, s) =
  if s = [] then Format.fprintf ppf "%s" n
  else
    Format.fprintf ppf 
      "%a-%s" 
      (pp_print_list Format.pp_print_string "-") s
      n

(* Return a string representation of the name of a state variable *)
let string_of_state_var_name (n, s) = 
  string_of_t pp_print_state_var_name (n, s) 

(* Pretty-print a state variable *)
let pp_print_state_var_node ppf (n, s) = 
  pp_print_state_var_name ppf (n, s)

(* Pretty-print a hashconsed state variable *)
let pp_print_state_var ppf { Hashcons.node = (n, s) } =
  pp_print_state_var_node ppf (n, s)

let pp_print_state_var_debug ppf state_var =
  Format.fprintf ppf "node %a; prop %a"
    (pp_print_state_var_name) state_var.Hashcons.node
    (pp_print_state_var_prop) state_var.Hashcons.prop

(* Return a string representation of a hashconsed state variable *)
let string_of_state_var s = string_of_t pp_print_state_var s


(* ********************************************************************* *)
(* Accessor function                                                     *)
(* ********************************************************************* *)


(* Identifier of a state variable *)
let name_of_state_var { Hashcons.node = (n, _) } = n

(* Identifier of a state variable *)
let scope_of_state_var { Hashcons.node = (_, s) } = s

(* Type of a state variable *)
let type_of_state_var { Hashcons.prop = { var_type = t } } = t

(* Change the type of a state variable *)
let change_type_of_state_var { Hashcons.prop = v } t = v.var_type <- t

(* Uninterpreted function symbol of a state variable *)
let uf_symbol_of_state_var { Hashcons.prop = { uf_symbol = u } } = u

(* Uninterpreted function symbol of a state variable *)
let state_var_of_uf_symbol u = 
  UfSymbol.UfSymbolHashtbl.find uf_symbols_map u
  
(* Return true if state variable is an input *)
let is_input { Hashcons.prop = { is_input } } = is_input

(* Return true if state variable is constant *)
let is_const { Hashcons.prop = { is_const } } = is_const

let set_const flag { Hashcons.prop } = prop.is_const <- flag

(* Return true if state variable is to be used in invariant generation *)
let for_inv_gen { Hashcons.prop = { for_inv_gen } } = for_inv_gen

(* Set or unset flag to use state variable in invariant generation *)
let set_for_inv_gen flag { Hashcons.prop } = prop.for_inv_gen <- flag


(* ********************************************************************* *)
(* Constructors                                                          *)
(* ********************************************************************* *)


(* Generate a new identifier for an uninterpreted functions symbol *)
let gen_uf =
  let r = ref 0 in
  fun a s -> 
    incr r; 
    UfSymbol.mk_uf_symbol 
      (Format.sprintf "%%f%d" !r)
      a
      s

(* Hashcons a state variable *)
let mk_state_var 
    ?(is_input:bool = false)
    ?(is_const:bool = false)
    ?(for_inv_gen:bool = true)
    state_var_name
    state_var_scope
    state_var_type = 
  
  try 

    (* Get previous declaration of identifier *)
    let v = 
      Hstate_var.find ht (state_var_name, state_var_scope)  
    in

    if 

      (* Given type is a subtype of declared type? *)
      (Type.check_type state_var_type (type_of_state_var v)) 

    then

      (

        (* Return previously declared symbol *)
        v

      )

    else

      raise
        (Invalid_argument 
           (Format.asprintf
              "State variable %a redeclared with different type (%a, now %a)" 
              pp_print_state_var_name 
              (state_var_name, state_var_scope)
              Type.pp_print_type state_var_type
              Type.pp_print_type (type_of_state_var v)
            )
         )

  (* State variable is not in the hashcons table *)
  with Not_found -> 
    
    try 
      
      if (Flags.Smt.short_names () && not is_const) then raise Not_found;

      let _ = 
        UfSymbol.uf_symbol_of_string 
          (string_of_state_var_name (state_var_name, state_var_scope))
      in

      raise 
        (Invalid_argument
           (Format.asprintf 
              "State variable %a conflicts with uninterpreted \
               function symbol"
              pp_print_state_var_name 
              (state_var_name, state_var_scope)))

    with Not_found -> 

       (* Create an uninterpreted function symbol for the state variable *)
       let state_var_uf_symbol = 

         (if (Flags.Smt.short_names () && not is_const) then 
            
            gen_uf
              
          else
            
            (UfSymbol.mk_uf_symbol 
               (string_of_state_var_name 
                 (state_var_name, state_var_scope))))

           []
           (* (if is_const then [] else [Type.mk_int ()]) *)
           state_var_type 
       in

       (* Hashcons state variable *)
       let state_var = 
         Hstate_var.hashcons 
           ht 
           (state_var_name, state_var_scope) 
           { var_type = state_var_type; 
             uf_symbol = state_var_uf_symbol;
             is_input = is_input;
             is_const = is_const;
             for_inv_gen = for_inv_gen } 
       in

       (* Remember association of uninterpreted function symbol with
          state variable *)
       UfSymbol.UfSymbolHashtbl.add 
         uf_symbols_map 
         state_var_uf_symbol 
         state_var;

       (* Return state variable *)
       state_var

(* Returns a scoped init flag. *)
let mk_init_flag scope =
  mk_state_var
    ~is_input:true
    ~is_const:false
    ~for_inv_gen:false
    init_flag_string
    scope
    Type.t_bool

(* Returns a scoped depth input. *)
let mk_depth_input scope =
  mk_state_var
    ~is_input:true
    ~is_const:true
    ~for_inv_gen:false
    depth_input_string
    scope
    Type.t_int

(* Returns a scoped max depth input. *)
let mk_max_depth_input scope =
  mk_state_var
    ~is_input:true
    ~is_const:true
    ~for_inv_gen:false
    max_depth_input_string
    scope
    Type.t_int


(* Import a state variable from a different instance into this
   hashcons table *)
let import v = 
  mk_state_var 
    ~is_input:(is_input v)
    ~is_const:(is_const v)
    ~for_inv_gen:(for_inv_gen v)
    (name_of_state_var v) 
    (scope_of_state_var v) 
    (Type.import (type_of_state_var v))
    
(* Return a previously declared state variable *)
let state_var_of_string (state_var_name, state_var_scope) = 

  (* Get previous declaration of symbol, raise {!Not_found} if
     symbol was not declared *)
  Hstate_var.find ht (state_var_name, state_var_scope)


(* Return a previously declared state variable from a string consisting of the
   concatenation of all scopes and the state variable. Raises {Not_found} if it
   was not previously declared. *)
let state_var_of_long_string s =
  state_var_of_string (Lib.extract_scope_name s)
    

(* ********************************************************************* *)
(* Folding and utility functions on state variables                      *)
(* ********************************************************************* *)


(* Fold all variables in the hash-cons table *)
let fold f a = Hstate_var.fold f ht a

(* Fold all variables in the hash-cons table *)
let iter f = 
  Hstate_var.iter f ht


(*******************************)
(* Encoding of array variables *)
(*******************************)

let select_prefix = "_select"

(** @deprecated Not good with node calls, use {!encode_select_type} instead *)
(*let encode_select_name sv =
  let sv_uf = uf_symbol_of_state_var sv in
  let ty = UfSymbol.res_type_of_uf_symbol sv_uf in
  assert (Type.is_array ty);
  let ty_indexes = Type.all_index_types_of_array ty in
  (* add type for array *)
  let ty_args = ty :: ty_indexes in
  let ty_elem = Type.last_elem_type_of_array ty in
  let name =
    select_prefix ^ (*string_of_int (List.length ty_indexes) ^*) "_" ^
    (UfSymbol.string_of_uf_symbol sv_uf) (* ^ *)
    (* "@" ^ (Numeral.string_of_numeral off) *) in
  UfSymbol.mk_uf_symbol name ty_args ty_elem*)

module TyH = Type.TypeHashtbl

(* select functions *)
let array_ty_to_select_fun = TyH.create 7

let encode_select_type =
  let cpt = ref 0 in
  fun sv ->
    (* let sv_uf = uf_symbol_of_state_var sv in *)
    let ty = type_of_state_var sv |> Type.generalize in
    assert (Type.is_array ty);
    try TyH.find array_ty_to_select_fun ty
    with Not_found ->
      let ty_indexes = Type.all_index_types_of_array ty in
      (* add type for array *)
      let ty_args = ty :: ty_indexes in
      let ty_elem = Type.last_elem_type_of_array ty in
      incr cpt;
      let name = select_prefix ^ "_" ^ string_of_int !cpt in
      let f = UfSymbol.mk_uf_symbol name ty_args ty_elem in
      TyH.add array_ty_to_select_fun ty f;
      f

(* Encoding select funtion is done byt type (i.e. one select by array type).
   The select function performs all projections if the array is
   multidimensional. This means you should have something like [(select_1 m 0
   3)] in case [m] is a matrix *)
let encode_select = encode_select_type

(* Return select function that were created (this is used for declaration so
   it's better to return more - all - than not enough) *)
let get_select_ufs () =
  TyH.fold (fun _ f acc -> f :: acc) array_ty_to_select_fun []

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
