(* This file is part of the Kind 2 model checker.

   Copyright (c) 2026 by the Board of Trustees of the University of Iowa

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

(* Generation of well-formedness predicates for recursive ADTs.

   A refinement type on a field of a recursive ADT constrains infinitely many
   values (every node at every depth), so unlike a record or a non-recursive
   ADT it cannot be expanded into a finite conjunction over the type's
   structure. Instead each such ADT gets a recursive predicate

     function rec wf_NatList(.wf_arg: NatList) returns (.wf_res: bool);
     (*@contract decreases .wf_arg; *)
     let
       .wf_res = match .wf_arg with
                 | Nil          : true
                 | Cons(hd, tl) : hd >= 0 and wf_NatList(tl)
                 end;
     tel

   The declaration is tagged NodeId.WellFormedness, which is both what
   distinguishes it from a user declaration of the same name and how the passes
   that must treat it specially recognize it.

   which callers use as an ordinary constraint: assumed where the value comes
   from an assumption boundary, proved where it does not. *)

module A = LustreAst
module AH = LustreAstHelpers
module Ctx = TypeCheckerContext
module LDAT = LustreDesugarADTs
module AN = LustreAstNormalizer
module NI = NodeId

(* Bound names of the generated predicate. A leading '.' cannot occur in a user
   identifier, so neither can be shadowed by a constructor field name. *)
let self_var = HString.mk_hstring ".wf_arg"
let out_var = HString.mk_hstring ".wf_res"

(* One match arm per constructor. Each field of the constructor is bound by a
   pattern variable named after the field, and contributes whatever constraint
   its own type carries -- a predicate for a refinement type, a recursive call
   for a self-referential field, nothing for an unconstrained one. *)
let mk_arms ctx adt_map pos ctors =
  List.map
    (fun (ctor, fields) ->
      let vars = List.map (fun (fname, _) -> A.VarPat (pos, fname)) fields in
      let conjuncts =
        List.concat_map
          (fun (fname, fty) ->
            AN.mk_ref_type_expr adt_map ctx None (A.Ident (pos, fname)) fty)
          fields
      in
      (A.Pat (pos, ctor, vars), AH.mk_conj pos conjuncts))
    ctors

let mk_wf_predicate ctx adt_map pos ty_name ctors =
  let span = { A.start_pos = pos; A.end_pos = pos } in
  let body = A.Match (pos, A.Ident (pos, self_var), mk_arms ctx adt_map pos ctors, None) in
  let eq =
    A.Body (A.Equation (pos, A.StructDef (pos, [A.SingleIdent (pos, out_var)]), body))
  in
  (* The measure is the scrutinee itself: every recursive call is on a pattern
     variable of a constructor of that scrutinee, hence a structural subterm. *)
  let contract = (pos, [A.Decreases (pos, A.Ident (pos, self_var))]) in
  A.FuncDecl
    ( span,
      ( LDAT.wf_pred_id ty_name,
        false,
        A.Default,
        [],
        [ (pos, self_var, A.UserType (pos, [], ty_name), A.ClockTrue, false) ],
        [ (pos, out_var, A.Bool pos, A.ClockTrue) ],
        [],
        [ eq ],
        Some contract ),
      { A.is_rec = true; A.is_lemma = false } )

(* A predicate is needed only for a recursive ADT that actually carries a
   refinement somewhere; a recursive ADT with no constrained field imposes
   nothing, and a non-recursive one is expanded structurally instead. *)
let gen_wf_predicates ctx adt_map decls =
  List.filter_map
    (fun decl ->
      match decl with
      | A.TypeDecl (_, A.AliasType (pos, ty_name, _, (A.ADT (_, _, ctors) as ty))) ->
        let is_recursive =
          match LDAT.HStringMap.find_opt ty_name adt_map with
          | Some info -> info.LDAT.is_recursive
          | None -> false
        in
        if is_recursive && Ctx.type_contains_ref ctx ty then
          Some (mk_wf_predicate ctx adt_map pos ty_name ctors)
        else None
      | _ -> None)
    decls
