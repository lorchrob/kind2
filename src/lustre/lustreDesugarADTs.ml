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

(* Desugaring of algebraic data types (ADTs) to records.

    For each non-recursive ADT declaration
      type T = C0 | C1(t1_0, t1_1) | C2(t2_0)
    we produce a discriminant enum type and an equivalent record type:
      type T_tag = T_tag_C0 | T_tag_C1 | T_tag_C2;
      type T = { T_tag: T_tag;
                 C1_0: t1_0; C1_1: t1_1;
                 C2_0: t2_0 }

    For each bounded recursive ADT declaration
      bounded datatype Message = | Atomic(int) | Enc(Message, Message)
    used at depths 0..k (determined by scanning the program), we produce
    one enum+record pair per depth:
      type Message.0_tag = { Atomic };        (* only non-recursive ctors *)
      type Message.0 = { Message.0_tag: Message.0_tag; Atomic_0: int }
      type Message.1_tag = { Atomic, Enc };
      type Message.1 = { Message.1_tag: Message.1_tag;
                         Atomic_0: int; Enc_0: Message.0; Enc_1: Message.0 }
      ...
    The dot notation (Message.2) is valid in SMT-LIB but not in Lustre
    identifiers, so it cannot clash with user-defined names.

    ADTTerm and Match expressions are desugared during normalization.
    This module handles the pre-pass (TypeDecl transformation and context
    update) and exports shared infrastructure used by the normalizer. *)

module LA = LustreAst
module LH = LustreAstHelpers
module Ctx = TypeCheckerContext
module GI = GeneratedIdentifiers
module IC = LustreAstInlineConstants
module HStringMap = HString.HStringMap

(** Counter for generating unique oracle variable names. *)
let oracle_counter = ref 0

type adt_info = {
  type_name : HString.t;

  (* Original (non-depth-augmented) ADT name; equals type_name for non-bounded *)
  base_name : HString.t;

  (* name of the tag field in the record *)
  disc_field : HString.t;

  (* name of the generated enum type for the discriminant *)
  disc_enum : HString.t;

  (* ordered list of constructor names, also used as enum variant names *)
  ctor_variants : HString.t list;

  (* constructor name -> ordered list of (payload_field_name, field_type) *)
  ctor_fields : (HString.t * LA.lustre_type) list HStringMap.t;

  (* all payload fields across all constructors, in declaration order,
     deduplicated by field name *)
  all_payload_fields : (HString.t * LA.lustre_type) list;
}

type adt_map = adt_info HStringMap.t

let disc_field_name type_name =
  HString.mk_hstring (HString.string_of_hstring type_name ^ "_tag")

let payload_field_name ctor i =
  HString.mk_hstring (HString.string_of_hstring ctor ^ "_" ^ string_of_int i)

let bounded_type_name base_name depth =
  HString.mk_hstring (HString.string_of_hstring base_name ^ "." ^ string_of_int depth)

(* Build adt_info for an ADT (possibly depth-specific for bounded ADTs).
   base_name is the original non-augmented name; type_name is the (possibly
   depth-augmented) name used as the record type name. *)
let build_adt_info_named ~base_name ~type_name ctors =
  let disc_field = disc_field_name type_name in
  let disc_enum = disc_field_name type_name in
  let ctor_variants = List.map fst ctors in
  let ctor_fields =
    List.fold_left (fun m (ctor, field_types) ->
      let fields =
        List.mapi (fun j ty -> (payload_field_name ctor j, ty)) field_types
      in
      HStringMap.add ctor fields m
    ) HStringMap.empty ctors
  in
  let all_payload_fields =
    List.concat_map (fun (ctor, _) -> HStringMap.find ctor ctor_fields) ctors
  in
  { type_name; base_name; disc_field; disc_enum;
    ctor_variants; ctor_fields; all_payload_fields }

(* Build adt_info for a non-bounded ADT *)
let build_adt_info type_name ctors =
  build_adt_info_named ~base_name:type_name ~type_name ctors

(* Build adt_info for one depth level of a bounded ADT.
   At depth 0: only non-recursive constructors.
   At depth d > 0: all constructors, with recursive UserType(base_name, _)
   fields replaced by UserType(base_name.(d-1), None). *)
let build_bounded_adt_info_at_depth base_name ctors depth =
  let is_recursive_field base ty =
    match ty with
    | LA.UserType (_, _, n, _) -> n = base
    | _ -> false
  in
  let has_recursive_field base field_tys =
    List.exists (is_recursive_field base) field_tys
  in
  let child_name = bounded_type_name base_name (depth - 1) in
  let adjust_field base ty =
    match ty with
    | LA.UserType (p, args, n, _) when n = base ->
      LA.UserType (p, args, child_name, None)
    | _ -> ty
  in
  (* Filter and adjust constructors for this depth *)
  let filtered_ctors =
    if depth = 0 then
      List.filter (fun (_, ftys) -> not (has_recursive_field base_name ftys)) ctors
    else
      List.map (fun (ctor, ftys) ->
        ctor, List.map (adjust_field base_name) ftys
      ) ctors
  in
  let type_name = bounded_type_name base_name depth in
  build_adt_info_named ~base_name ~type_name filtered_ctors

(* Collect all ADT type declarations from a program into an adt_map.
   For bounded ADTs, scans the program for the maximum depth used per name
   and generates one adt_info per depth level (0..max_depth). *)
let build_adt_map ctx decls =
  (* First pass: collect bounded ADT names+ctors and non-bounded ADTs *)
  let bounded_adts : (HString.t * (HString.t * LA.lustre_type list) list) list ref = ref [] in
  let non_bounded_adts : (HString.t * (HString.t * LA.lustre_type list) list) list ref = ref [] in
  List.iter (function
    | LA.TypeDecl (_, LA.AliasType (_, name, _, LA.ADT (_, _, Some _, ctors))) ->
      bounded_adts := (name, ctors) :: !bounded_adts
    | LA.TypeDecl (_, LA.AliasType (_, name, _, LA.ADT (_, _, None, ctors))) ->
      non_bounded_adts := (name, ctors) :: !non_bounded_adts
    | _ -> ()
  ) decls;
  (* Build a map from ctor name -> base bounded ADT name for depth scanning *)
  let ctor_to_base : HString.t HStringMap.t =
    List.fold_left (fun m (name, ctors) ->
      List.fold_left (fun m (ctor, _) -> HStringMap.add ctor name m) m ctors
    ) HStringMap.empty !bounded_adts
  in
  let bounded_names : unit HStringMap.t =
    List.fold_left (fun m (name, _) -> HStringMap.add name () m)
      HStringMap.empty !bounded_adts
  in
  (* Scan depth from a Const integer expression *)
  let depth_of_const = function
    | LA.Const (_, LA.Num k_str) -> Some (int_of_string (HString.string_of_hstring k_str))
    | _ -> None
  in
  (* Second pass: find max depth used per bounded ADT *)
  let max_depths : int HStringMap.t ref = ref HStringMap.empty in
  let update_depth name d =
    let cur = try HStringMap.find name !max_depths with Not_found -> -1 in
    if d > cur then max_depths := HStringMap.add name d !max_depths
  in
  let rec scan_ty ty =
    match ty with
    | LA.UserType (_, _, name, Some k_expr) when HStringMap.mem name bounded_names ->
      let k_expr_eval =
        match depth_of_const k_expr with
        | Some k -> Some k
        | None ->
          match IC.eval_int_expr ctx k_expr with
          | Ok k -> Some k | Error _ -> None
      in
      (match k_expr_eval with
      | Some k -> update_depth name k
      | None -> ())
    | LA.UserType (_, args, _, _) -> List.iter scan_ty args
    | LA.ArrayType (_, (ty, _)) -> scan_ty ty
    | LA.TupleType (_, tys) | LA.GroupType (_, tys) -> List.iter scan_ty tys
    | LA.RecordType (_, _, fields) -> List.iter (fun (_, _, ty) -> scan_ty ty) fields
    | LA.ADT (_, _, _, ctors) ->
      List.iter (fun (_, ftys) -> List.iter scan_ty ftys) ctors
    | LA.TArr (_, t1, t2) | LA.Map (_, t1, t2) -> scan_ty t1; scan_ty t2
    | LA.Set (_, ty) -> scan_ty ty
    | LA.RefinementType (_, (_, _, ty), _) -> scan_ty ty
    | _ -> ()
  in
  let rec scan_expr expr =
    match expr with
    | LA.ADTTerm (_, ctor, Some k_expr, args) ->
      (match HStringMap.find_opt ctor ctor_to_base with
      | Some base ->
        (match depth_of_const k_expr with
        | Some k -> update_depth base k
        | None ->
          match IC.eval_int_expr ctx k_expr with
          | Ok k -> update_depth base k | Error _ -> ())
      | None -> ());
      List.iter scan_expr args
    | LA.ADTTerm (_, _, _, args) -> List.iter scan_expr args
    | LA.Match (_, scrut, arms, ty_opt) ->
      scan_expr scrut;
      List.iter (fun (_, body) -> scan_expr body) arms;
      (match ty_opt with Some ty -> scan_ty ty | None -> ())
    | LA.BinaryOp (_, _, e1, e2) | LA.CompOp (_, _, e1, e2)
    | LA.Arrow (_, e1, e2) | LA.ArrayConstr (_, e1, e2)
    | LA.IndexAccess (_, e1, e2, _) ->
      scan_expr e1; scan_expr e2
    | LA.UnaryOp (_, _, e) | LA.ConvOp (_, _, e)
    | LA.When (_, e, _) | LA.Pre (_, e)
    | LA.RecordProject (_, e, _) -> scan_expr e
    | LA.TernaryOp (_, _, e1, e2, e3) -> scan_expr e1; scan_expr e2; scan_expr e3
    | LA.GroupExpr (_, _, es) | LA.Call (_, _, _, es) -> List.iter scan_expr es
    | LA.RecordExpr (_, _, _, fields) -> List.iter (fun (_, e) -> scan_expr e) fields
    | LA.TypeAscription (_, e, ty) -> scan_expr e; scan_ty ty
    | LA.Quantifier (_, _, tis, e) ->
      List.iter (fun (_, _, ty) -> scan_ty ty) tis; scan_expr e
    | LA.Condact (_, e1, e2, _, es1, es2) ->
      scan_expr e1; scan_expr e2; List.iter scan_expr es1; List.iter scan_expr es2
    | LA.Activate (_, _, e1, e2, es) ->
      scan_expr e1; scan_expr e2; List.iter scan_expr es
    | LA.Merge (_, _, cases) -> List.iter (fun (_, e) -> scan_expr e) cases
    | LA.RestartEvery (_, _, es, e) -> List.iter scan_expr es; scan_expr e
    | LA.StructUpdate (_, e, _, Some e2) -> scan_expr e; scan_expr e2
    | LA.StructUpdate (_, e, _, None) -> scan_expr e
    | _ -> ()
  in
  let scan_node_item item =
    let open LA in
    match item with
    | Body (Equation (_, _, e)) -> scan_expr e
    | Body (Assert (_, e)) -> scan_expr e
    | AnnotMain _ | AnnotProperty _ -> ()
    | IfBlock _ | FrameBlock _ -> ()
  in
  let scan_decl decl =
    let open LA in
    match decl with
    | NodeDecl (_, (_, _, _, _, inputs, outputs, ldecls, items, _)) ->
      List.iter (fun (_, _, ty, _, _) -> scan_ty ty) inputs;
      List.iter (fun (_, _, ty, _) -> scan_ty ty) outputs;
      List.iter (function
        | NodeVarDecl (_, (_, _, ty, _)) -> scan_ty ty
        | NodeConstDecl (_, TypedConst (_, _, _, ty)) -> scan_ty ty
        | NodeConstDecl (_, FreeConst (_, _, ty)) -> scan_ty ty
        | NodeConstDecl (_, UntypedConst _) -> ()
      ) ldecls;
      List.iter scan_node_item items
    | FuncDecl (_, (_, _, _, _, inputs, outputs, ldecls, items, _)) ->
      List.iter (fun (_, _, ty, _, _) -> scan_ty ty) inputs;
      List.iter (fun (_, _, ty, _) -> scan_ty ty) outputs;
      List.iter (function
        | NodeVarDecl (_, (_, _, ty, _)) -> scan_ty ty
        | NodeConstDecl (_, TypedConst (_, _, _, ty)) -> scan_ty ty
        | NodeConstDecl (_, FreeConst (_, _, ty)) -> scan_ty ty
        | NodeConstDecl (_, UntypedConst _) -> ()
      ) ldecls;
      List.iter scan_node_item items
    | ConstDecl (_, TypedConst (_, _, e, ty)) -> scan_expr e; scan_ty ty
    | ConstDecl (_, UntypedConst (_, _, e)) -> scan_expr e
    | ConstDecl (_, FreeConst (_, _, ty)) -> scan_ty ty
    | TypeDecl _ | ContractNodeDecl _ | NodeParamInst _ -> ()
  in
  List.iter scan_decl decls;
  (* Build the adt_map *)
  let m = ref HStringMap.empty in
  (* Non-bounded ADTs *)
  List.iter (fun (name, ctors) ->
    m := HStringMap.add name (build_adt_info name ctors) !m
  ) !non_bounded_adts;
  (* Bounded ADTs: generate one entry per depth 0..max_depth *)
  List.iter (fun (base_name, ctors) ->
    let max_d = try HStringMap.find base_name !max_depths with Not_found -> -1 in
    for d = 0 to max_d do
      let type_name = bounded_type_name base_name d in
      let info = build_bounded_adt_info_at_depth base_name ctors d in
      m := HStringMap.add type_name info !m
    done
  ) !bounded_adts;
  !m

let record_type_of_adt pos info =
  let disc_fld = (pos, info.disc_field, LA.UserType (pos, [], info.disc_enum, None)) in
  let payload_flds =
    List.map (fun (fname, ftype) -> (pos, fname, ftype)) info.all_payload_fields
  in
  LA.RecordType (pos, info.type_name, disc_fld :: payload_flds)

(* Mint a fresh unconstrained oracle variable for a junk payload field.
   Returns the identifier expression and a gids record containing the oracle. *)
let mk_fresh_adt_term_oracle pos ty =
  incr oracle_counter;
  let name = HString.mk_hstring (string_of_int !oracle_counter ^ "_adt_junk") in
  let gids = { (GI.empty ()) with GI.adt_term_oracles = [(name, ty)] } in
  LA.Ident (pos, name), gids

(* Build a RecordProject accessing the tag field of an expression. *)
let tag_of pos info scrut =
  LA.RecordProject (pos, scrut, info.disc_field)

let adt_info_of_type adt_map ty =
  match ty with
  | LA.UserType (_, _, name, Some (LA.Const (_, LA.Num k_str))) ->
    (* Bounded ADT with concrete depth: look up by depth-augmented name *)
    let augmented = HString.mk_hstring
      (HString.string_of_hstring name ^ "." ^ HString.string_of_hstring k_str) in
    HStringMap.find_opt augmented adt_map
  | LA.UserType (_, _, name, _) -> HStringMap.find_opt name adt_map
  | LA.ADT (_, name, _, _) -> HStringMap.find_opt name adt_map
  | _ -> None

(* Replace every ADT type with its desugared record equivalent. *)
let rec desugar_type pos adt_map ty =
  match adt_info_of_type adt_map ty with
  | Some adt_info -> record_type_of_adt pos adt_info
  | None ->
    let ds = desugar_type pos adt_map in
    match ty with
    | LA.Bool _ | LA.Int _ | LA.Real _
    | LA.SBitVector _ | LA.UBitVector _
    | LA.IntRange _ | LA.AbstractType _
    | LA.EnumType _ | LA.History _ -> ty
    | LA.UserType (p, params, name, k) ->
      LA.UserType (p, List.map ds params, name, k)
    | LA.TupleType (p, ts) -> LA.TupleType (p, List.map ds ts)
    | LA.GroupType (p, ts) -> LA.GroupType (p, List.map ds ts)
    | LA.RecordType (p, n, fields) ->
      LA.RecordType (p, n,
        List.map (fun (fp, fn, ft) -> (fp, fn, ds ft)) fields)
    | LA.ArrayType (p, (t, e)) -> LA.ArrayType (p, (ds t, e))
    | LA.TArr (p, t1, t2) -> LA.TArr (p, ds t1, ds t2)
    | LA.RefinementType (p, (p2, id, t), e) ->
      LA.RefinementType (p, (p2, id, ds t), e)
    | LA.Map (p, kt, vt) -> LA.Map (p, ds kt, ds vt)
    | LA.Set (p, t) -> LA.Set (p, ds t)
    | LA.ADT _ -> ty (* unreachable: adt_info_of_type handles ADT *)

(* Recursively collect the conjunction of tag equality conditions and the
   variable->field-projection substitutions imposed by a (possibly nested)
   constructor pattern.  Returns (conditions, substitutions). *)
let rec collect_pattern_constraints pos adt_map info scrut (LA.Pat (_, name, _, sub_pats)) =
  if List.mem name info.ctor_variants then
    let ctor = name in
    let outer_cond =
      LA.CompOp (pos, LA.Eq, tag_of pos info scrut, LA.Ident (pos, ctor))
    in
    let ctor_fields =
      match HStringMap.find_opt ctor info.ctor_fields with
      | Some fs -> fs
      | None -> []
    in
    let sub_conds, sub_subs =
      List.fold_left2 (fun (conds, subs) (fname, ftype) sub_pat ->
        let field_expr = LA.RecordProject (pos, scrut, fname) in
        let LA.Pat (_, sub_name, _, _) = sub_pat in
        match adt_info_of_type adt_map ftype with
        | Some sub_info when List.mem sub_name sub_info.ctor_variants ->
          let (c, s) = collect_pattern_constraints pos adt_map sub_info field_expr sub_pat in
          (conds @ c, subs @ s)
        | _ ->
          (conds, subs @ [(sub_name, field_expr)])
      ) ([], []) ctor_fields sub_pats
    in
    (outer_cond :: sub_conds, sub_subs)
  else
    ([], [(name, scrut)])

(* Desugar a single match arm into a (condition option, body) pair.
   Substitutes pattern variables with field projections in body. *)
let desugar_arm pos adt_map info scrut pat body =
  let (conds, subs) = collect_pattern_constraints pos adt_map info scrut pat in
  let body =
    List.fold_left (fun b (var, expr) -> LH.substitute_naive var expr b) body subs
  in
  match conds with
  | [] -> (None, body)
  | first :: rest ->
    let cond = List.fold_left (fun acc c -> LA.BinaryOp (pos, LA.And, acc, c)) first rest in
    (Some cond, body)

(* Build a nested ITE from a list of (condition option, body) pairs. *)
let rec build_ite pos arms =
  match arms with
  | [] -> assert false
  (* More cases after a catch-all; will be caught in later PR by redundancy checks *)
  | (None, _) :: _ :: _ -> assert false
  (* Last case must always cover all cases so far uncovered *)
  | [(_, body)] -> body
  | (Some cond, body) :: rest ->
    LA.TernaryOp (pos, LA.LazyIte, cond, body, build_ite pos rest)

let update_context adt_map ctx =
  HStringMap.fold (fun type_name info acc_ctx ->
    let pos = Lib.dummy_pos in
    let enum_user_ty = LA.UserType (pos, [], info.disc_enum, None) in
    let enum_ty = LA.EnumType (pos, info.disc_enum, info.ctor_variants) in
    let acc_ctx = Ctx.add_enum_variants acc_ctx info.disc_enum info.ctor_variants in
    let acc_ctx = Ctx.add_ty_syn acc_ctx info.disc_enum enum_ty in
    let acc_ctx = Ctx.add_ty_decl acc_ctx info.disc_enum in
    let type_bindings = List.map (fun v -> Ctx.singleton_ty v enum_user_ty) info.ctor_variants in
    let const_bindings = List.map (fun v ->
      Ctx.singleton_const v (LA.Ident (pos, v)) enum_user_ty Global
    ) info.ctor_variants in
    let acc_ctx = List.fold_left Ctx.union acc_ctx (type_bindings @ const_bindings) in
    let acc_ctx = HStringMap.fold (fun ctor fields acc ->
      let field_tys = List.map snd fields in
      Ctx.add_adt_ctor acc ctor type_name field_tys
    ) info.ctor_fields acc_ctx in
    let record_ty = record_type_of_adt pos info in
    Ctx.add_ty_syn acc_ctx type_name record_ty
  ) adt_map ctx

(* Pre-pass: transform ADT TypeDecls into enum + record TypeDecls and update
   the type-checker context. Expression-level desugaring (ADTTerm, Match)
   is interspersed within the normalizer. *)
let desugar_adts_program ctx decls =
  let adt_map = build_adt_map ctx decls in
  if HStringMap.is_empty adt_map then
    (decls, ctx, adt_map)
  else
    let decls = List.concat_map (fun decl ->
      match decl with
      | LA.TypeDecl (sp, LA.AliasType (_, name, ty_params, LA.ADT (pos, _, None, _))) ->
        (* Non-bounded ADT: single enum + record pair *)
        (match HStringMap.find_opt name adt_map with
        | Some info ->
          let enum_ty = LA.EnumType (pos, info.disc_enum, info.ctor_variants) in
          let enum_decl = LA.TypeDecl (sp, LA.AliasType (pos, info.disc_enum, [], enum_ty)) in
          let record_ty = record_type_of_adt pos info in
          let record_decl = LA.TypeDecl (sp, LA.AliasType (pos, name, ty_params, record_ty)) in
          [enum_decl; record_decl]
        | None -> assert false)
      | LA.TypeDecl (sp, LA.AliasType (_, name, ty_params, LA.ADT (pos, _, Some _, _))) ->
        (* Bounded ADT: emit one enum + record pair per depth 0..max *)
        let depth_entries =
          HStringMap.bindings adt_map
          |> List.filter (fun (k, info) ->
            k <> name && info.base_name = name)
          |> List.sort (fun (_, i1) (_, i2) ->
            (* Sort by depth: parse the suffix after the last '.' *)
            let depth_of type_name =
              let s = HString.string_of_hstring type_name in
              match String.rindex_opt s '.' with
              | Some idx -> int_of_string (String.sub s (idx+1) (String.length s - idx - 1))
              | None -> -1
            in
            compare (depth_of i1.type_name) (depth_of i2.type_name))
        in
        List.concat_map (fun (_, info) ->
          let enum_ty = LA.EnumType (pos, info.disc_enum, info.ctor_variants) in
          let enum_decl = LA.TypeDecl (sp, LA.AliasType (pos, info.disc_enum, [], enum_ty)) in
          let record_ty = record_type_of_adt pos info in
          let record_decl = LA.TypeDecl (sp, LA.AliasType (pos, info.type_name, ty_params, record_ty)) in
          [enum_decl; record_decl]
        ) depth_entries
      | _ -> [decl]
    ) decls in
    let ctx = update_context adt_map ctx in
    (decls, ctx, adt_map)
