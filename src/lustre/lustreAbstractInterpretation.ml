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

(**
    @author Andrew Marmaduke *)

open Lib
module LA = LustreAst
module LAH = LustreAstHelpers
module Ctx = TypeCheckerContext
module TC = LustreTypeChecker

module IMap = struct
  (* everything that [Stdlib.Map] gives us  *)
  include Map.Make(struct
              type t = LA.ident
              let compare i1 i2 = HString.compare i1 i2
            end)
  let keys: 'a t -> key list = fun m -> List.map fst (bindings m)
end

(** Context from a node identifier to a map of its
  variable identifiers to their inferred subrange bounds *)
type context = LA.lustre_type IMap.t IMap.t

let dpos = Lib.dummy_pos

let empty_context = IMap.empty

let union a b = IMap.union
  (fun _ n1 n2 -> Some (IMap.union
    (fun _ _ i2 -> Some i2)
    n1 n2))
  a b

let get_type ctx node_name id = match IMap.find_opt node_name ctx with
  | Some node_ctx -> (match IMap.find_opt id node_ctx with
    | Some ty -> Some ty
    | None -> None)
  | None -> None

let add_type ctx node_name id ty =
  let update = IMap.singleton node_name (IMap.singleton id ty) in
  union ctx update

let extract_bounds_from_type ty =
  (match ty with
  | LA.IntRange (_, Const (_, Num l), Const (_, Num r)) ->
    let l = Numeral.of_string (HString.string_of_hstring l) in
    let r = Numeral.of_string (HString.string_of_hstring r) in
    Some l, Some r
  (* If the int range is not constant, we treat it as an int for now *)
  | IntRange _ -> None, None
  | _ -> None, None)

let subrange_from_bounds l r =
  let l = HString.mk_hstring (Numeral.string_of_numeral l) in
  let r = HString.mk_hstring (Numeral.string_of_numeral r) in
  LA.IntRange (dpos, Const (dpos, Num l), Const (dpos, Num r))

let rec merge_types a b = match a, b with
  | LA.ArrayType (_, (t1, e)), LA.ArrayType (_, (t2, _)) ->
    let t = merge_types t1 t2 in
    LA.ArrayType (dpos, (t, e))
  | RecordType (_, t1s), RecordType (_, t2s) ->
    let ts = List.map2
      (fun (p, i, t1) (_, _, t2) -> p, i, merge_types t1 t2)
      t1s t2s
    in
    LA.RecordType (dpos, ts)
  | TupleType (_, t1s), TupleType (_, t2s) ->
    let ts = List.map2 (fun t1 t2 -> merge_types t1 t2) t1s t2s in
    LA.TupleType (dpos, ts)
  | IntRange (_, Const (_, Num l1), Const (_, Num r1)),
    IntRange (_, Const (_, Num l2), Const (_, Num r2)) ->
    let l1 = Numeral.of_string (HString.string_of_hstring l1) in
    let l2 = Numeral.of_string (HString.string_of_hstring l2) in
    let r1 = Numeral.of_string (HString.string_of_hstring r1) in
    let r2 = Numeral.of_string (HString.string_of_hstring r2) in
    let l = HString.mk_hstring (Numeral.string_of_numeral (Numeral.min l1 l2)) in
    let r = HString.mk_hstring (Numeral.string_of_numeral (Numeral.max r1 r2)) in
    IntRange (dpos, Const (dpos, Num l), Const (dpos, Num r))
  | IntRange _, (Int _ as t) -> t
  | Int _ as t, IntRange _ -> t
  | t, _ -> t

let rec arity_of_expr ty_ctx = function
  | LA.GroupExpr (_, ExprList, es) -> List.length es
  | TernaryOp (_, Ite, _, e, _) -> arity_of_expr ty_ctx e
  | Condact (_, _, _, id, _, _)
  | Activate (_, id, _, _, _)
  | RestartEvery (_, id, _, _)
  | Call (_, id, _) ->
    let node_ty = Ctx.lookup_node_ty ty_ctx id |> get in
    let (_, o) = LAH.type_arity node_ty in
    o
  | _ -> 1

let rec interpret_program ty_ctx = function
  | [] -> empty_context
  | h :: t -> union (interpret_decl ty_ctx h) (interpret_program ty_ctx t)

and interpret_contract node_id (ctx:context) ty_ctx eqns =
  let ty_ctx = TC.tc_ctx_of_contract ty_ctx eqns
    |> Res.map_err (fun (_, s) -> fun _ -> Debug.parse "%s" s)
    |> Res.unwrap
  in
  List.fold_left (fun acc eqn ->
      union acc (interpret_contract_eqn node_id ctx ty_ctx eqn))
    empty_context
    eqns

and interpret_contract_eqn node_id ctx ty_ctx = function
  | LA.GhostConst _ -> empty_context
  | GhostVar decl -> interpret_ghost_var node_id ctx ty_ctx decl
  | Assume _ | Guarantee _ | Mode _
  | ContractCall _ | AssumptionVars _ -> empty_context

and interpret_ghost_var node_id ctx ty_ctx = function
  | LA.FreeConst _ -> empty_context
  | UntypedConst (_, id, expr) ->
    let ty = TC.infer_type_expr ty_ctx expr
      |> Res.map_err (fun (_, s) -> fun _ -> Debug.parse "%s" s)
      |> Res.unwrap
    in
    let ty = interpret_expr_by_type node_id ctx ty_ctx ty 0 expr in
    add_type ctx node_id id ty
  | TypedConst (_, id, expr, ty) ->
    let ty = interpret_expr_by_type node_id ctx ty_ctx ty 0 expr in
    add_type ctx node_id id ty

and interpret_decl ty_ctx = function
  | LA.TypeDecl _
  | ConstDecl _ -> empty_context
  | NodeDecl (_, decl)
  | FuncDecl (_, decl) -> interpret_node ty_ctx decl
  | ContractNodeDecl _
  | NodeParamInst _ -> empty_context

and interpret_node ty_ctx (id, _, _, ins, outs, locals, items, contract) =
  (* Setup the typing context *)
  let constants_ctx = ins
    |> List.map Ctx.extract_consts
    |> (List.fold_left Ctx.union ty_ctx)
  in
  let input_ctx = ins
    |> List.map Ctx.extract_arg_ctx
    |> (List.fold_left Ctx.union ty_ctx)
  in
  let output_ctx = outs
    |> List.map Ctx.extract_ret_ctx
    |> (List.fold_left Ctx.union ty_ctx)
  in
  let ty_ctx = Ctx.union
    (Ctx.union constants_ctx ty_ctx)
    (Ctx.union input_ctx output_ctx)
  in
  let ty_ctx = List.fold_left
    (fun ctx local -> TC.local_var_binding ctx local
      |> Res.map_err (fun (_, s) -> fun _ -> Debug.parse "%s" s)
      |> Res.unwrap)
    ty_ctx
    locals
  in
  let ctx = IMap.empty in
  let eqns = List.fold_left (fun acc -> function
    | LA.Body eqn -> (match eqn with
      | LA.Assert _ -> acc
      | Equation (_, lhs, rhs) -> (lhs, rhs) :: acc
      | Automaton _ -> acc)
    | AnnotMain _ -> acc
    | AnnotProperty _ -> acc)
    []
    items
  in
  let contract_ctx = match contract with
    | Some contract -> interpret_contract id ctx ty_ctx contract 
    | None -> empty_context
  in
  let eqn_ctx = List.fold_left (fun acc (lhs, rhs) ->
      let ctx = interpret_eqn id acc ty_ctx lhs rhs in
      union acc ctx)
    ctx
    eqns
  in
  union contract_ctx eqn_ctx

and interpret_eqn node_id ctx ty_ctx lhs rhs =
  let struct_items = match lhs with
    | StructDef (_, items) -> items
  in
  let rec separate_eqns rhs = match rhs with
    | LA.GroupExpr (_, ExprList, es) ->
      es |> List.map (separate_eqns) |> List.flatten
    | e -> List.init (arity_of_expr ty_ctx e) (fun p -> e, p)
  in
  let eqns = separate_eqns rhs in
  List.fold_left2 (fun acc lhs (expr, p) -> match lhs with
      | LA.SingleIdent (_, id) ->
        let ty1 = Ctx.lookup_ty ty_ctx id |> get in
        let ty1 = Ctx.expand_nested_type_syn ty_ctx ty1 in
        let ty2 = interpret_expr_by_type node_id ctx ty_ctx ty1 p expr in
        let ty = merge_types ty1 ty2 in
        add_type acc node_id id ty
      | LA.ArrayDef (_, _, _) -> acc
      | _ -> assert false)
    ctx
    struct_items
    eqns

and interpret_expr_by_type node_id ctx ty_ctx ty proj expr : LA.lustre_type =
  match ty with
  | RecordType (_, ts) -> 
    (match expr with
    | Ident (_, id) -> (match (get_type ctx node_id id) with
      | Some id_ty -> merge_types ty id_ty
      | None -> ty)
    | RecordExpr (_, _, es) ->
      let emap = List.fold_left
        (fun acc (id, e) -> IMap.add id e acc)
        IMap.empty es
      in
      let ts = List.map (fun (p, i, t) ->
          let e = IMap.find i emap in
          p, i, interpret_expr_by_type node_id ctx ty_ctx t proj e)
        ts
      in
      RecordType (dpos, ts)
    | Call _ | Condact _ | Activate _ | RestartEvery _ -> ty
    | TernaryOp (_, Ite, _, e1, e2) ->
      let t1 = interpret_expr_by_type node_id ctx ty_ctx ty proj e1 in
      let t2 = interpret_expr_by_type node_id ctx ty_ctx ty proj e2 in
      merge_types t1 t2
    | Pre (_, e) -> interpret_expr_by_type node_id ctx ty_ctx ty proj e
    | Arrow (_, e1, e2) ->
      let t1 = interpret_expr_by_type node_id ctx ty_ctx ty proj e1 in
      let t2 = interpret_expr_by_type node_id ctx ty_ctx ty proj e2 in
      merge_types t1 t2
    | RecordProject _ | TupleProject _ | StructUpdate _ -> ty
    | _ -> assert false)
  | ArrayType (_, (t, s)) -> (match expr with
    | Ident (_, id) -> (match (get_type ctx node_id id) with
      | Some id_ty -> merge_types ty id_ty
      | None -> ty)
    | GroupExpr (_, ArrayExpr, es) ->
      let t = List.fold_left (fun acc e ->
          let t' = interpret_expr_by_type node_id ctx ty_ctx t proj e in
          merge_types acc t')
        t es
      in
      ArrayType (dpos, (t, s))
    | ArrayConstr (_, e1, _) ->
      let t = interpret_expr_by_type node_id ctx ty_ctx t proj e1 in
      ArrayType (dpos, (t, s))
    | Call _ | Condact _ | Activate _ | RestartEvery _ -> ty
    | TernaryOp (_, Ite, _, e1, e2) ->
      let t1 = interpret_expr_by_type node_id ctx ty_ctx ty proj e1 in
      let t2 = interpret_expr_by_type node_id ctx ty_ctx ty proj e2 in
      merge_types t1 t2
    | Pre (_, e) -> interpret_expr_by_type node_id ctx ty_ctx ty proj e
    | Arrow (_, e1, e2) ->
      let t1 = interpret_expr_by_type node_id ctx ty_ctx ty proj e1 in
      let t2 = interpret_expr_by_type node_id ctx ty_ctx ty proj e2 in
      merge_types t1 t2
    | RecordProject _ | TupleProject _ | StructUpdate _ -> ty
    | _ -> assert false)
  | TupleType (_, ts) -> (match expr with
    | Ident (_, id) -> (match (get_type ctx node_id id) with
      | Some id_ty -> merge_types ty id_ty
      | None -> ty)
    | GroupExpr (_, TupleExpr, es) ->
      let ts = List.map2
        (fun t e -> interpret_expr_by_type node_id ctx ty_ctx t proj e)
        ts es
      in
      TupleType (dpos, ts)
    | Call _ | Condact _ | Activate _ | RestartEvery _ -> ty
    | TernaryOp (_, Ite, _, e1, e2) ->
      let t1 = interpret_expr_by_type node_id ctx ty_ctx ty proj e1 in
      let t2 = interpret_expr_by_type node_id ctx ty_ctx ty proj e2 in
      merge_types t1 t2
    | Pre (_, e) -> interpret_expr_by_type node_id ctx ty_ctx ty proj e
    | Arrow (_, e1, e2) ->
      let t1 = interpret_expr_by_type node_id ctx ty_ctx ty proj e1 in
      let t2 = interpret_expr_by_type node_id ctx ty_ctx ty proj e2 in
      merge_types t1 t2
    | RecordProject _ | TupleProject _ | StructUpdate _ -> ty
    | _ -> assert false)
  | IntRange (_, Const (_, Num l1), Const (_, Num r1)) as t ->
    let l1 = Numeral.of_string (HString.string_of_hstring l1) in
    let r1 = Numeral.of_string (HString.string_of_hstring r1) in
    let l2, r2 = interpret_int_expr node_id ctx ty_ctx proj expr in
    (match l2, r2 with
    | Some l2, Some r2 ->
      let l, r = Numeral.max l1 l2, Numeral.min r1 r2 in
      subrange_from_bounds l r
    | _ -> t)
  | Int _ | IntRange _ ->
    let l, r = interpret_int_expr node_id ctx ty_ctx proj expr in
    (match l, r with
    | Some l, Some r -> subrange_from_bounds l r
    | _ -> LA.Int dpos)
  | t -> t

and interpret_int_expr node_id ctx ty_ctx proj expr = 
  let infer e =
    let ty = TC.infer_type_expr ty_ctx e
      |> Res.map_err (fun (_, s) -> fun _ -> Debug.parse "%s" s)
      |> Res.unwrap
    in
    let ty = Ctx.expand_nested_type_syn ty_ctx ty in
    interpret_expr_by_type node_id ctx ty_ctx ty proj e
  in
  match expr with
  | LA.Ident (_, id) -> (match get_type ctx node_id id with
    | Some ty -> extract_bounds_from_type ty
    | None -> None, None)
  | ModeRef (_, _) -> assert false
  | RecordProject (_, e, p) -> (match infer e with
    | RecordType (_, nested) ->
      let (_, _, ty) = List.find (fun (_, id, _) -> HString.equal id p) nested in
      extract_bounds_from_type ty
    | _ -> assert false)
  | TupleProject (_, e, idx) -> (match infer e with
    | TupleType (_, nested) -> 
      let ty = List.nth nested idx in
      extract_bounds_from_type ty
    | _ -> assert false)
  | ArrayIndex (_, e, _) -> (match infer e with
    | ArrayType (_, (t, _)) -> extract_bounds_from_type t
    | _ -> assert false)
  | Const (_, const) -> (match const with
    | True | False -> assert false
    | Num x -> 
      let v = Numeral.of_string (HString.string_of_hstring x) in
      Some v, Some v
    | Dec _ -> assert false)
  | UnaryOp (_, op, e) ->
    interpret_int_unary_expr node_id ctx ty_ctx op proj e
  | BinaryOp (_, op, e1, e2) ->
    interpret_int_binary_expr node_id ctx ty_ctx proj op e1 e2
  (* Either constant inlining removed the if-statement,
    or we can't learn which branch to take yet*)
  | TernaryOp (_, Ite, _, e1, e2) ->
    interpret_int_branch_expr node_id ctx ty_ctx proj e1 e2
  | TernaryOp (_, With, _, _, _) -> assert false
  | NArityOp _ -> assert false
  | ConvOp (_, _, e) -> interpret_int_expr node_id ctx ty_ctx proj e
  | CompOp _-> assert false
  | RecordExpr _ -> assert false
  | GroupExpr (_, ExprList, es) ->
    let e = List.nth es proj in
    interpret_int_expr node_id ctx ty_ctx 0 e
  | GroupExpr _ -> assert false
  | StructUpdate _ -> assert false
  | ArrayConstr _ -> assert false
  | ArraySlice _-> assert false
  | ArrayConcat _ -> assert false
  | Quantifier _ -> assert false
  | When _ -> assert false
  | Current _ -> assert false
  | Condact (_, _, _, id, _, _)
  | Activate (_, id, _, _, _)
  | RestartEvery (_, id, _, _)
  | Call (_, id, _) ->
    let ty = Ctx.lookup_node_ty ty_ctx id |> get in
    let output_ty = match ty with
      | TArr (_, _, GroupType (_, tys)) -> List.nth tys proj
      | TArr (_, _, ty) -> ty
      | _ -> assert false
    in
    extract_bounds_from_type output_ty
  | Merge _ -> None, None
  | Pre (_, e) -> interpret_int_expr node_id ctx ty_ctx proj e
  | Last _
  | Fby _ -> assert false
  | Arrow (_, e1, e2) -> interpret_int_branch_expr node_id ctx ty_ctx proj e1 e2
  | CallParam _ -> assert false

and interpret_int_unary_expr node_id ctx ty_ctx op proj e =
  let (l, r) = interpret_int_expr node_id ctx ty_ctx proj e in
  (match op with
    | Uminus ->
      let l = (match l with
        | Some l -> Some (Numeral.neg l)
        | _ -> None)
      in
      let r = (match r with
        | Some r -> Some (Numeral.neg r)
        | _ -> None)
      in
      r, l
    | _ -> assert false)

and interpret_int_binary_expr node_id ctx ty_ctx proj op e1 e2 =
  let (l1, r1) = interpret_int_expr node_id ctx ty_ctx proj e1 in
  let (l2, r2) = interpret_int_expr node_id ctx ty_ctx proj e2 in
  let template op =
    let l = (match l1, l2 with
      | Some l1, Some l2 -> Some (op l1 l2)
      | _ -> None)
    in
    let r = (match r1, r2 with
      | Some r1, Some r2 -> Some (op r1 r2)
      | _ -> None)
    in
    l, r
  in
  (match op with
  | Mod ->
    let r = (match r1, r2 with
      | Some r1, Some r2 -> 
        let left = Numeral.abs r1 in
        let right = Numeral.abs r2 in
        let result = Numeral.(-) (Numeral.max left right) (Numeral.one) in
        Some result
      | _ -> None)
    in
    Some Numeral.zero, r
  | Minus -> template Numeral.(-)
  | Plus -> template Numeral.(+)
  | Times -> template Numeral.( * )
  | IntDiv -> template Numeral.(/)
  | _ -> assert false)

and interpret_int_branch_expr node_id ctx ty_ctx proj e1 e2 =
  let (l1, r1) = interpret_int_expr node_id ctx ty_ctx proj e1 in
  let (l2, r2) = interpret_int_expr node_id ctx ty_ctx proj e2 in
  let l = (match l1, l2 with
    | Some l1, Some l2 -> Some (Numeral.min l1 l2)
    | _ -> None)
  in
  let r = (match r1, r2 with
    | Some r1, Some r2 -> Some (Numeral.max r1 r2)
    | _ -> None)
  in
  l, r
