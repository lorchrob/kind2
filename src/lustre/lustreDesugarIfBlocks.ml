(* This file is part of the Kind 2 model checker.

   Copyright (c) 2022 by the Board of Trustees of the University of Iowa

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

module R = Res
module A = LustreAst
module AH = LustreAstHelpers
module GI = GeneratedIdentifiers
module AD = LustreAstDependencies
module Chk = LustreTypeChecker
module Ctx = TypeCheckerContext


type error_kind = 
  | MisplacedNodeItemError of A.node_item

let error_message error = match error with
  | MisplacedNodeItemError ni -> (match ni with
    | Body (Assert _) -> "Asserts are not allowed inside if blocks."
    | FrameBlock _ -> "Frame blocks are not allowed inside if blocks."
    | AnnotMain _ -> "Main annotations are not allowed inside if blocks."
    | AnnotProperty _ -> "Property annotations are not allowed inside if blocks."
    (* Other node items are allowed *)
    | _ -> assert false
  )

type error = [
  | `LustreDesugarIfBlocksError of Lib.position * error_kind
]

let ib_oracle_tree = HString.mk_hstring "ib_oracle" 

(** [i] is module state used to guarantee newly created identifiers are unique *)
let i = ref (0)

module LhsMap = struct
  include Map.Make (struct
    (* LHS and its corresponding position on the RHS *)
    type t = (A.eq_lhs * Lib.position)
    let compare lhs1 lhs2 = 
      let (A.StructDef (_, ss1)), _ = lhs1 in
      let (A.StructDef (_, ss2)), _ = lhs2 in
      let vars1 = A.SI.flatten (List.map AH.vars_of_struct_item ss1) in
      let vars2 = A.SI.flatten (List.map AH.vars_of_struct_item ss2) in 
      compare vars1 vars2
  end)
end

type cond_tree =
	| Leaf of A.expr option
	| Node of cond_tree * A.expr * cond_tree

let pos_list_map : (Lib.position * A.eq_lhs) list HString.HStringHashtbl.t = 
  HString.HStringHashtbl.create 20

let (let*) = R.(>>=)

let mk_error pos kind = Error (`LustreDesugarIfBlocksError (pos, kind))

(* This looks unsafe, but we only apply unwrap when we know from earlier stages
   in the pipeline that an error is not possible. *)
let unwrap result = match result with
  | Ok r -> r
  | Error _ -> assert false

(** Create a new oracle for use with if blocks. *)
let mk_fresh_ib_oracle pos ty =
  i := !i + 1;
  let prefix = HString.mk_hstring (string_of_int !i) in
  let name = HString.concat2 prefix (HString.mk_hstring GI.iboracle)  in
  A.Call(pos, name, []), 
  A.FuncDecl ( { A.start_pos = pos; A.end_pos = pos }, 
                (name, true, [], [], [(pos, HString.mk_hstring "input", ty, ClockTrue)], [], [], None))

let rec update_if_position_info node_id ni = match ni with
  | A.IfBlock (_, _, nis1, nis2) ->
    List.iter (update_if_position_info node_id) nis1;
    List.iter (update_if_position_info node_id) nis2;
  | Body (Equation (_, lhs, expr)) ->
    (* If there is already a binding, we want to retain the old 'if_info' *)
    let if_info = match HString.HStringHashtbl.find_opt pos_list_map node_id with
      | Some if_info2 -> (AH.pos_of_expr expr, lhs) :: if_info2
      | None -> [(AH.pos_of_expr expr, lhs)] 
    in
    HString.HStringHashtbl.add pos_list_map node_id if_info;
  | _ -> ()

(** Updates a tree (modeling an ITE structure) with a new equation. *)
let rec add_eq_to_tree conds rhs node = 
  (* let ppf = Format.std_formatter in *)
  match conds with
    | [] -> node
    | [(b, cond)] -> (
      match node with
        | Leaf (Some _) -> 
          (* shouldn't be possible *)
          assert false 
        | Leaf None -> 
          if b then (Node (Leaf (Some rhs), cond, Leaf None))
          else      (Node (Leaf None, cond, Leaf (Some rhs)))
        | Node (l, c, r) -> 
          if b then (Node (Leaf (Some rhs), c, r))
          else      (Node (l, c, Leaf (Some rhs)))
    )
    | (b, cond)::conds -> (
      match node with
        | Leaf (Some _) -> 
          (* shouldn't be possible *)
          assert false
        | Leaf None -> 
          if b then (Node (add_eq_to_tree conds rhs (Leaf None), cond, Leaf None))
          else (Node (Leaf None, cond, add_eq_to_tree conds rhs (Leaf None)))
        | Node (l, c, r) -> 
          if b then (Node (add_eq_to_tree conds rhs l, c, r))
          else (Node (l, c, add_eq_to_tree conds rhs r))
    )


(* If there are multiple recursive array definitions for the same array that use
   different locals, we need to translate to using only one set of locals for desugaring.
   For example,
   if c
   then 
     array[i] = expr1
   else
     array[j] = expr2
  
    desugars to array[i] = if c then expr1 else expr2. In this function, we update expr2
    to use the local "i" rather than "j".   *)
let update_recursive_array_locals map lhs expr = 
  match lhs with
    | A.StructDef (_, [ArrayDef (_, var1, inds1)]) -> (
      let matching_lhs = LhsMap.bindings map |> List.map fst |> List.map fst
      |> List.find_opt 
        (fun x -> (match x with 
          | A.StructDef (_, [ArrayDef (_, var2, _)]) when var1 = var2 -> true 
          | _ -> false)
        ) in 
      match matching_lhs with
        | Some (A.StructDef (_, [ArrayDef (_, _, inds2)]) as lhs2) -> 
        (* Replace instances with "inds1" with "inds2" *)
        lhs2, AH.replace_idents inds1 inds2 expr
        | _ -> lhs, expr
      ) 
    | _ -> lhs, expr


(** Converts an if block to a map of trees (creates a tree for each equation LHS) *)
let if_block_to_trees ib =
  let rec helper ib trees conds = (
    match ib with 
      | A.IfBlock (pos, cond, ni::nis, nis') -> (
        match ni with
          | A.Body (Equation (_, lhs, expr)) -> 
          let lhs, expr = update_recursive_array_locals trees lhs expr in
          (* Update corresponding tree (or add new tree if it doesn't exist) *)
          let trees = LhsMap.update (lhs, AH.pos_of_expr expr) 
            (fun tree -> match tree with
              | Some tree -> Some (add_eq_to_tree (conds @ [(true, cond)]) expr tree)
              | None -> Some (add_eq_to_tree (conds @ [(true, cond)]) expr (Leaf None)))
            trees 
          in
          (helper (A.IfBlock (pos, cond, nis, nis')) trees conds)
          (* Recurse, keeping track of our location within the if blocks using the 
             'conds' list. *)
          | A.IfBlock _ -> 
            let* res = (helper ni trees (conds @ [(true, cond)])) in
            (helper (A.IfBlock (pos, cond, nis, nis'))
                   res
                   conds)
          (* Misplaced frame block, annot main, or annot property *)
          | A.Body (Assert (pos, _)) 
          | A.FrameBlock (pos, _, _, _)
          | A.AnnotProperty (pos, _, _, _) 
          | A.AnnotMain (pos, _) -> mk_error pos (MisplacedNodeItemError ni)
        )
      | A.IfBlock (pos, cond, [], ni::nis) -> (
        match ni with
          | A.Body (Equation (_, lhs, expr)) -> 
            let lhs, expr = update_recursive_array_locals trees lhs expr in
            (* Update corresponding tree (or add new tree if it doesn't exist) *)
            let trees = LhsMap.update (lhs, AH.pos_of_expr expr) 
              (fun tree -> match tree with
                | Some tree -> Some (add_eq_to_tree (conds @ [(false, cond)]) expr tree)
                | None -> Some (add_eq_to_tree (conds @ [(false, cond)]) expr (Leaf None))) 
              trees 
            in
            (helper (A.IfBlock (pos, cond, [], nis)) trees conds)
          (* Recurse, keeping track of our location within the if blocks using the 
             'conds' list. *)
          | A.IfBlock _ -> 
            let* res = (helper ni trees (conds @ [(false, cond)])) in
            (helper (A.IfBlock (pos, cond, [], nis))
                   res
                   conds)
          (* Misplaced frame block, annot main, or annot property *)
          | A.FrameBlock (pos, _, _, _)
          | A.Body (Assert (pos, _)) 
          | A.AnnotProperty (pos, _, _, _)
          | A.AnnotMain (pos, _) -> mk_error pos (MisplacedNodeItemError ni)
        )
      (* We've processed everything in the if block. *)
      | A. IfBlock (_, _, [], []) -> R.ok (trees)
      (* shouldn't be possible *)
      | _ -> assert false
  ) in
  (helper ib LhsMap.empty [])
  
(** Converts a tree of conditions/expressions to an ITE expression. *)
let rec tree_to_ite pos node =
  match node with
    | Leaf Some expr -> expr
    | Leaf None -> A.Ident(pos, ib_oracle_tree)
    | Node (left, cond, right) -> 
      let left = tree_to_ite pos left in
      let right = tree_to_ite pos right in
      let pos = AH.pos_of_expr left in
      TernaryOp (pos, Ite, cond, left, right)

(** Returns the type associated with a tree. *)
let get_tree_type ctx lhs = 
  match lhs with
    | A.StructDef(_, [SingleIdent(_, i)]) -> (Ctx.lookup_ty ctx i) 
    | A.StructDef(_, [ArrayDef(_, i, _)]) -> (
      match (Ctx.lookup_ty ctx i) with
        (* Assignment in the form of A[i] = f(i), so the RHS type is no
           longer an array *)
        | Some (ArrayType (_, (ty, _))) -> Some ty
        | _ -> None
      )
    (* Other cases not possible *)
    | _ -> assert false


(** Fills empty spots in an ITE with oracles. *)
let rec fill_ite_with_oracles expr ty =
  match expr with
    | A.TernaryOp (pos, Ite, cond, e1, e2) -> 
      let e1, decls1 = fill_ite_with_oracles e1 ty in
      let e2, decls2 = fill_ite_with_oracles e2 ty in
      A.TernaryOp (pos, Ite, cond, e1, e2), decls1 @ decls2
    | Ident(p, s) when s = ib_oracle_tree -> 
      let expr, decl = mk_fresh_ib_oracle p ty in 
      expr, [decl]
    | _ -> expr, []

(** Helper function to determine if two trees are equal *)
let rec trees_eq node1 node2 = match node1, node2 with
  | Leaf (Some i), Leaf (Some j) -> (match (AH.syn_expr_equal None i j) with
    | Ok n -> n
    | Error _ -> false
  )
  | Node (l1, _, r1), Node (l2, _, r2) -> 
    trees_eq l1 l2 && trees_eq r1 r2
  | _ -> false

  
(** Removes redundancy from a binary tree. *)
let rec simplify_tree node = 
match node with
| Leaf _ -> node
| Node (i, str, j) -> 
  let i = simplify_tree i in
  let j = simplify_tree j in
  if trees_eq i j then i else
  Node (i, str, j)

(** Helper function for 'desugar_node_item' that converts IfBlocks to a list
    of ITEs. There are a number of steps in this process.

    Precondition: Multiple assignment has been removed from if blocks.

    Steps:
    1. Converting the if block to a list of trees modeling the ITEs.
    2. Doing any possible simplication on the above trees.
    3. Converting the trees to ITE expressions.
    4. Filling in the ITE expressions with oracles where variables are undefined.
    5. Returning lists of new local declarations and generated equations
    *)
let extract_equations_from_if node_id ctx ib =
  (* Keep track of where the if block variables are defined so that the position can
     be displayed in post analysis, eg ivcMcs.ml *)
  update_if_position_info node_id ib;
  let* tree_map = if_block_to_trees ib in
  let (lhss_poss, trees) = LhsMap.bindings (tree_map) |> List.split in
  let trees = List.map simplify_tree trees in  
  let lhs_poss = List.map (fun (A.StructDef (pos, _), _) -> pos) lhss_poss in
  let rhs_poss = List.map snd lhss_poss in
  let lhss = List.map fst lhss_poss in
  let ites = List.map2 tree_to_ite rhs_poss trees in
  let tys = (List.map (get_tree_type ctx) lhss) in 
  let tys = (List.map (fun x -> match x with | Some y -> y | None -> assert false (* not possible *)) 
                       tys) in
  let ites, gen_decls = List.map2 fill_ite_with_oracles ites tys |> List.split in
  (* Combine poss, lhss, and ites into a list of equations *)
  let eqs = (List.map2 (fun (a, b) c -> (A.Body (A.Equation (a, b, c)))) (List.combine lhs_poss lhss) ites) in
  R.ok (eqs, gen_decls |> List.flatten)


(** Desugar an individual node item. Given a node item, it returns any generated
    local declarations (if we introduce new local variables) and the converted
    node_item list in the form of ITEs).
*)
let rec desugar_node_item node_id ctx ni = match ni with
  | A.IfBlock _ as ib -> extract_equations_from_if node_id ctx ib
  | A.FrameBlock (pos, vars, nes, nis) -> 
    let* res = R.seq (List.map (desugar_node_item node_id ctx) nis) in
    let nis, gen_decls = List.split res in
    R.ok ([A.FrameBlock(pos, vars, nes, List.flatten nis)], List.flatten gen_decls)
  | _ -> R.ok ([ni], [])

(** Desugars an individual node declaration (removing IfBlocks). *)
let desugar_node_decl ctx decl = match decl with
  | A.FuncDecl (s, ((node_id, b, nps, cctds, ctds, nlds, nis, co) as d)) ->
    let ctx = Chk.get_node_ctx ctx d |> unwrap in
    let* res = R.seq (List.map (desugar_node_item node_id ctx) nis) in
    let nis, gen_decls = List.split res in
    let nis, gen_decls = List.flatten nis, List.flatten gen_decls in
    let ctx, gids, ns = List.fold_left (fun (acc_ctx, acc_gids, acc_ns) gen_decl -> match gen_decl with 
      | A.FuncDecl (_, (fun_id, _, _, _, [_, _, ty, _], _, _, _)) -> 
        Ctx.add_ty_node acc_ctx fun_id (A.TArr (Lib.dummy_pos, A.GroupType(Lib.dummy_pos, []), 
                                                               A.GroupType(Lib.dummy_pos, [ty]))),
        GI.StringMap.merge GI.union_keys2 acc_gids (GI.StringMap.singleton fun_id (GI.empty ())),
        AD.IMap.union (fun _ _ v2 -> Some v2) acc_ns (AD.IMap.singleton fun_id (AD.IntMap.empty))
      | _ -> assert false 
    ) (ctx, GI.StringMap.empty, AD.IMap.empty) gen_decls in
    R.ok (ctx, 
         gen_decls @ [A.FuncDecl (s, (node_id, b, nps, cctds, ctds, nlds, nis, co))], 
         gids,
         ns) 
  | A.NodeDecl (s, ((node_id, b, nps, cctds, ctds, nlds, nis, co) as d)) -> 
    let ctx = Chk.get_node_ctx ctx d |> unwrap in
    let* res = R.seq (List.map (desugar_node_item node_id ctx) nis) in
    let nis, gen_decls = List.split res in
    let nis, gen_decls = List.flatten nis, List.flatten gen_decls in
    let ctx, gids, ns = List.fold_left (fun (acc_ctx, acc_gids, acc_ns) gen_decl -> match gen_decl with 
      | A.FuncDecl (_, (fun_id, _, _, _, [_, _, ty, _], _, _, _)) -> 
        Ctx.add_ty_node acc_ctx fun_id (A.TArr (Lib.dummy_pos, A.GroupType(Lib.dummy_pos, []), 
                                                               A.GroupType(Lib.dummy_pos, [ty]))),
        GI.StringMap.merge GI.union_keys2 acc_gids (GI.StringMap.singleton fun_id (GI.empty ())),
        AD.IMap.union (fun _ _ v2 -> print_endline (HString.string_of_hstring fun_id); Some v2) acc_ns (AD.IMap.singleton fun_id (AD.IntMap.empty))
      | _ -> assert false 
    ) (ctx, GI.StringMap.empty, AD.IMap.empty) gen_decls in
    R.ok (ctx, 
         gen_decls @ [A.NodeDecl (s, (node_id, b, nps, cctds, ctds,  nlds, nis, co))], 
         gids,
         ns) 
  | _ -> R.ok (ctx, [decl], GI.StringMap.empty, AD.IMap.empty)


(** Desugars a declaration list to remove IfBlocks. Converts IfBlocks to
    declarative ITEs, filling in oracles if branches are undefined. *)
let desugar_if_blocks ctx sorted_node_contract_decls gids ns = 
  HString.HStringHashtbl.clear pos_list_map ;
  let* res = R.seq (List.map (desugar_node_decl ctx) sorted_node_contract_decls) in
  let split4 lst = 
    List.fold_left (fun (acc1, acc2, acc3, acc4) (a, b, c, d) -> 
      (a :: acc1, b :: acc2, c :: acc3, d :: acc4)
    ) ([], [], [], []) lst |> 
      (fun (a, b, c, d) -> (List.rev a, List.rev b, List.rev c, List.rev d)) 
  in
  let ctx, decls, gids2, ns2 = split4 res in
  let ctx = List.fold_left Ctx.union Ctx.empty_tc_context ctx in 
  let gids2 = List.fold_left (GI.StringMap.merge GI.union_keys2) GI.StringMap.empty gids2 in
  let gids = GI.StringMap.merge GI.union_keys2 gids gids2 in
  let ns = List.fold_left (AD.IMap.union (fun _ _ v2 -> Some v2)) ns ns2 in 
  R.ok (ctx, List.flatten decls, gids, ns)

  (* TODO: Update node summary data to include new generated imported functions. Debug. *)