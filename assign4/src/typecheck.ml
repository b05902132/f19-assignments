open Flags
open Core
open Result.Monad_infix
open Ast

let aequiv = Ast_util.Type.aequiv

exception Unimplemented

let rec typecheck_expr (ctx : Type.t String.Map.t) (e : Expr.t)
  : (Type.t, string) Result.t =

  match e with
  | Expr.Num _ -> Ok Type.Num
  | Expr.Unit -> Ok Type.Unit
  | Expr.Var x ->
    ( match String.Map.find ctx x with
      | Some t -> Ok t
      | None -> Error (Printf.sprintf "Unbound variable %s" x) )

  | Expr.Binop {left; right; _} ->
    typecheck_expr ctx left >>= fun tau_left ->
    typecheck_expr ctx right >>= fun tau_right ->
    (match (tau_left, tau_right) with
     | (Type.Num, Type.Num) -> Ok Type.Num
     | _ -> Error (
       Printf.sprintf
         "Binary operands have incompatible types: (%s : %s), (%s : %s)"
         (Expr.to_string left) (Type.to_string tau_left)
         (Expr.to_string right) (Type.to_string tau_right)))

  | Expr.Relop {left; right;_} ->
    typecheck_expr ctx left >>= fun left_t ->
    typecheck_expr ctx right >>= fun right_t ->
    (match (left_t, right_t) with
      | (Type.Num, Type.Num) -> Ok Type.Bool
      | _ -> Error (
          Printf.sprintf "Relop operands have incompatible types: (%s : %s) and (%s : %s)"
          (Expr.to_string left) (Type.to_string left_t)
          (Expr.to_string right) (Type.to_string right_t) ) )

  | Expr.True  -> Ok Type.Bool
  | Expr.False -> Ok Type.Bool
  | (Expr.And {left; right} | Expr.Or {left; right}) ->
    typecheck_expr ctx left >>= fun left_t ->
    typecheck_expr ctx right >>= fun right_t ->
    ( match (left_t, right_t) with
      | (Type.Bool, Type.Bool) -> Ok Type.Bool
      | _ -> Error (
          Printf.sprintf "Logical operands have incompatible types: (%s : %s) and (%s : %s)"
            (Expr.to_string left) (Type.to_string left_t)
            (Expr.to_string right) (Type.to_string right_t) ) )

  | Expr.If {cond; then_; else_} ->
      typecheck_expr ctx cond >>= fun cond_t ->
      typecheck_expr ctx then_ >>= fun then_t ->
      typecheck_expr ctx else_ >>= fun else_t ->
      ( if not (aequiv cond_t Type.bool)
        then Error (
            Printf.sprintf "If condition expression %s has type %s, expected bool"
              (Expr.to_string cond) (Type.to_string cond_t) )
        else if not (aequiv then_t else_t)
        then Error ( Printf.sprintf
                     "Then branch %s has type %s, not matching else branch type %s of type %s"
                     (Expr.to_string then_) (Type.to_string then_t)
                     (Expr.to_string else_) (Type.to_string else_t) )
        else Ok then_t)
  | Expr.App {lam; arg} ->
    typecheck_expr ctx arg >>= fun arg_t ->
    typecheck_expr ctx lam >>= fun lam_t ->
    let arg_expr = arg in
    ( match lam_t with
      | Fn {arg; ret} ->
        if aequiv arg arg_t then Ok ret
        else Error (Printf.sprintf "Attempted to call function %s of expected argument type %s with argument expression %s of actual type %s"
                    (Expr.to_string lam) (Type.to_string arg)
                    (Expr.to_string arg_expr) (Type.to_string arg_t))

      | _ -> Error ( Printf.sprintf "Attempted to call expression %s of non-function type %s as a function"
                     (Expr.to_string lam) (Type.to_string lam_t) )
    )
  | Expr.Lam {x; tau; e} ->
    let ctx = String.Map.set ctx ~key:x ~data:tau in
    typecheck_expr ctx e >>= fun ret ->
      Ok (Type.Fn {arg = tau ; ret} )

  | Expr.Pair {left; right} ->
    typecheck_expr ctx left >>= fun left_t ->
    typecheck_expr ctx right >>= fun right_t ->
    Ok (Type.Product {left=left_t; right=right_t})
  | Expr.Project {e; d} ->
    typecheck_expr ctx e >>= fun e_t ->
    ( match e_t with
      | Type.Product {left; right} ->
        (match d with
         | Left -> Ok left
         | Right -> Ok right)
      | _ -> Error (Printf.sprintf "Attempted to project out of non-tuple %s with type %s"
                    (Expr.to_string e) (Type.to_string e_t) ) )
  | Expr.Inject {e; d; tau} ->
    typecheck_expr ctx e >>= fun e_t ->
    ( match tau with
      | Type.Sum {left; right} ->
        let expected_expr_t = (match d with | Left -> left | Right ->right) in
        if aequiv expected_expr_t e_t then Ok tau
        else Error (Printf.sprintf "Attempted to inject %s with actual type %s into sum type %s"
                    (Expr.to_string e) (Type.to_string e_t) (Type.to_string tau) )

      | _ -> Error (Printf.sprintf "Attempted to inject into non-sum type %s" (Type.to_string tau) )
    )

  | Expr.Case {e; xleft; eleft; xright; eright} ->
    typecheck_expr ctx e >>= fun e_t ->
    ( match e_t with
      | Type.Sum {left; right} ->
        let left_ctx = String.Map.set ctx ~key:xleft ~data:left in
        let right_ctx = String.Map.set ctx ~key:xright~data:right in
        typecheck_expr left_ctx eleft >>= fun l_type ->
        typecheck_expr right_ctx eright >>= fun r_type ->
        if aequiv l_type r_type then Ok l_type
        else Error (Printf.sprintf "Case branch types aren't the same: %s != %s"
                      (Type.to_string l_type) (Type.to_string r_type) )

      | _ -> Error (Printf.sprintf "Casing on expression %s of non-sum type %s"
                      (Expr.to_string e) (Type.to_string e_t) )
    )

  | Expr.Fix {x; tau; e} ->
    let new_ctx = String.Map.set ctx ~key:x ~data:tau in
    typecheck_expr new_ctx e >>= fun tau' ->
    if aequiv tau tau' then Ok tau
    else Error (Printf.sprintf "Fixpoint expression %s of type %s does not match argument type %s"
                  (Expr.to_string e) (Type.to_string tau') (Type.to_string tau) )
  | Expr.TyLam {a; e} ->
    typecheck_expr ctx e >>= fun e_t -> Ok (Type.Forall {a; tau=e_t} )

  | Expr.TyApp {e; tau} ->
    typecheck_expr ctx e >>= fun e_t ->
    ( match e_t with
      | Type.Forall tyExpr-> Ok (Ast_util.Type.substitute tyExpr.a tau tyExpr.tau)
      | _ -> Error (Printf.sprintf "Type-application on non-polymorphic expression %s of type %s"
                      (Expr.to_string e) (Type.to_string e_t))
    )

  | Expr.Fold_ {e; tau} ->
    typecheck_expr ctx e >>= fun e_t ->
    ( match tau with
      | Type.Rec r ->
        let tau_exp = Ast_util.Type.substitute r.a tau r.tau in
        if aequiv tau_exp e_t
            then Ok tau
            else Error ( Printf.sprintf "Folded expr %s of type %s does not match recursive type one-step unfolding %s"
                            (Expr.to_string e) (Type.to_string e_t) (Type.to_string tau_exp)
                       )
      | _ -> Error (Printf.sprintf "Provided fold type %s is not recursive" (Type.to_string tau) )
    )
  | Expr.Unfold e ->
    typecheck_expr ctx e >>= fun e_t ->
    ( match e_t with
      | Type.Rec r -> Ok (Ast_util.Type.substitute r.a e_t r.tau)
      | _ -> Error ( Printf.sprintf "Unfolding expression %s with non-recursive type %s"
                       (Expr.to_string e) (Type.to_string e_t) )
    )

  (* Add more cases here! *)

  | _ -> raise Unimplemented

let typecheck t = typecheck_expr String.Map.empty t

let inline_tests () =
  let p_ex = Parser.parse_expr_exn in
  let p_ty = Parser.parse_type_exn in
  let e1 = p_ex "fun (x : num) -> x" in
  assert (typecheck e1 = Ok(p_ty "num -> num"));

  let e2 = p_ex "fun (x : num) -> y" in
  assert (Result.is_error (typecheck e2));

  let t3 = p_ex "(fun (x : num) -> x) 3"in
  assert (typecheck t3 = Ok(p_ty "num"));

  let t4 = p_ex "((fun (x : num) -> x) 3) 3" in
  assert (Result.is_error (typecheck t4));

  let t5 = p_ex "0 + (fun (x : num) -> x)" in
  assert (Result.is_error (typecheck t5))

(* Uncomment the line below when you want to run the inline tests. *)
let () = inline_tests ()
