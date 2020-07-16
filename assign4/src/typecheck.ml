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

  | Expr.Binop {left; right; _} ->
    typecheck_expr ctx left >>= fun tau_left ->
    typecheck_expr ctx right >>= fun tau_right ->
    (match (tau_left, tau_right) with
     | (Type.Num, Type.Num) -> Ok Type.Num
     | _ -> Error (
       Printf.sprintf
         "Binary operands have incompatible types: (%s : %s) and (%s : %s)"
         (Expr.to_string left) (Type.to_string tau_left)
         (Expr.to_string right) (Type.to_string tau_right)))

  | Expr.Relop {left; right;_} ->
    typecheck_expr ctx left >>= fun left_t ->
    typecheck_expr ctx right >>= fun right_t ->
    (match (left_t, right_t) with
      | (Type.Num, Type.Num) -> Ok Type.Bool
      | _ -> Error (
          Printf.sprintf "Can't compare (%s: %s) and (%s: %s)! (Both need to be Num)"
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
          Printf.sprintf "Boolean operants requires boolean type: (%s: %s), (%s: %s)"
            (Expr.to_string left) (Type.to_string left_t)
            (Expr.to_string right) (Type.to_string right_t) ) )

  | Expr.If {cond; then_; else_} ->
      typecheck_expr ctx cond >>= fun cond_t ->
      typecheck_expr ctx then_ >>= fun then_t ->
      typecheck_expr ctx else_ >>= fun else_t ->
      ( if not (aequiv cond_t Type.bool)
        then Error (
            Printf.sprintf "If expression requires a Bool but the type of \"%s\" is %s!"
              (Expr.to_string cond) (Type.to_string cond_t) )
        else if not (aequiv then_t else_t)
        then Error ( Printf.sprintf
                     "The expressions following then and else should be of the same type: (%s : %s) (%s : %s)"
                     (Expr.to_string then_) (Type.to_string then_t)
                     (Expr.to_string else_) (Type.to_string else_t) )
        else Ok then_t)

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
(* let () = inline_tests () *)
