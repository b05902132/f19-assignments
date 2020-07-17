open Flags
open Core
open Ast

type outcome =
  | Step of Expr.t
  | Val

exception RuntimeError of string

let rec trystep (e : Expr.t) : outcome =
  match e with
  | (Expr.Lam _ | Expr.Num _ | Expr.True | Expr.False | Expr.Pair _ | Expr.Unit
    | Expr.Inject _ | Expr.TyLam _ | Expr.Export _ | Expr.Fold_ _) -> Val

  | Expr.Binop {binop; left; right} ->
    (left, fun left' -> Expr.Binop {left = left'; binop; right;}) |-> fun () ->
    (right, (fun right' -> Expr.Binop {right = right'; binop; left})) |-> fun () ->
    let (Expr.Num n1, Expr.Num n2) = (left, right) in
    let f = match binop with
      | Expr.Add -> (+)
      | Expr.Sub -> (-)
      | Expr.Mul -> ( * )
      | Expr.Div -> (/)
    in
    Step (Expr.Num (f n1 n2) )
  | Expr.Relop {relop; left; right} ->
    (left, fun left' -> Expr.Relop{relop; left=left'; right}) |-> fun() ->
    (right, fun right' -> Expr.Relop {relop; left; right=right'}) |-> fun() ->
    let (Expr.Num l_num, Expr.Num r_num) = (left, right) in
    let res = match relop with
      | Expr.Lt -> l_num < r_num
      | Expr.Gt -> l_num > r_num
      | Expr.Eq -> l_num = r_num
    in
    Step (if res then Expr.True else Expr.False)

  | Expr.If {cond; then_; else_} ->
    (cond, fun cond' -> Expr.If {cond = cond'; then_; else_}) |-> fun () ->
      (match cond with
      | Expr.True -> Step then_
      | Expr.False -> Step else_ )

  | Expr.And {left; right} ->
    (left, fun left' -> Expr.And {left=left'; right}) |-> fun () ->
      (right, fun right' -> Expr.And {left; right=right'}) |-> fun () ->
      if (left, right) = (Expr.True, Expr.True) then Step Expr.True else Step Expr.False

  | Expr.Or {left; right} ->
    (left, fun left' -> Expr.Or {left=left'; right}) |-> fun () ->
      (right, fun right' -> Expr.Or {left; right=right'}) |-> fun () ->
      if (left, right) = (Expr.False, Expr.False) then Step Expr.False else Step Expr.True

  | Expr.App {lam; arg} ->
    (lam, fun lam' -> Expr.App {lam=lam'; arg}) |-> fun () ->
    (arg, fun arg' -> Expr.App {lam;arg=arg'}) |-> fun () ->
      Step (match lam with Expr.Lam{x; e; _} -> Ast_util.Expr.substitute x arg e)

  | Expr.Project {e; d} ->
    (e, fun e' -> Expr.Project {e=e'; d}) |-> fun() ->
      (match e with Expr.Pair {left; right} ->
         (match d with
          | Left -> Step left
          | Right -> Step right
         )
      )
  | Expr.Case {e; xleft; eleft; xright; eright} ->
    (e, fun e' -> Expr.Case { e=e'; xleft; eleft; xright; eright}) |-> fun() ->
    ( match e with Expr.Inject{e; d; _} ->
      Step ( match d with
        | Left -> Ast_util.Expr.substitute xleft e eleft
        | Right -> Ast_util.Expr.substitute xright e eright
      )
    )



  (* Add more cases here! *)

  | _ -> raise (RuntimeError (
    Printf.sprintf "Reached a stuck state at expression: %s" (Expr.to_string e)))

and (|->) ((e, hole) : Expr.t * (Expr.t -> Expr.t)) (next : unit -> outcome)
  : outcome =
  match trystep e with Step e' -> Step (hole e') | Val -> next ()

let rec eval e =
  match trystep e with
  | Step e' ->
    (if extra_verbose () then
       Printf.printf "Stepped:\n%s\n|->\n%s\n\n"
         (Expr.to_string e) (Expr.to_string e'));
    eval e'
  | Val -> Ok e

let inline_tests () =
  let p = Parser.parse_expr_exn in
  let e1 = p "2 + 3" in
  assert (trystep e1 = Step(Expr.Num 5));

  let e2 = p "(fun (x : num) -> x) 3" in
  assert (trystep e2 = Step(Expr.Num 3))

(* Uncomment the line below when you want to run the inline tests. *)
let () = inline_tests ()
