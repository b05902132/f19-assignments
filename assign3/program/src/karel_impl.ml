open Core
open Option.Monad_infix

exception Unimplemented

(* Set this to true to print out intermediate state between Karel steps *)
let debug = true

type cell =
  | Empty
  | Wall
  | Beeper

type grid = cell list list

type dir =
  | North
  | West
  | South
  | East

type pos = int * int

type state = {
  karel_pos : pos;
  karel_dir : dir;
  grid : grid;
}

let get_cell (grid : grid) ((i, j) : pos) : cell option =
  (List.nth grid j) >>= fun l -> List.nth l i
;;

let set_cell (grid : grid) ((i, j) : pos) (cell : cell) : grid =
  List.mapi grid ~f:(fun j' l ->
    if j = j' then List.mapi l ~f:(fun i' c -> if i = i' then cell else c)
    else l)
;;

let state_to_string (state : state) : string =
  let cell_symbol: cell -> char = fun s -> match s with
    | Empty -> '.'
    | Beeper -> 'B'
    | Wall -> 'x'
  in
  let symbol_grid : char list list = List.map state.grid ~f:(List.map ~f:cell_symbol) in
  let karel_grid: char list list = List.mapi symbol_grid
      ~f:(fun (y:int) row -> (List.mapi row ~f:(fun (x:int) (c:char) -> if (x,y) = state.karel_pos then 'K' else c)) )
  in
  let row_list : string list = List.map karel_grid ~f:String.of_char_list in
  List.fold_left row_list ~init:"" ~f:(fun l r -> (l ^ r) ^ ("\n"))
;;


let empty_grid (m : int) (n : int) : grid =
  List.map (List.range 0 m) ~f:(fun _ ->
    List.map (List.range 0 n) ~f:(fun _ -> Empty))
;;

let relative_to : pos -> dir -> pos = 
  fun (x, y) dir -> match dir with
    | North -> (x, y-1)
    | South -> (x, y+1)
    | East -> (x+1, y)
    | West -> (x-1, y)

let rotate_counterclockwise : dir -> dir = 
  fun d -> match d with
    | North -> West
    | West -> South
    | South -> East
    | East -> North

type predicate =
  | FrontIs of cell
  | NoBeepersPresent
  | Facing of dir
  | Not of predicate

type instruction =
  | Move
  | TurnLeft
  | PickBeeper
  | PutBeeper
  | While of predicate * instruction list
  | If of predicate * instruction list * instruction list

let rec predicate_to_string (pred : predicate) : string =
  match pred with
  | FrontIs c ->
    let cellstr = match c with
      | Empty -> "Empty" | Beeper -> "Beeper" | Wall -> "Wall"
    in
    Printf.sprintf "FrontIs(%s)" cellstr
  | NoBeepersPresent -> "NoBeepersPresent"
  | Facing dir ->
    let dirstr = match dir with
      | North -> "North" | South -> "South" | East -> "East" | West -> "West"
    in
    Printf.sprintf "Facing(%s)" dirstr
  | Not pred' -> Printf.sprintf "Not(%s)" (predicate_to_string pred')

let rec instruction_to_string (instr : instruction) : string =
  match instr with
  | Move -> "Move"
  | TurnLeft -> "TurnLeft"
  | PickBeeper -> "PickBeeper"
  | PutBeeper -> "PutBeeper"
  | While (pred, instrs) ->
    Printf.sprintf "While(%s, [%s])"
      (predicate_to_string pred)
      (instruction_list_to_string instrs)
  | If (pred, then_, else_) ->
    Printf.sprintf "If(%s, [%s], [%s])"
      (predicate_to_string pred)
      (instruction_list_to_string then_)
      (instruction_list_to_string else_)
and instruction_list_to_string (instrs: instruction list) : string =
  String.concat ~sep:", " (List.map ~f:instruction_to_string instrs)


let rec eval_pred (state : state) (pred : predicate) : bool =
  match pred with
  | Not p -> (eval_pred state p) <> true
  | Facing d -> state.karel_dir = d
  | FrontIs c -> (match get_cell state.grid (relative_to state.karel_pos state.karel_dir) with
    | None -> c = Wall
    | (Some d) -> c = d
    )
  | NoBeepersPresent -> (match get_cell state.grid state.karel_pos with
    | Some c -> c <> Beeper
    | None -> false
    )

let rec step (state : state) (code : instruction) : state =
  match code with 
  | Move -> 
    (let target_pos = relative_to state.karel_pos state.karel_dir in
     match get_cell state.grid target_pos with
     | None -> state
     | Some Wall -> state
     | _ -> {state with karel_pos = target_pos }
    )
  | TurnLeft -> {state with karel_dir = rotate_counterclockwise state.karel_dir}
  | PickBeeper -> 
    (match get_cell state.grid state.karel_pos with
     | Some Beeper -> {state with grid = set_cell state.grid state.karel_pos Empty}
     | _ -> state
    )
  | PutBeeper ->
    (match get_cell state.grid state.karel_pos with
     | Some Empty -> {state with grid = set_cell state.grid state.karel_pos Beeper}
     | _ -> state
    )
  | While (p, instrs) -> if eval_pred state p 
    then (let new_state = step_list state instrs in step new_state (While (p, instrs)) )
    else state
  | If (p, then_, else_) -> if eval_pred state p then step_list state then_ else step_list state else_

and step_list (state : state) (instrs : instruction list) : state =
  List.fold instrs ~init:state ~f:(fun state instr ->
    if debug then
       (Printf.printf "Executing instruction %s...\n"
          (instruction_to_string instr);
        let state' = step state instr in
        Printf.printf "Executed instruction %s. New state:\n%s\n"
          (instruction_to_string instr)
          (state_to_string state');
        state')
     else
       step state instr)

;;

let checkers_algo : instruction list = [
  While (Not (FrontIs Wall),  [
      PutBeeper;
      While (Not (FrontIs Wall), [Move; If (FrontIs Wall, [], [Move;PutBeeper]) ]);
      If (Facing East, [TurnLeft; TurnLeft; TurnLeft], [TurnLeft] );
      (* currently facing south *)
      If (FrontIs Wall, [], [
          If (NoBeepersPresent, [
              Move; TurnLeft; If (FrontIs Wall, [TurnLeft; TurnLeft;], [])
            ], [ (* else *)
              Move; TurnLeft; If (FrontIs Wall, [TurnLeft; TurnLeft;], []); Move
            ])
        ])
  ])
]
