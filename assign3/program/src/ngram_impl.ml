open Core

exception Unimplemented
exception Impossible

type ngram = string list
type ngram_map = (ngram, string list) Map.Poly.t
type word_distribution = float String.Map.t

let rec remove_last_impl1 (l : string list) : string list =
  match l with
  | [] -> []
  | [x] -> []
  | x::xs -> x :: (remove_last_impl1 xs)
;;

assert (remove_last_impl1 ["a"; "b"] = ["a"]);
;;

let remove_last_impl2 (l : string list) : string list =
  let len = List.length l in
  List.filteri ~f:(fun i _ -> i + 1 <> len) l
;;

assert (remove_last_impl2 ["a"; "b"] = ["a"]);
;;

let rec split_last (l: 'a list) : 'a list * 'a option = 
  match l with
  | [] -> ([], None)
  | [x] -> ([], Some x)
  | x::xs -> let (ys, last) = split_last xs in (x::ys, last)
;;

let compute_ngrams (l : string list) (n : int) : string list list =
  (* [a; b; c] -> [ []; [c]; [c;b]; [c;b;a] ] *)
  let (_, rev_history) = List.fold_left l ~init:([], [[]])
      ~f:(fun (ngram, accu) word -> let new_ngram = List.take (word::ngram) n in (new_ngram, new_ngram::accu))
  in
  let history : string list list = List.fold_left rev_history ~init:[] ~f:(fun accu ngram -> (List.rev ngram)::accu) in
  List.drop history n
;;


assert (compute_ngrams ["a"; "b"; "c"] 2 = [["a"; "b"]; ["b"; "c"]]);
;;

let ngram_to_string ng =
  Printf.sprintf "[%s]" (String.concat ~sep:", " ng)
;;

let ngram_map_new () : ngram_map =
  Map.Poly.empty
;;

let ngram_map_add (map : ngram_map) (ngram : ngram) : ngram_map =
  let (key, value) = split_last ngram in
  let add (map : ngram_map) (key: ngram) (value: string) =
    match Map.Poly.find map key with
    | None -> Map.Poly.set map ~key:key ~data:[value]
    | Some l -> Map.Poly.set map ~key:key ~data:(value::l)
  in
  match value with
  | None -> map
  | Some(value) -> add map key value 
;;

let () =
  let map = ngram_map_new () in
  let map = ngram_map_add map ["a"; "b"; "c"] in
  assert (Map.Poly.find map ["a"; "b"] = Some ["c"] );
  assert (Map.Poly.find map ["a"; "c"] = None );
  let map = ngram_map_add map ["a"; "b"; "d"] in
  assert (Map.Poly.find map ["a"; "b"] = Some ["d"; "c"] );
  let map = ngram_map_add map ["a"; "b"; "d"] in
  assert (Map.Poly.find map ["a"; "b"] = Some ["d"; "d"; "c"] );
  let map = ngram_map_add map ["b"; "b"; "d"] in
  assert (Map.Poly.find map ["a"; "b"] = Some ["d"; "d"; "c"] );
  assert (Map.Poly.find map ["b"; "b"] = Some ["d"] );
;;

let calc_distribution (l: string list) : word_distribution = 
  let alist : (string * unit) list = List.map l ~f:(fun x -> (x, ()) ) in
  let word_count : int String.Map.t = String.Map.of_alist_fold alist ~init:0 ~f:(fun x _ -> x+1) in
  let total_count = List.length l in
  String.Map.map word_count ~f:(fun x -> (Float.of_int x) /. (Float.of_int total_count) )
;;

let ngram_map_distribution (map : ngram_map) (ngram : ngram)
  : word_distribution option =
  match Map.Poly.find map ngram with
  | None -> None
  | Some ngram -> Some (calc_distribution ngram)
;;

let distribution_to_string (dist : word_distribution) : string =
  Sexp.to_string_hum (String.Map.sexp_of_t Float.sexp_of_t dist)
;;

let sample_distribution (dist : word_distribution) : string =
  let rand = Random.float 1. in
  let step ~key ~data (num, res) = match res with
    | Some k -> (num, Some k)
    | None -> let new_num = num -. data in if new_num <=. 0. then (0., Some key) else (new_num, None)
  in
  let (_, Some res) = String.Map.fold dist ~init:(rand, None) ~f:step in
  res
;;

let rec sample_n (map : ngram_map) (ng : ngram) (n : int) : string list =
  if n <= 0 then [] else
    let (Some word_freq) = ngram_map_distribution map ng in
    let word = sample_distribution word_freq in
    let (_::tail) = ng in
    let new_ng = tail @ [word] in
    word :: sample_n map new_ng (n-1)
    
;;
