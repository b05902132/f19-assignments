open Core

exception Unimplemented

let main () =
  let rec gcd (m : int) (n : int) : int =
    if n = 0 then m
    else if m = 0 then n
    else if m = n then m
    else if m > n then gcd n (m % n)
                  else gcd m (n % m)
  in

  assert (gcd 5 2 = 1);
  assert (gcd 10 2 = 2);
  assert (gcd 48 18 = 6);

  let do_num(i: int) :unit = 
      if i % 15 = 0 then
          Printf.printf "fizzbuzz"
      else if i % 3 = 0 then
          Printf.printf "fizz"
      else if i % 5 = 0 then
          Printf.printf "buzz"
      else ()
  in

  let rec fizz_buzz (n : int) : unit =
    if n < 0 then
      ()
    else (
      fizz_buzz (n - 1);
      do_num n
    )
  in

  let read_line () : string =
    match In_channel.input_line In_channel.stdin with
    | Some s -> s
    | None -> assert false
  in

  let rec read_password (password : string) : unit =
    let () = Printf.printf "%s!" "Please enter your password:" in
    let read = read_line () in
    if read == password then 
      Printf.printf "%s!" "success!"
    else 
      read_password password
  in

  (* Uncomment the line below to test read_password *)
  (* let () = read_password "password" in *)

  let rec substring_match (pattern : string) (source : string) : int option =
    let len = String.length pattern in
    if String.length source < len then
      None
    else 
      if String.slice source 0 len = pattern then Some 0
      else match substring_match pattern (String.slice source 1 (String.length source)) with
        | Some n -> Some (n + 1)
        | None -> None
  in

  assert (substring_match "foo" "foobar" = Some 0);
  assert (substring_match "foo" "barfoo" = Some 3);
  assert (substring_match "z" "foobar" = None)

let () = main ()
