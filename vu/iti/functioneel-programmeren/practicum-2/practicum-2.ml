(* Oplossingen opdrachten practicum 2 *)


(* Opdracht 1 *)

let rec filter f l = match l with
    []    -> []
  | x::xs ->
      if f x then
        x::(filter f xs)
      else
        filter f xs


(* Opdracht 2 *)

(* hm ? *)


(* Opdracht 3 *)

exception List_too_short of string

let rec take n l = match n with
    0 -> []
  | n -> match l with
        []    -> raise (List_too_short "take")
      | x::xs -> x::(take (n-1) xs)


(* Opdracht 4 *)

let rec drop n l = match n with
    0 -> l
  | n -> match l with
        []    -> raise (List_too_short "drop")
      | x::xs -> drop (n-1) xs


(* Opdracht 5 *)

let rec foldr f e l = match l with
    []    -> e
  | x::xs -> f x (foldr f e xs)

(*
  foldl: (((((e + 1) + 2) + 3) + 4) + 5)
  foldr: (1 + (2 + (3 + (4 + (5 + e)))))

  foldl is moeilijker (foldr op reverse?)
*)


(* Opdracht 6 *)
