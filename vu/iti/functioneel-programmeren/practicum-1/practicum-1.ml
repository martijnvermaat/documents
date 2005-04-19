(* Oplossingen opdrachten practicum 1 *)


(* Opdracht 1 *)

let rec length l = match l with
    []    -> 0
  | x::xs -> 1 + (length xs)


(* Opdracht 2 *)

let rec append l l' = match l with
    []    -> l'
  | x::xs -> x::(append xs l')


(* Opdracht 3 *)

let rec reverse l = match l with
    []    -> []
  | x::xs -> append (reverse xs) [x]


(* Opdracht 4 *)

let rec member e l = match l with
    []    -> false
  | x::xs -> x = e || member e xs


(* Opdracht 5 *)

let rec insert e l = match l with
    []    -> [e]
  | x::xs ->
      if e <= x then
        e::x::xs
      else
        x::(insert e xs)


(* Opdracht 6 *)

let rec insertionsort l = match l with
    []    -> []
  | x::xs -> insert x (insertionsort xs)
