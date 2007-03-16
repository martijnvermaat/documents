(* Oplossingen opdrachten practicum 2 *)
(* Tweede deel *)


(* Opdracht 1 *)

let rec churchnumeral n =
  if n = 0 then fun s -> fun z -> z
  else fun s -> fun z -> churchnumeral (n-1) s (s z);;

let backtonatural n =
  n (fun x -> x + 1) 0;;

(*
(* 'probeer, probeer' *)
backtonatural (churchnumeral 5);;
*)


(* Opdracht 2 *)

let equality c1 c2 = (backtonatural c1) = (backtonatural c2)


(* Opdracht 3 *)

let successor x s z = s (x s z)


(* Opdracht 4 *)

let successor' x s z = x s (s z)


(* Opdracht 5 *)

let test1 f n = backtonatural (f (churchnumeral n))

(* In Haskell:
     test1 f = backtonatural . f . churchnumeral
   Maar ik ken geen functie compositie operator in
   OCaml. *)


(* Opdracht 6 *)

let addition x y s z = x s (y s z);;

let multiplication x y s = x (y s);;

let exponentation x y = y x;;


(* Opdracht 7 *)

let test2 f n m = backtonatural (f
                                   (churchnumeral n)
                                   (churchnumeral m))
