(* Oplossingen opdrachten practicum 2 *)
(* Tweede deel *)


(* Opdracht 1 *)

let rec churchnumeral n =
  if n = 0 then fun s -> fun z -> z
  else fun s -> fun z -> churchnumeral (n-1) s (s z);;

let backtonatural n =
  n (fun x -> x + 1) 0;;

backtonatural (churchnumeral 5);;
