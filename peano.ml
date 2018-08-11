open List;;

type peano = Z | S of peano;; 

let rec peano_of_int a = match a with
	| 0 -> Z
	| _ -> S (peano_of_int (a - 1));;

let rec int_of_peano p = match p with
    Z -> 0
  | S x -> 1 + int_of_peano x;;

let rec add a b = match b with
	| Z -> a
	| S b' -> S (add a b');;

let rec sub a b = match b with
	| Z -> a
	| S b' -> match a with
		| Z -> Z
		| S a' -> sub a' b';;

let rec mul a b = match b with
	| Z -> Z
	| S b' -> add (mul a b') a;;

let inc a = S a;;

let rec power a b = match b with
	| Z -> S Z
	| S b' -> mul (power a b') a;;
