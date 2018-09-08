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

let rev l = List.fold_left (fun d s -> s::d) [] l;;

let split_half l = List.fold_right (fun x (left, right, n) -> if n > 0 then (x::left, right, n - 1)
															else (left, x::right, n)) l ([], [], (List.length l / 2))

let rec merge a b = match a with 
				| [] -> b
				| (x::xs) -> match b with
							| [] -> a
							| (y::ys) -> if y < x then y::(merge a ys)
													  else x::(merge xs b);;

let rec merge_sort li = match li with 
					| [x] -> [x]
					| l -> let (left, right, _) = (split_half l) in merge (merge_sort left) (merge_sort right);;



let rec print_list l = match l with
					| (x::xs) -> print_int x; print_string " "; print_list xs
					| [] -> ();;

let rec create_list n = if n = 0 then [] else (n :: create_list (n - 1));;

let print_list l = print_string (String.concat " " (List.map string_of_int l));;

print_list (rev [1;2;3]);;
print_string ("\n");;
print_list (merge_sort [3;2;1;4]);;

type lambda = Var of string | Abs of string * lambda | App of lambda * lambda;;

let isSymbol ch = match ch with
			 | '(' -> 1
			 | ')' -> 1
			 | ' ' -> 1
			 | '\\' -> 1
			 | '.' -> 1
			 | _ -> 0;;
let tail s = match s with
			| [] -> []
			| x::xs -> xs;;
let head s = match s with
			| [] -> ""
			| x::xs -> x;;
let tailS s = match s with	
			| "" -> ""
			| _ -> String.sub s 1 (String.length s - 1);;
let rec break s n = match s with
			| "" -> ("", "")
			| _ -> let x = s.[0] in let xs = tailS s in 
							if ((isSymbol x) = 1) then 
								if n = 0 then 
									((String.make 1 x), xs) 
								else ("", (String.make 1 x)^xs) 
							else let (a, b) = break xs (n + 1) in ((String.make 1 x)^a, b);;

let rec di s = match s with
						| "" -> [""]
						| _ -> let (fst, snd) = break s 0 in 
								List.filter (fun x -> x <> " " && x <> "") (List.append [fst] (di snd));;

let temp = Var "x";;

let rec parseAbs r f = match r with
					| x::"."::xs -> let (a, b) = f xs 1 temp in (Abs (x, a), b)
					| _ -> failwith "";;

let rec parseTerm str f = match str with
						| "("::xs -> let (l, left) = f xs 1 temp in (l, tail left)
						| x::xs -> (Var x, xs)
						| x -> (Var (head x), [""]);;

let rec parseExpr str fst acc = let f a b= let ne = if fst = 1 then a else App (acc, a) in parseExpr b 0 ne in match str with
						| [] -> (acc, [])
						| ")"::xs -> (acc, str)
						| "\\"::xs -> let (a, b) = parseAbs xs parseExpr in f a b
						| _ -> let (a, b) = parseTerm str parseExpr in f a b;;


let parse str = parseExpr (di str) 1 temp;;

let lambda_of_string s = let (ans, _) = parse s in ans;;

let rec string_of_lambda l = match l with
						| (Var (s)) -> (" "^s^" ")
						| App (a, b) -> ("("^(string_of_lambda a)^" "^(string_of_lambda b)^")")
						| Abs (var, lam) -> ("(\\"^var^"."^(string_of_lambda lam)^")");;


let print_the_same s = string_of_lambda (lambda_of_string s);;
