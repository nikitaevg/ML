module M = Map.Make (String)
module S = Set.Make (String)

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


let rec alpha_eqv a b m = match a with
								| Var (nA) -> (match b with 
												| Var (nB) -> if M.mem nA m then (M.find nA m) = nB
																else (nA = nB)
												| _ -> false)
								| App (aA, bA) -> (match b with
												| App (aB, bB) -> let qA = alpha_eqv aA aB m in
																  let qB = alpha_eqv bA bB m in
																  qA && qB
												| _ -> false)
								| Abs (nA, eA) -> (match b with
												| Abs (nB, eB) -> alpha_eqv eA eB (M.add nA nB m)
												| _ -> false)

let is_alpha_equivalent a b = alpha_eqv a b M.empty

let rec free_vars thS theta a locked = match theta with 
					| Var (n) -> if a = n && (not (S.mem n locked)) then S.cardinal (S.inter locked thS) = 0 else true
					| App (o, t) -> free_vars thS o a locked && (free_vars thS t a locked)
					| Abs (n, e) -> free_vars thS e a (S.add n locked)

let rec makeSet a = match a with
					| Var (n) -> S.singleton n
					| App (o, t) -> S.union (makeSet o) (makeSet t)
					| Abs (_, _) -> S.empty

let free_to_subst x theta a = free_vars (makeSet x) theta a S.empty

let rec is_normal_form a = match a with
                    | Var (_) -> true
                    | Abs (_, a') -> is_normal_form a'
                    | App (Abs (_), _) -> false
                    | App (a', b') -> is_normal_form a' && is_normal_form b'

(* x - what to substitute, theta where to and a instead of what *)
let rec subst x theta a = match theta with
                            | Var (x') -> if a = x' then x else theta
                            | Abs (var', theta') -> if a = var' then theta else Abs (var', (subst x theta' a))
                            | App (p, q) -> App ((subst x p a), (subst x q a))

let counter = ref 0
let next_name prev = counter := !counter + 1; "Prev" ^ prev ^ (string_of_int(!counter))

let rec rename_impl x m = match x with
                    | Var (n) -> if M.mem n m then Var (M.find n m) else x
                    | App (p, q) -> App (rename_impl p m, rename_impl q m)
                    | Abs (n, t) -> let new_name = next_name n in Abs (new_name, rename_impl t (M.add n new_name m))

let rename x = rename_impl x M.empty

let rec normal_impl theta = if is_normal_form theta then theta else
                            match theta with
                                | Var (_) -> theta
                                | Abs (_, _) -> theta
                                | App (Abs (name, theta), x) -> subst x theta name
                                | App (o, t) -> if is_normal_form o then App (o, (normal_impl t))
                                                else App ((normal_impl o), t)

let rec normal_beta_reduction theta = if is_normal_form theta then theta else
                                    let renamed = rename theta in normal_impl renamed

type lambda_ptr = PVar of string | PAbs of string * lambda_ptr ref | PApp of lambda_ptr ref * lambda_ptr ref;;

let rec to_ptr x = match x with
            | Var (a) -> ref (PVar a)
            | Abs (a, b) -> ref (PAbs (a, to_ptr b))
            | App (a, b) -> ref (PApp (to_ptr a, to_ptr b))

let rec from_ptr x = match !x with
            | PVar (a) -> Var a
            | PAbs (a, b) -> Abs (a, from_ptr b)
            | PApp (a, b) -> App (from_ptr a, from_ptr b)

let string_of_plambda l = string_of_lambda (from_ptr l)

let rec subst_ptr x theta a = match !theta with
                            | PVar (x') -> if a = x' then theta := !x
                            | PAbs (var', theta') -> if a <> var' then subst_ptr x theta' a
                            | PApp (p, q) -> (subst_ptr x p a); (subst_ptr x q a)

let copy theta = to_ptr (from_ptr theta)

let rec reduce_impl theta = match !theta with
                    | PVar (_) -> false
                    | PAbs (_, theta') -> reduce_impl theta'
                    | PApp (l, x') -> match !l with 
                        | PAbs (a, theta') -> theta := !(copy theta'); subst_ptr x' theta a; true
                        | _ -> reduce_impl l || reduce_impl x'

let rec reduces_impl x = while reduce_impl x do
                            ()
                         done; x

let reduce_to_normal_form x = from_ptr (reduces_impl (to_ptr (rename x)))

let lam = lambda_of_string "(\\a. a a) (\\a. a f)";;
let plam = to_ptr lam;;
print_string (string_of_lambda lam);;
print_string "\n";;
print_string (string_of_lambda (reduce_to_normal_form lam));;
