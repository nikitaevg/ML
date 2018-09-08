open Hw1
module M = Map.Make (String)
module S = Set.Make (String)

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

let rec free_vars_impl a locked = match a with
                                        | Var (n) -> if S.mem n locked then S.empty else S.singleton n
					| App (o, t) -> S.union (free_vars_impl o locked) (free_vars_impl t locked)
					| Abs (x, v) -> free_vars_impl v (S.add x locked)

let free_vars_set a = free_vars_impl a S.empty

let free_vars a = S.fold (fun x l -> x :: l) (free_vars_set a) []

let rec free_to_subst_impl thS theta a locked = match theta with 
					| Var (n) -> if a = n && (not (S.mem n locked)) then S.cardinal (S.inter locked thS) = 0 else true
					| App (o, t) -> free_to_subst_impl thS o a locked && (free_to_subst_impl thS t a locked)
					| Abs (n, e) -> free_to_subst_impl thS e a (S.add n locked)

let free_to_subst x theta a = free_to_subst_impl (free_vars_set x) theta a S.empty

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
let next_name() = counter := !counter + 1; "x" ^ (string_of_int(!counter))

let rec rename_impl x m = match x with
                    | Var (n) -> if M.mem n m then Var (M.find n m) else x
                    | App (p, q) -> App (rename_impl p m, rename_impl q m)
                    | Abs (n, t) -> let new_name = next_name () in Abs (new_name, rename_impl t (M.add n new_name m))

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

let copy theta = to_ptr (rename (from_ptr theta))

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
let str = "(\\s.\\k.\\i.(((s ((s (k s)) ((s ((s (k s)) ((s (k k)) i))) (k ((s (k (s ((s (k s)) ((s (k (s (k (s ((s ((s ((s i) (k (k (k i))))) (k ((s (k k)) i)))) (k ((s ((s (k s)) ((s (k k)) i))) (k i))))))))) ((s ((s (k s)) ((s (k k)) ((s (k s)) ((s (k (s (k ((s ((s (k s)) ((s (k k)) ((s (k s)) ((s (k k)) i))))) (k ((s ((s (k s)) ((s (k k)) i))) (k i)))))))) ((s ((s (k s)) ((s (k k)) i))) (k i))))))) (k ((s (k k)) i)))))))) ((s (k k)) ((s ((s (k s)) ((s (k k)) i))) (k i)))))))) (k (k ((s ((s (k s)) ((s (k k)) i))) ((s ((s (k s)) ((s (k k)) i))) ((s ((s (k s)) ((s (k k)) i))) (k i))))))) ((s ((s ((s (k s)) ((s (k k)) i))) (k ((s i) i)))) ((s ((s (k s)) ((s (k k)) i))) (k ((s i) i))))) ((s ((s (k s)) ((s (k (s (k s)))) ((s ((s (k s)) ((s (k (s (k s)))) ((s (k (s (k k)))) ((s ((s (k s)) ((s (k k)) i))) (k ((s (k (s (k (s i))))) ((s (k (s (k k)))) ((s (k (s i))) ((s (k k)) i)))))))))) (k (k ((s (k k)) i))))))) (k (k (k i))))) (\\x.\\y.\\z.x z (y z)) (\\x.\\y.x) (\\x.x)";;
let llam = lambda_of_string str;;
let pllam = to_ptr llam;;
