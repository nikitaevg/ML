type algebraic_term = Var of string | Fun of string * (algebraic_term list)

let rec find_biggest func = match func with
    | Fun (name, args) -> List.fold_left (fun max arg -> let found = find_biggest arg in
                        if String.length max > String.length found then max else found)
                    name args
    | _ -> ""

let rec create_new_name system = match system with
    | [] -> ""
    | x :: xs -> match x with 
        | Fun (name, args) -> let rest = create_new_name xs in
                              let curr = find_biggest x in
                if String.length rest > String.length curr then rest else curr
        | _ -> create_new_name xs

let create_new_name_sys system = let (left, right) = List.split system in
                                 let maxl = create_new_name left in
                                 let maxr = create_new_name right in
                                 let max = if String.length maxl > String.length maxr
                                           then maxl
                                           else maxr
                                 in max ^ "new"

let system_to_equation system = let (left, right) = List.split system in
                                let new_name = create_new_name_sys system in
                                (Fun (new_name, left), Fun(new_name, right))

let rec apply_substitution subst term = match term with
    | Var (name) -> let p x = fst x = name in
                        if List.exists p subst
                        then snd (List.find p subst)
                        else term
    | Fun (name, args) -> Fun (name, List.map (apply_substitution subst) args)

let check_solution s p = List.fold_left (fun acc (l, r) -> acc && let f = apply_substitution s in f l = f r) true p

exception NoSolution

let double_map func a b = ((List.map (fun (l, r) -> (func l, func r)) a), (List.map (fun (l, r) -> (func l, func r)) b)) 

let rec contains t x = match t with
    | Var (name) -> x = name
    | Fun (_, args) -> List.fold_left (fun acc arg -> acc || contains arg x) false args

let rec solve_system_impl x ans = match x with
    | [] -> ans
    | (lhs, rhs) :: xs -> if lhs = rhs then solve_system_impl xs ans else match lhs with
        | Var (name) -> if contains rhs name then raise NoSolution
                        else let (xs_mod, ans_mod) = double_map (apply_substitution [(name, rhs)]) xs ans in
                            solve_system_impl xs_mod ((lhs, rhs) :: ans_mod)
        | Fun (namea, argsa) -> match rhs with
            | Var (_) -> solve_system_impl ((rhs, lhs) :: xs) ans
            | Fun (nameb, argsb) -> if namea <> nameb || List.length argsa <> List.length argsb
                                    then raise NoSolution
                                    else solve_system_impl (List.combine argsa argsb @ xs) ans
             
let filter_and_transform x = List.map (fun (lhs, rhs) -> match lhs with
                            | Var (name) -> if contains rhs name then raise NoSolution else (name, rhs)
                            | _ -> raise NoSolution) x

let solve_system x = (try Some (filter_and_transform (solve_system_impl x []))
                     with _ -> None)
