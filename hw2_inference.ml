open Parser
open Hw2_unify

module M = Map.Make (String)
module S = Set.Make (String)

type simp_type = S_Elem of string | S_Arrow of simp_type * simp_type

let counter = ref 0
let next_name prev = counter := !counter + 1; "" ^ prev ^ (string_of_int(!counter))

let rec infer_impl expr maps = match expr with
    | Parser.Var a -> ([], M.find a (fst maps), snd maps)
    | Parser.App (p, r) -> let (em1, tm1, maps1) = infer_impl p maps in
                    let (em2, tm2, maps2) = infer_impl r maps in
                    let pi = S_Elem (next_name "app") in
                    ((tm1, S_Arrow (tm2, pi)) :: em1 @ em2, pi, maps1 @ maps2)
    | Parser.Abs (x, p) -> let new_type = S_Elem (next_name x) in
                    let (map1, map2) = maps in
                    let (em, tm, map2v2) = infer_impl p (M.add x new_type map1, map2) in
                    (em, S_Arrow (new_type, tm), (new_type, x) :: map2v2)

let rec trans_simp_to_lam a = match a with
                        | S_Elem (n) -> Hw2_unify.Var n
                        | S_Arrow (a, b) -> Hw2_unify.Fun ("f", [trans_simp_to_lam a; trans_simp_to_lam b])

let simp_to_lam simp = List.map (fun (a, b) -> (trans_simp_to_lam a, trans_simp_to_lam b)) simp

let rec trans_lam_to_simp a = match a with
                        | Hw2_unify.Var (n) -> S_Elem n
                        | Hw2_unify.Fun (_, [a; b]) -> S_Arrow (trans_lam_to_simp a, trans_lam_to_simp b)
                        | _ -> failwith "unreachable"

let lam_to_simp lam = List.map (fun (a, b) -> (trans_lam_to_simp a, trans_lam_to_simp b)) lam
let lam_to_simp' lam = List.map (fun (a, b) -> (a, trans_lam_to_simp b)) lam

let cont e l = List.fold_left (fun ans (name, exp) -> try
    let (_, var) = List.find (fun (S_Elem (typ), _) -> name = typ) l in (var, exp) :: ans
with _ -> ans) [] e

let infer_simp_type lam = try let ans =( 
                          let (e, t, l) = infer_impl lam (M.empty, []) in
                          let e_lam = simp_to_lam e in
                          let t_lam = trans_simp_to_lam t in
                          match Hw2_unify.solve_system e_lam with
                            | Some (sol) -> let type_ans = trans_lam_to_simp (Hw2_unify.apply_substitution sol t_lam) in
                                            let s = cont sol l in
                                (lam_to_simp' s, type_ans)
                            | _ -> failwith "")
                          in Some ans
                          with _ -> None


type hm_lambda = HM_Var of string |
                 HM_Abs of string * hm_lambda |
                 HM_App of hm_lambda * hm_lambda |
                 HM_Let of string * hm_lambda * hm_lambda
type hm_type = HM_Elem of string |
               HM_Arrow of hm_type * hm_type |
               HM_ForAll of string * hm_type

let rec concretize_in type_ map = match type_ with
    | HM_Elem (name) -> (try M.find name map with _ -> type_)
    | HM_Arrow (a, b) -> HM_Arrow ((concretize_in a map), (concretize_in b map))
    | HM_ForAll (_, _) -> failwith "unreachable"

let rec concretize_impl type_ map = match type_ with
    | HM_ForAll (a, b) -> concretize_impl b (M.add a (HM_Elem (next_name "b")) map)
    | _ -> concretize_in type_ map

let concretize type_ = concretize_impl type_ M.empty

let rec subst_in_type_impl s not_free type_ = match type_ with
    | HM_Elem (name) -> if M.mem name s && not (S.mem name not_free)
                      then M.find name s
                      else type_
    | HM_Arrow (a, b) -> HM_Arrow ((subst_in_type_impl s not_free a), (subst_in_type_impl s not_free b))
    | HM_ForAll (name, expr) -> HM_ForAll (name, subst_in_type_impl s (S.add name not_free) expr)

let subst_in_type s type_ = subst_in_type_impl s S.empty type_

let subst_in_ctx s = M.map (fun type_ -> subst_in_type s type_)

let rec trans_hm_to_lam a = match a with
                        | HM_Elem (n) -> Hw2_unify.Var n
                        | HM_Arrow (a, b) -> Hw2_unify.Fun ("f", [trans_hm_to_lam a; trans_hm_to_lam b])
                        | HM_ForAll (a, b) -> Hw2_unify.Fun ("g", [Hw2_unify.Var a; trans_hm_to_lam b])

let rec trans_lam_to_hm a = match a with
                        | Hw2_unify.Var (n) -> HM_Elem n
                        | Hw2_unify.Fun (n, [a; b]) -> if n = "f"
                                    then HM_Arrow (trans_lam_to_hm a, trans_lam_to_hm b)
                                    else (match a with 
                                        | Hw2_unify.Var (name) ->
                                                HM_ForAll (name, trans_lam_to_hm b)
                                        | _ -> failwith "unreachable")
                        | _ -> failwith "unreachable"

let merge_map = M.merge (fun k x y -> match x with
                                    | Some _ -> x
                                    | None -> y)

let concat_subst a b = let new_b = M.map (fun v -> subst_in_type a v) b in
                       merge_map a new_b

exception CantType

let rec free_vars_type_impl type_ used = match type_ with
    | HM_Elem (n) -> if not (S.mem n used) then S.singleton n else S.empty
    | HM_Arrow (a, b) -> S.union (free_vars_type_impl a used) (free_vars_type_impl b used)
    | HM_ForAll (a, b) -> free_vars_type_impl b (S.add a used)

let free_vars_type type_ = free_vars_type_impl type_ S.empty

let free_vars_ctx ctx = M.fold (fun _ v set -> S.union set (free_vars_type v)) ctx S.empty

let generalization ctx type_ = let fv_type = free_vars_type type_ in
                               let fv_ctx = free_vars_ctx ctx in
                               let compl = S.filter (fun x -> not (S.mem x fv_ctx)) fv_type in
                               S.fold (fun n type1 -> HM_ForAll (n, type1)) compl type_ 

let rec algorithm_w_impl lam ctx = match lam with
    | HM_Var (n) -> (M.empty, concretize (M.find n ctx))
    | HM_App (e1,e2) -> let (s1, t1) = algorithm_w_impl e1 ctx in
                      let (s2, t2) = algorithm_w_impl e2 (subst_in_ctx s1 ctx) in
                      let b = HM_Elem (next_name "b") in
                          let eq_type = (trans_hm_to_lam (subst_in_type s2 t1), trans_hm_to_lam(HM_Arrow (t2, b))) in
                          let ss = Hw2_unify.solve_system [eq_type] in
                          (match ss with 
                          | None -> raise CantType
                          | Some (vv) ->
                          let v = List.map (fun (a, b) -> (a, trans_lam_to_hm b)) vv in
                      let v_map = List.fold_left (fun map (a, b) -> M.add a b map) M.empty v in 
                      let s = concat_subst v_map (concat_subst s2 s1) in
                                   (s, subst_in_type s b))

    | HM_Abs (name,expr) -> let b = HM_Elem (next_name "b") in
                            let (s1, t1) = algorithm_w_impl expr (M.add name b ctx) in
                            (s1, HM_Arrow (subst_in_type s1 b, t1))
    | HM_Let (x, e1, e2) -> let (s1, t1) = algorithm_w_impl e1 ctx in
                            let new_ctx = subst_in_ctx s1 ctx in
                            let (s2, t2) = algorithm_w_impl e2 (M.add x (generalization new_ctx t1) new_ctx) in
                            (concat_subst s2 s1, t2)


let rec get_context lam used = match lam with
    | HM_Var (n) -> if S.mem n used then M.empty else
                        M.singleton n (HM_Elem (next_name "a"))
    | HM_App (e1, e2) -> merge_map (get_context e1 used) (get_context e2 used)
    | HM_Abs (name, expr) -> get_context expr (S.add name used)
    | HM_Let (x, e1, e2) -> merge_map (get_context e1 used)
                                      (get_context e2 (S.add x used))

let algorithm_w lam = try (let (ctx, type_) = algorithm_w_impl lam (get_context lam S.empty) in
                        Some (M.fold (fun k v l -> (k, v) :: l) ctx [], type_))
                      with _ -> None
