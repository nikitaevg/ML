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
