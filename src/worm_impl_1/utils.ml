type var = string
type yes = Yes
type no = No

let find_index_FRf _FRf r =
  let rec aux i _FRf =
    match _FRf with
      | []   -> None
      | h::t -> if h = r then Some i else aux (i+1) t
  in Option.map (fun x -> x) (aux 0 (List.rev _FRf))

let rec update r v l =
  match (r,l) with
    | (0,h :: t) -> v :: t
    | (i,h :: t) -> h :: (update (i-1) v t)
    | _ -> l

let append_NoDup l l' =
  let rec aux l res =
    match l with
      | [] -> List.append l' res
      | h :: t -> if List.mem h l' then aux t res else aux t (h::res)
  in aux l []

let print_list f lst =
  let rec print_elements = function
    | [] -> ()
    | [h] -> f h
    | h::t -> f h; print_string ";"; print_elements t
  in
  print_string "[";
  print_elements lst;
  print_string "]";;

let fmt_var_list f l =
    let rec aux_fmt_list f l =
      match l with
        | [] -> Format.fprintf f ""
        | [h] -> Format.fprintf f "%s" h
        | h :: t -> Format.fprintf f "%s; %a" h aux_fmt_list t
    in Format.fprintf f "[%a]" aux_fmt_list l

let rec list_option lst =
  match lst with
   | [] -> Some []
   | Some h::t -> begin match list_option t with
                    | Some t' -> Some (h::t')
                    | None -> None
                  end
   | None::_ -> None
