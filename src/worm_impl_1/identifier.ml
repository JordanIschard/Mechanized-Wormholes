open Utils

module Id =
struct

  type 'kind identifier =
    | Tag    : var -> <bruijn: no;..> identifier
    | BTag   : int -> <bruijn: yes;..> identifier

  type variable = <lmabda:yes;arrow:yes;bruijn: no> identifier
  type level = <lmabda:yes;arrow:yes;bruijn: yes> identifier

  let apply_name f (x : <bruijn: no;..> identifier) :  <bruijn: no; ..> identifier =
    match x with
      | Tag x' -> Tag (f x')

  let apply_lvl f (x : <bruijn: yes;..> identifier) :  <bruijn: yes; ..> identifier =
  match x with
    | BTag x' -> BTag (f x')

  let pi_var (Tag x) = x

  let pi_lvl (BTag x) = x

  let transition (v : int) (x : <bruijn: no;..> identifier) :  <bruijn: yes;..> identifier =
  match x with
    | Tag x' -> BTag v

  let rec fmt : type kind. Format.formatter -> kind identifier ->  unit = fun f t ->
    match t with
      | Tag x -> Format.fprintf f "\x1b[4m%s\x1b[0m" x
      | BTag x -> Format.fprintf f "\x1b[4m%d\x1b[0m" x

  let rec valid (k : int) (BTag t : <bruijn: yes;..> identifier) : bool = t < k
      
  let rec shift (lb : int) (k : int) (t : <bruijn: yes;..> identifier) : <bruijn: yes;..> identifier = 
    apply_lvl (fun (i : int) -> if i < lb then i else i + k) t

  let fmt_list f l =
    let rec aux_fmt_list f l =
      match l with
        | [] -> Format.fprintf f ""
        | [h] -> Format.fprintf f "%a" fmt h
        | h :: t -> Format.fprintf f "%a; %a" fmt h aux_fmt_list t
    in Format.fprintf f "[%a]" aux_fmt_list l 
end
