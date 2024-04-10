open Utils

module Id =
struct

  type t = int

  let rec fmt : Format.formatter -> t ->  unit = fun f t -> Format.fprintf f "\x1b[4m%d\x1b[0m" t

  let rec valid (k : int) (t : t) : bool = t < k
      
  let rec shift (lb : int) (k : int) (t : t) : t = 
    if lb <= t then t + k else t

  let fmt_list f l =
    let rec aux_fmt_list f l =
      match l with
        | [] -> Format.fprintf f ""
        | [h] -> Format.fprintf f "%a" fmt h
        | h :: t -> Format.fprintf f "%a; %a" fmt h aux_fmt_list t
    in Format.fprintf f "[%a]" aux_fmt_list l 
    
end
