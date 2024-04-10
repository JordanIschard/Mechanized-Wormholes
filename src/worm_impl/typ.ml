open Utils
open Identifier

module Typ = 
struct
  
  type t =
    | Unit     : t
    | Fun      : t * t -> t
    | Prod     : t * t -> t
    | React   : t * t * Id.t list -> t


  let map (f : t -> t) (g : Id.t -> Id.t) (e : t) : t =
  match e with
    | Unit -> Unit
    | Fun (a,b)      -> Fun (f a,f b)
    | Prod (a,b)     -> Prod (f a,f b)
    | React (a,b,rl) -> React (f a,f b,List.map g rl)

  let rec remove_dup vl nvl =
    match vl with
      | [] -> nvl
      | h::t -> if List.mem h nvl then remove_dup t nvl else remove_dup t (h :: nvl)

  let rec shift (lb : int) (k : int) (t : t) : t = map (shift lb k) (Id.shift lb k) t

  let rec valid (k : int) (t : t) : bool =
    match t with
      | Unit -> true
      | Fun (a,b)      -> (valid k a) && (valid k b)
      | Prod (a,b)     -> (valid k a) && (valid k b)
      | React (a,b,rl) -> (valid k a) && (valid k b) && (List.for_all (Id.valid k) rl)

  let rec fmt : Format.formatter -> t ->  unit = fun f t ->
    match t with
      | Unit -> Format.fprintf f "U"
      | Fun (a,b)       -> Format.fprintf f "%a --> %a" fmt a fmt b
      | Prod (a,b)      -> Format.fprintf f "%a * %a" fmt a fmt b
      | React (a,b,rl)  -> Format.fprintf f "(%a ==> %a | %a)" fmt a fmt b Id.fmt_list rl

end
