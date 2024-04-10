open Utils
open Identifier

module Typ = 
struct
  
  type ('deep_kind,'surface_kind) fl_type =
    | Unit     : (<lambda: yes; ..>,<lambda: yes; ..>) fl_type
    | Fun      : 'deep_kind typ * 'deep_kind typ -> ('deep_kind,<lambda: yes; ..>) fl_type
    | Prod     : 'deep_kind typ * 'deep_kind typ -> ('deep_kind,<lambda: yes; ..>) fl_type
    | React    : 'deep_kind typ * 'deep_kind typ * ('deep_kind Id.identifier) list -> ('deep_kind,<arrow: yes; bruijn: no;..>) fl_type
    | BReact   : 'deep_kind typ * 'deep_kind typ * ('deep_kind Id.identifier) list -> ('deep_kind,<arrow: yes; bruijn: yes;..>) fl_type
  and 'kind typ = ('kind,'kind) fl_type

  type raw = <lambda:yes;arrow:yes;bruijn:no> typ 
  type t = <lambda:yes;arrow:yes;bruijn:yes> typ 
  

  let shallow_map (type src_kind dst_kind reftype) 
  (f : src_kind typ -> dst_kind typ)
  (g : src_kind Id.identifier -> dst_kind Id.identifier)
  (e : (src_kind,dst_kind) fl_type) : dst_kind typ =
  match e with
    | Unit -> Unit
    | Fun (a,b)      -> Fun (f a,f b)
    | Prod (a,b)     -> Prod (f a,f b)
    | React (a,b,rl) -> React (f a,f b,List.map g rl)
    | BReact (a,b,rl) -> BReact (f a,f b,List.map g rl)

  let rec remove_dup vl nvl =
    match vl with
      | [] -> nvl
      | h::t -> if List.mem h nvl then remove_dup t nvl else remove_dup t (h :: nvl)

  let rec get_Rtau : <bruijn:no;..> typ -> var list = function
    | Unit -> []
    | Fun (a,b)      -> Utils.append_NoDup (get_Rtau a) (get_Rtau b)
    | Prod (a,b)     -> Utils.append_NoDup (get_Rtau a) (get_Rtau b)
    | React (a,b,rl) -> Utils.append_NoDup (remove_dup (List.map Id.pi_var rl) []) (get_Rtau b)


  let rec transition (_FRf : var list) (t : <bruijn:no;..> typ) : (<bruijn:yes;..> typ) option =
    match t with
      | Unit -> Some Unit
      | React (a,b,rl) -> let io (r : var) : int option = find_index_FRf _FRf r in
                          let cToi (c : <bruijn:no;..> Id.identifier) : (<bruijn:yes;..> Id.identifier) option =  
                            Option.map (fun i -> Id.transition i c) (io (Id.pi_var c))
                          in
                          begin match (transition _FRf a,transition _FRf b,list_option (List.map (fun c ->  cToi c) rl)) with
                            | (Some a',Some b',Some rl') -> Some (BReact(a', b',rl'))
                            | _ -> None
                          end
      | Fun (a,b)      -> begin match (transition _FRf a,transition _FRf b) with
                            | (Some a',Some b') -> Some (Fun(a', b'))
                            | _ -> None
                          end
      | Prod (a,b)      -> begin match (transition _FRf a,transition _FRf b) with
                            | (Some a',Some b') -> Some (Prod(a', b'))
                            | _ -> None
                          end

  let rec shift (lb : int) (k : int) (t : t) : t = shallow_map  (shift lb k) (Id.shift lb k) t

  let rec valid (k : int) (t : t) : bool =
    match t with
      | Unit -> true
      | Fun (a,b)       -> (valid k a) && (valid k b)
      | Prod (a,b)      -> (valid k a) && (valid k b)
      | BReact (a,b,rl) -> (valid k a) && (valid k b) && (List.for_all (Id.valid k) rl)

  let rec fmt : type kind. Format.formatter -> kind typ ->  unit = fun f t ->
    match t with
      | Unit -> Format.fprintf f "U"
      | Fun (a,b)       -> Format.fprintf f "%a --> %a" fmt a fmt b
      | Prod (a,b)      -> Format.fprintf f "%a * %a" fmt a fmt b
      | React (a,b,rl)  -> Format.fprintf f "(%a ==> %a | %a)" fmt a fmt b Id.fmt_list rl
      | BReact (a,b,rl)  -> Format.fprintf f "(%a ==> %a | %a)" fmt a fmt b Id.fmt_list rl

end
