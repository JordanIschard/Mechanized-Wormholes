open Utils 
open Identifier 
open Typ

module Wh = 
struct  


  type ('deep_kind,'surface_kind) fl_expr = 
    | Unit   : (<lambda: yes; ..>,<lambda: yes; ..>) fl_expr
    | Var    : var -> (<lambda: yes; ..>,<lambda: yes; ..>) fl_expr
    | Abs    : var * 'deep_kind Typ.typ * 'deep_kind expr -> ('deep_kind,<lambda: yes;bruijn:no; ..>) fl_expr
    | BAbs   : var * 'deep_kind Typ.typ * 'deep_kind expr -> ('deep_kind,<lambda: yes;bruijn:yes; ..>) fl_expr
    | App    : 'deep_kind expr * 'deep_kind expr -> ('deep_kind,<lambda: yes; ..>) fl_expr

    | Pair   : 'deep_kind expr * 'deep_kind expr -> ('deep_kind,<lambda: yes; ..>) fl_expr
    | Fst    : 'deep_kind expr -> ('deep_kind,<lambda: yes; ..>) fl_expr
    | Snd    : 'deep_kind expr -> ('deep_kind,<lambda: yes; ..>) fl_expr
    
    | Arr    : 'deep_kind expr -> ('deep_kind,<arrow: yes;..>) fl_expr
    | First  : 'deep_kind expr -> ('deep_kind,<arrow: yes;..>) fl_expr
    | Comp   : 'deep_kind expr * 'deep_kind expr -> ('deep_kind,<arrow: yes; ..>) fl_expr
    
    | Rsf    : <bruijn:no;..> Id.identifier -> (<arrow: yes; bruijn: no;..>,<arrow: yes; bruijn: no;..>) fl_expr
    | BRsf   : <bruijn:yes;..> Id.identifier -> (<arrow: yes; bruijn: yes;..>,<arrow: yes; bruijn: yes;..>) fl_expr
    | Wh     : var * var * 'deep_kind expr * 'deep_kind expr -> ('deep_kind,<arrow: yes; bruijn: no;..>) fl_expr
    | BWh    : 'deep_kind expr * 'deep_kind expr -> ('deep_kind,<arrow: yes; bruijn: yes;..>) fl_expr
  and 'kind expr = ('kind,'kind) fl_expr

  
  type raw = <lambda:yes;arrow:yes;bruijn:no> expr 
  type t = <lambda:yes;arrow:yes;bruijn:yes> expr 


  let shallow_map (type src_kind dst_kind) 
  (f : src_kind expr -> dst_kind expr) 
  (g : src_kind Typ.typ -> dst_kind Typ.typ)
  (e : (src_kind,dst_kind) fl_expr) : dst_kind expr =
    match e with
      | Unit -> Unit
      | Var x -> Var x
      | App (e1,e2) -> App (f e1,f e2)
      | Abs (var,tau,e1) -> Abs (var,g tau,f e1)
      | BAbs (var,tau,e1) -> BAbs (var,g tau,f e1)

      | Pair (e1,e2) -> Pair (f e1,f e2)
      | Fst e -> Fst (f e)
      | Snd e -> Snd (f e)

      | Arr sf -> Arr (f sf)
      | First sf -> First (f sf)
      | Comp (sf1,sf2) -> Comp (f sf1,f sf2)

      | Rsf r -> Rsf r
      | BRsf r -> BRsf r
      | Wh (r,r',i,sf) -> Wh (r,r',f i,f sf)
      | BWh (i,sf) -> BWh (f i,f sf)
  
  let rec get_FRf : raw -> var list = function
    | Rsf r -> [Id.pi_var r]
    | Wh (r,r',i,sf) -> Utils.append_NoDup  (get_FRf i) (List.filter (fun x ->  x <> r && x <> r') (get_FRf sf))

    | Var _ -> []
    | Unit -> []
    | Pair (e1,e2) -> Utils.append_NoDup (get_FRf e1) (get_FRf e2)
    | App (e1,e2) -> Utils.append_NoDup (get_FRf e1) (get_FRf e2)
    | Abs (_,tau,e1) -> Utils.append_NoDup (Typ.get_Rtau tau) (get_FRf e1)

    | Fst e -> get_FRf e
    | Snd e -> get_FRf e
    | Arr sf -> get_FRf sf
    | First sf -> get_FRf sf
    | Comp (sf1,sf2) -> Utils.append_NoDup (get_FRf sf1) (get_FRf sf2)

  let rec transition (_FRf : var list) (t : raw) : t option =
    match t with
      | Rsf r -> Option.map (fun i -> BRsf (Id.transition i r)) (find_index_FRf _FRf (Id.pi_var r))
      | Wh (r,r',i,t) -> begin match (transition _FRf i,transition (r'::r::_FRf) t) with
                        | (Some i',Some t') -> Some (BWh(i',t'))
                        | _ -> None
                      end
      | Var x -> Some (Var x)
      | Unit -> Some Unit
      | Abs (x,tau,t) ->  begin match (Typ.transition _FRf tau,transition _FRf t) with
                            | (Some tau',Some t') -> Some (BAbs(x,tau',t'))
                            | _ -> None
                          end
      | App (t,t') ->   begin match (transition _FRf t,transition _FRf t') with
                          | (Some t1,Some t1') -> Some (App(t1,t1'))
                          | _ -> None
                        end
      | Pair (t,t') ->   begin match (transition _FRf t,transition _FRf t') with
                          | (Some t1,Some t1') -> Some (Pair(t1,t1'))
                          | _ -> None
                        end

      | Comp (t,t') ->   begin match (transition _FRf t,transition _FRf t') with
                          | (Some t1,Some t1') -> Some (Comp(t1,t1'))
                          | _ -> None
                        end
      | Fst t -> Option.map (fun t' -> Fst t') (transition _FRf t)
      | Snd t -> Option.map (fun t' -> Snd t') (transition _FRf t)
      | Arr t -> Option.map (fun t' -> Arr t') (transition _FRf t)
      | First t -> Option.map (fun t' -> First t') (transition _FRf t)

  let rec valid (k : int) (t : t) : bool =
    match t with
      | BRsf r -> Id.pi_lvl r < k
      | BWh(i,t) -> (valid k i) && (valid (k + 2) t)

      | BAbs(_,tau,t) -> (Typ.valid k tau) && (valid k t) 
      | App(t,t') -> (valid k t) && (valid k t')

      | Pair(t,t') -> (valid k t) && (valid k t')
      | Fst t -> (valid k t) 
      | Snd t -> (valid k t) 

      | Comp(t,t') -> (valid k t) && (valid k t')
      | Arr t -> (valid k t) 
      | First t -> (valid k t) 

      | _ -> true

  let rec shift (lb : int) (k : int) (t : t) : t =
    match t with
    | BRsf r -> if (Id.pi_lvl r < lb) then t else BRsf (Id.apply_lvl (fun i -> k + i) r)

    | e -> shallow_map (shift lb k) (Typ.shift lb k) e

  let rec value : type kind. kind expr -> bool = function
    | Unit -> true
    | Abs (_,_,_) -> true
    | BAbs (_,_,_) -> true
    | Pair (e1,e2) -> value e1 && value e2
    | Arr sf -> value sf
    | First sf -> value sf
    | Comp (sf1,sf2) -> value sf1 && value sf2
    | Rsf r ->  true
    | BRsf r ->  true
    | Wh (_,_,i,sf) -> value i && value sf
    | BWh (i,sf) -> value i && value sf
    | _ -> false

  let rec fmt : type kind. Format.formatter -> kind expr ->  unit = fun f t ->
    match t with
      | Unit -> Format.fprintf f "\x1b[1munit\x1b[0m"
      | Var x -> Format.fprintf f "%s" x
      | App (e1,e2) -> Format.fprintf f "(%a    %a)" fmt e1 fmt e2
      | Abs (var,tau,e1) -> Format.fprintf f "\x1b[1m\u{03BB}\x1b[0m%s:\x1b[2m%a\x1b[0m.(%a)" var Typ.fmt tau fmt e1
      | BAbs (var,tau,e1) -> Format.fprintf f "\x1b[1m\u{03BB}\x1b[0m%s:\x1b[2m%a\x1b[0m.(%a)" var Typ.fmt tau fmt e1

      | Pair (e1,e2) -> Format.fprintf f "(%a,%a)" fmt e1 fmt e2
      | Fst e -> Format.fprintf f "%a\x1b[1m.fst\x1b[0m" fmt e
      | Snd e -> Format.fprintf f "%a\x1b[1m.snd\x1b[0m" fmt e

      | Arr sf -> Format.fprintf f "\x1b[1marr\x1b[0m(%a)" fmt sf
      | First sf -> Format.fprintf f "\x1b[1mfirst\x1b[0m(%a)" fmt sf
      | Comp (sf1,sf2) -> Format.fprintf f "%a \x1b[1m>>>\x1b[0m %a" fmt sf1 fmt sf2

      | Rsf r -> Format.fprintf f "\x1b[1m\x1b[38;2;173;216;230mrsf\x1b[0m[%a]" Id.fmt r
      | BRsf r -> Format.fprintf f "\x1b[1m\x1b[38;2;200;173;127mrsf\x1b[0m[%a]" Id.fmt r
      | Wh (r,r',i,sf) -> Format.fprintf f "\x1b[1m\x1b[38;2;173;216;230mwormhole[%s,%s]\x1b[0m(%a;%a)" r r' fmt i fmt sf
      | BWh (i,sf) -> Format.fprintf f "\x1b[1m\x1b[38;2;200;173;127mwormhole\x1b[0m(%a;%a)" fmt i fmt sf


end
