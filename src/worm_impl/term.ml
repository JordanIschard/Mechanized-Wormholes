open Utils 
open Identifier 
open Typ

module Term = 
struct  


  type t = 
    | Unit   : t
    | Var    : var -> t
    | Abs    : var * Typ.t * t -> t
    | App    : t * t -> t

    | Pair   : t * t -> t
    | Fst    : t -> t
    | Snd    : t -> t
    
    | Arr    : t -> t
    | First  : Typ.t * t -> t
    | Comp   : t * t -> t
    
    | Rsf    : Id.t -> t
    | Wh    : t * t -> t


  let map (f : t -> t) (g : Typ.t -> Typ.t) (h : Id.t -> Id.t) (e : t) : t =
    match e with
      | Unit -> Unit
      | Var x -> Var x
      | App (e1,e2) -> App (f e1,f e2)
      | Abs (var,tau,e1) -> Abs (var,g tau,f e1)

      | Pair (e1,e2) -> Pair (f e1,f e2)
      | Fst e -> Fst (f e)
      | Snd e -> Snd (f e)

      | Arr sf -> Arr (f sf)
      | First (ty,sf) -> First (g ty,f sf)
      | Comp (sf1,sf2) -> Comp (f sf1,f sf2)

      | Rsf r -> Rsf (h r)
      | Wh (i,sf) -> Wh (f i,f sf)
  

  let rec valid (lb : int) (t : t) : bool =
    match t with
      | Rsf r -> Id.valid lb r
      | Wh(i,t) -> (valid lb i) && (valid (lb + 2) t)

      | Abs(_,tau,t) -> (Typ.valid lb tau) && (valid lb t) 
      | App(t,t') -> (valid lb t) && (valid lb t')

      | Pair(t,t') -> (valid lb t) && (valid lb t')
      | Fst t -> (valid lb t) 
      | Snd t -> (valid lb t) 

      | Comp(t,t') -> (valid lb t) && (valid lb t')
      | Arr t -> (valid lb t) 
      | First (ty,t) -> (Typ.valid lb ty) && (valid lb t) 

      | _ -> true

  let rec shift (lb : int) (k : int) (t : t) : t =
    map (shift lb k) (Typ.shift lb k) (Id.shift lb k) t

  let rec value : t -> bool = function
    | Unit -> true
    | Abs (_,_,_) -> true
    | Pair (e1,e2) -> value e1 && value e2
    | Arr sf -> value sf
    | First (_,sf) -> value sf
    | Comp (sf1,sf2) -> value sf1 && value sf2
    | Rsf r ->  true
    | Wh (i,sf) -> value i && value sf
    | _ -> false

  let rec fmt : Format.formatter -> t ->  unit = fun f t ->
    match t with
      | Unit -> Format.fprintf f "\x1b[1munit\x1b[0m"
      | Var x -> Format.fprintf f "%s" x
      | App (e1,e2) -> Format.fprintf f "(%a    %a)" fmt e1 fmt e2
      | Abs (var,tau,e1) -> Format.fprintf f "\x1b[1m\u{03BB}\x1b[0m%s:\x1b[2m%a\x1b[0m.(%a)" var Typ.fmt tau fmt e1

      | Pair (e1,e2) -> Format.fprintf f "(%a,%a)" fmt e1 fmt e2
      | Fst e -> Format.fprintf f "%a\x1b[1m.fst\x1b[0m" fmt e
      | Snd e -> Format.fprintf f "%a\x1b[1m.snd\x1b[0m" fmt e

      | Arr sf -> Format.fprintf f "\x1b[1marr\x1b[0m(%a)" fmt sf
      | First (ty,sf) -> Format.fprintf f "\x1b[1mfirst\x1b[0m(%a:%a)" Typ.fmt ty fmt sf
      | Comp (sf1,sf2) -> Format.fprintf f "%a \x1b[1m>>>\x1b[0m %a" fmt sf1 fmt sf2

      | Rsf r -> Format.fprintf f "\x1b[1m\x1b[38;2;173;216;230mrsf\x1b[0m[%a]" Id.fmt r
      | Wh (i,sf) -> Format.fprintf f "\x1b[1m\x1b[38;2;200;173;127mwormhole\x1b[0m(%a;%a)" fmt i fmt sf


end
