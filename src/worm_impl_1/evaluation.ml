open Utils 
open Identifier 
open Typ
open Wh

module Eval =
struct
  
  let fmt_simpl : type kind.  int ->  Wh.t ->  Format.formatter ->Wh.t -> unit = fun lb t f t' ->
    Format.fprintf f "\x1b[1m\x1b[38;2;0;128;0m%d |=\x1b[0m %a \x1b[1m\x1b[38;2;153;50;204m\n\t\t\t\u{27F6}  \x1b[0m %a" lb Wh.fmt t Wh.fmt t'
  
  
  let fmt : type kind.  int ->  Wh.t ->  Format.formatter ->Wh.t -> unit = fun lb t f t' ->
    Format.fprintf f "\x1b[1m\x1b[38;2;0;128;0m%d |=\x1b[0m %a \x1b[1m\x1b[38;2;153;50;204m\n\t\t\t\u{27F6}  *\x1b[0m %a" lb Wh.fmt t Wh.fmt t'

  let rec subst (lb : int) (k : int) (x : var) (v : Wh.t) (t : Wh.t) : Wh.t =
    match t with
      | Var y     -> if x == y then Wh.shift lb k v else t
      | BWh (i,t) -> BWh (subst lb k x v i,subst lb (k + 2) x v t)

      | e -> Wh.shallow_map (subst lb k x v) (fun i -> i) e

  let rec evaluate (lb : int)  (t : Wh.t) : Wh.t option =
    let (>>=) = Option.map in
    match t with
      | App (BAbs(var,tau,e),v) -> if Wh.value v then Some (subst lb 0 var v e) 
                                                 else (fun t' -> Wh.App (BAbs(var,tau,e),t')) >>= (evaluate lb v)

      | App (t1,t2) -> (fun t' -> (Wh.App (t',t2))) >>= (evaluate lb t1)

      | Pair (t1,t2) -> if Wh.value t1  then (fun t' -> Wh.Pair (t1,t')) >>= (evaluate lb t2) 
                                        else (fun t' -> Wh.Pair (t',t2)) >>= (evaluate lb t1) 
      | Fst t' -> if Wh.value t'  then begin match t' with
                                                | Pair (v1,_) -> Some v1
                                                | _ -> Format.printf "\x1b[1m\x1b[38;2;210;0;0mfst operator applied on a non-pair value !!\n\x1b[0m"; None
                                        end
                                  else (fun t' -> Wh.Fst t') >>= (evaluate lb t')
      | Snd t' -> if Wh.value t'  then begin match t' with
                                              | Pair (_,v2) -> Some v2
                                              | _ -> Format.printf "\x1b[1m\x1b[38;2;210;0;0msnd operator applied on a non-pair value !!\n\x1b[0m"; None
                                       end
                                  else (fun t' -> Wh.Snd t') >>= (evaluate lb t')
      | First sf -> (fun sf' -> Wh.First sf') >>= (evaluate lb sf)
      | Comp (sf1,sf2) -> if Wh.value sf1 then (fun t' -> Wh.Comp (sf1,t')) >>= (evaluate lb sf2)
                                          else (fun t' -> Wh.Comp (t',sf2)) >>= (evaluate lb sf1)
      | BWh (i,sf) -> if Wh.value i then (fun sf' -> Wh.BWh (i,sf')) >>= (evaluate (lb+2) sf)
                                    else (fun i'  -> Wh.BWh (i,sf)) >>= (evaluate lb i)
      | _ -> Format.printf "\x1b[1m\x1b[38;2;210;0;0mNo transition found for the term ''%a'' !!\n\x1b[0m" Wh.fmt t; None

  let normalize lb t : Wh.t option =
    Format.printf "\x1b[1m\x1b[38;2;0;128;0m %d |=\x1b[0m %a\n" lb Wh.fmt t;
    let rec aux t = 
      if Wh.value t then begin Format.printf "\x1b[1m\x1b[38;2;153;50;204m END\x1b[0m\n\n"; Some t end
                    else match evaluate lb t with 
                          | Some t' ->  Format.printf "\x1b[1m\x1b[38;2;153;50;204m\t\t\t\u{27F6}  \x1b[0m %a\n" Wh.fmt t';
                                        aux t' 
                          | _ -> None
    in aux t


end