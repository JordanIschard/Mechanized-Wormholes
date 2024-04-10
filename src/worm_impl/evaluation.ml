open Utils 
open Identifier 
open Typ
open Term

module Eval =
struct
  
  let fmt_simpl : type kind.  int ->  Term.t ->  Format.formatter -> Term.t -> unit = fun lb t f t' ->
    Format.fprintf f "\x1b[1m\x1b[38;2;0;128;0m%d |=\x1b[0m %a \x1b[1m\x1b[38;2;153;50;204m\n\t\t\t\u{27F6}  \x1b[0m %a" lb Term.fmt t Term.fmt t'
  
  
  let fmt : type kind.  int ->  Term.t ->  Format.formatter ->Term.t -> unit = fun lb t f t' ->
    Format.fprintf f "\x1b[1m\x1b[38;2;0;128;0m%d |=\x1b[0m %a \x1b[1m\x1b[38;2;153;50;204m\n\t\t\t\u{27F6}  *\x1b[0m %a" lb Term.fmt t Term.fmt t'


  let rec subst (lb : int) (k : int) (x : var) (v : Term.t) (t : Term.t) : Term.t =
    match t with
      | Var y     -> (* Format.printf "\t\x1b[1m\x1b[38;2;210;0;0m[%s := %a\x1b[1m\x1b[38;2;210;0;0m ~ %d <= %d] %a\n\x1b[0m" x Term.fmt v lb k Term.fmt t ; *) if x == y then Term.shift lb k v else t
      | Wh (i,e) ->  (* Format.printf "\t\x1b[1m\x1b[38;2;210;0;0m[%s := %a\x1b[1m\x1b[38;2;210;0;0m ~ %d <= %d] %a\n\x1b[0m" x Term.fmt v lb k Term.fmt t ; *) Wh (subst lb k x v i,subst lb (k + 2) x v e)

      | e -> (* Format.printf "\t\x1b[1m\x1b[38;2;210;0;0m[%s := %a\x1b[1m\x1b[38;2;210;0;0m ~ %d <= %d] %a\n\x1b[0m" x Term.fmt v lb k Term.fmt t ; *) Term.map (subst lb k x v) (Fun.id) (Fun.id) e


  let rec evaluate (lb : int)  (t : Term.t) : Term.t option =
    let (>>=) = Option.map in
    match t with
      | App (Abs(var,tau,e),v) -> if Term.value v then Some (subst lb 0 var v e) 
                                                 else (fun t' -> Term.App (Abs(var,tau,e),t')) >>= (evaluate lb v)

      | App (t1,t2) -> (fun t' -> (Term.App (t',t2))) >>= (evaluate lb t1)

      | Pair (t1,t2) -> if Term.value t1  then (fun t' -> Term.Pair (t1,t')) >>= (evaluate lb t2) 
                                        else (fun t' -> Term.Pair (t',t2)) >>= (evaluate lb t1) 
      | Fst t' -> if Term.value t'  then begin match t' with
                                                | Pair (v1,_) -> Some v1
                                                | _ -> Format.printf "\x1b[1m\x1b[38;2;210;0;0mfst operator applied on a non-pair value !!\n\x1b[0m"; None
                                        end
                                  else (fun t' -> Term.Fst t') >>= (evaluate lb t')
      | Snd t' -> if Term.value t'  then begin match t' with
                                              | Pair (_,v2) -> Some v2
                                              | _ -> Format.printf "\x1b[1m\x1b[38;2;210;0;0msnd operator applied on a non-pair value !!\n\x1b[0m"; None
                                       end
                                  else (fun t' -> Term.Snd t') >>= (evaluate lb t')
      | First (ty,sf) -> (fun sf' -> Term.First (ty,sf')) >>= (evaluate lb sf)
      | Comp (sf1,sf2) -> if Term.value sf1 then (fun t' -> Term.Comp (sf1,t')) >>= (evaluate lb sf2)
                                          else (fun t' -> Term.Comp (t',sf2)) >>= (evaluate lb sf1)
      | Wh (i,sf) -> if Term.value i then (fun sf' -> Term.Wh (i,sf')) >>= (evaluate (lb+2) sf)
                                    else (fun i'  -> Term.Wh (i,sf)) >>= (evaluate lb i)
      | _ -> Format.printf "\x1b[1m\x1b[38;2;210;0;0mNo transition found for the term ''%a'' !!\n\x1b[0m" Term.fmt t; None

  let normalize lb t : Term.t option =
    Format.printf "\x1b[1m\x1b[38;2;0;128;0m %d |=\x1b[0m %a\n" lb Term.fmt t;
    let rec aux t = 
      if Term.value t then begin Format.printf "\x1b[1m\x1b[38;2;153;50;204m END\x1b[0m\n\n"; Some t end
                    else match evaluate lb t with 
                          | Some t' ->  Format.printf "\x1b[1m\x1b[38;2;153;50;204m\t\t\t\u{27F6}  \x1b[0m %a\n" Term.fmt t';
                                        aux t' 
                          | _ -> None
    in aux t


end