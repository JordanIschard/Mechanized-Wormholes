open Term
open Typ
open Identifier

module Typing = struct

  let fontstyle = "\x1b[1m\x1b[38;2;255;140;0m"
  let endstyle = "\x1b[0m"

  type vcontext = (string * Typ.t) list
  type rcontext = (Id.t * (Typ.t * Typ.t)) list

  let vlookup (s : string) (vc : vcontext) : Typ.t option =
    Option.map (snd) (List.find_opt (fun x -> (fst x) = s) vc)

  let vadd (s : string) (t : Typ.t) (vc : vcontext) : vcontext =
    let rec aux vc' =
      match vc' with
        | [] -> [(s,t)]
        | (s',t') :: vc1 -> if (s = s') then (s',t) :: vc1 else (s',t') :: (aux vc1)
    in aux vc

  let rlookup (s : Id.t) (rc : rcontext) : (Typ.t * Typ.t) option =
    Option.map (snd) (List.find_opt (fun x -> (fst x) = s) rc)

  let radd (s : Id.t) (t : Typ.t * Typ.t) (rc : rcontext) : rcontext =
    let rec aux rc' =
      match rc' with
        | [] -> [(s,t)]
        | (s',t') :: rc1 -> if (s = s') then (s',t) :: rc1 else (s',t') :: (aux rc1)
    in aux rc

  let rmax (rc : rcontext) = List.fold_right (fun x acc -> if (fst x) > acc then (fst x) else acc) rc 0
  let rnew (rc : rcontext) =
    match rc with
      | [] -> 0
      | _ -> (rmax rc) + 1

  let fmt_vcontext f l =
    let rec aux f l =
      match l with
        | [] -> Format.fprintf f ""
        | [h] -> Format.fprintf f "%s \u{2190} %a" (fst h) Typ.fmt (snd h)
        | h :: t -> Format.fprintf f "%s \u{2190} %a; %a" (fst h) Typ.fmt (snd h) aux t
    in Format.fprintf f "[%a]" aux l

  let fmt_rcontext f (l : rcontext) =
    let rec aux f (l : rcontext) =
      match l with
        | [] -> Format.fprintf f ""
        | [h] -> Format.fprintf f "%a \u{2190} %a x %a" Id.fmt (fst h) Typ.fmt (fst (snd h)) Typ.fmt (snd (snd h))
        | h :: t -> Format.fprintf f "%a \u{2190} %a x %a; %a" Id.fmt (fst h) Typ.fmt (fst (snd h)) Typ.fmt (snd (snd h)) aux t
    in Format.fprintf f "[%a]" aux l

  let rec typing (vc : vcontext) (rc : rcontext) (t : Term.t) : Typ.t option =
    match t with
      | Unit    -> Some Typ.Unit
      | Var x   -> vlookup x vc 
      | Abs (x,ty,t1) -> typing (vadd x ty vc) rc t1 
      | App (t1,t2) ->  begin 
                          match (typing vc rc t1,typing vc rc t2) with
                            | (Some Typ.Fun (ty1,ty2),Some ty3) -> if (ty1 = ty3) then Some ty2 else None
                            | _ -> None
                        end
      | Pair (t1,t2) -> begin 
                          match (typing vc rc t1,typing vc rc t2) with
                            | (Some ty1,Some ty2) -> Some (Prod (ty1,ty2))
                            | _ -> None
                        end
      | Fst t1 -> begin
                    match typing vc rc t1 with
                      | Some (Prod (ty,_)) -> Some ty
                      | _ -> None
                  end 
      | Snd t1 -> begin
                    match typing vc rc t1 with
                      | Some (Prod (_,ty)) -> Some ty
                      | _ -> None
                  end
      | Arr t1 -> begin
                    match typing vc rc t1 with
                      | Some (Fun (ty1,ty2)) -> Some (React (ty1,ty2,[]))
                      | _ -> None
                  end
      | First (ty,t1) ->  begin
                            match typing vc rc t1 with
                              | Some (React (ty1,ty2,rl)) -> 
                                  Some (React (Prod (ty1,ty),Prod (ty2,ty),rl))
                              | _ -> None
                          end
      | Comp (t1,t2) -> begin
                          match (typing vc rc t1,typing vc rc t2) with
                            | Some (React (ty1,ty1',rl1)), Some (React (ty2,ty2',rl2)) ->
                                  if (ty1' = ty2) then Some (React (ty1,ty2',List.merge (-) rl1 rl2))
                                                  else None
                            | _ -> None
                        end
      | Rsf r ->  begin 
                    match rlookup r rc with
                      | Some (ty1,ty2) -> Some (React (ty1,ty2,[r]))
                      | _ -> None
                  end
      | Wh (i,t1) ->  begin
                        match typing vc rc i with
                          | Some ty ->  begin
                                          match typing vc (radd ((rnew rc) + 1) (ty,Typ.Unit) 
                                                              (radd (rnew rc) (Typ.Unit,ty) rc)) t1 with
                                            | Some (React (ty1,ty2,rl)) -> 
                                                Some (React (ty1,ty2,List.filter (fun r -> r <> (rnew rc) && r <> ((rnew rc) + 1)) rl))
                                            | _ -> None
                                        end 
                          | _ -> None
                      end
  
  let fmt f (vl : vcontext) (rc : rcontext) (t : Term.t) (ty : Typ.t) =
    Format.fprintf f "%a . %a \u{22A2} %a :: %a" fmt_vcontext vl fmt_rcontext rc Term.fmt t Typ.fmt ty

end