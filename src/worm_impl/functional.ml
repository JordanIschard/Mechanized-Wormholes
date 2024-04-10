open Utils 
open Identifier 
open Typ
open Term
open Evaluation

module Functional = struct

  let fontstyle = "\x1b[1m\x1b[38;2;255;140;0m"
  let endstyle = "\x1b[0m"
  
  type cell = In of Term.t | Out of Term.t
  type element = { read : Id.t; write : Id.t; value : Term.t }

  type in_func = { env : cell list; stream : Term.t; expr : Term.t }
  type out_func = { env : cell list; stream : Term.t; expr : Term.t; stock : element list }


  let fmt_cell : Format.formatter -> cell -> unit = fun f c ->
    match c with
      | In v  -> Format.fprintf f "< %a , _ >" Term.fmt v
      | Out v -> Format.fprintf f "< _ , %a >" Term.fmt v

  let fmt_element : Format.formatter -> element -> unit = fun f el ->
    Format.fprintf f "(%a,%a : %a)" Id.fmt el.read Id.fmt el.write Term.fmt el.value

  let fmt_stock f l =
    let rec aux f l =
      match l with
        | [] -> Format.fprintf f ""
        | [h] -> Format.fprintf f "%a" fmt_element h
        | h :: t -> Format.fprintf f "%a; %a" fmt_element h aux t
    in Format.fprintf f "[%a]" aux l

  let fmt_env f l =
    let rec aux f l =
      match l with
        | [] -> Format.fprintf f ""
        | [h] -> Format.fprintf f "%a" fmt_cell h
        | h :: t -> Format.fprintf f "%a; %a" fmt_cell h aux t
    in Format.fprintf f "[%a]" aux l

  let fmt_in : Format.formatter -> in_func -> unit = fun f inf ->
    Format.fprintf f "%s((%s %a %s,%s %a %s,%s %a %s))%s" fontstyle endstyle fmt_env inf.env fontstyle endstyle Term.fmt inf.stream fontstyle endstyle Term.fmt inf.expr fontstyle endstyle

  let fmt_out : Format.formatter -> out_func -> unit = fun f outf ->
    Format.fprintf f "%s((%s %a %s,%s %a %s,%s %a %s,%s %a %s))%s" fontstyle endstyle fmt_env outf.env fontstyle endstyle Term.fmt outf.stream fontstyle endstyle Term.fmt outf.expr fontstyle endstyle fmt_stock outf.stock fontstyle endstyle


  let fmt : in_func ->  Format.formatter -> out_func -> unit = fun inf f outf ->
    Format.fprintf f "%a \x1b[1m\x1b[38;2;255;140;0m\n\t\t\t\u{2B46}\x1b[0m %a" fmt_in inf fmt_out outf


  let rec functional : in_func -> out_func option = fun c ->
    Format.printf "%a\n" fmt_in c; 
    match c.expr with
      | Arr f -> Some { env = c.env; stream = (App (f,c.stream)); expr = c.expr; stock = [] }
      (*| First sf ->  *)

      | Comp (sf1,sf2) -> begin match functional {c with expr = sf1} with
                                  | Some ofu -> begin match functional { env = ofu.env ; stream = ofu.stream; expr = Term.shift (List.length c.env) ((List.length ofu.env) - (List.length c.env)) sf2} with
                                                        | Some ofu' -> Some { ofu' with expr = (Comp (ofu.expr,ofu'.expr)); stock = List.append ofu.stock ofu'.stock }
                                                        | _ -> None
                                                end
                                  | _ -> None
                          end

      | First (ty,sf) -> let v = Eval.normalize (List.length c.env) c.stream in
                    begin match v with 
                            | Some Term.Pair (v1,v2) -> begin match functional {c with stream = v1; expr = sf} with
                                                      | Some ofu -> Some { ofu with stream = (Pair (ofu.stream,v2)); expr = First (ty,ofu.expr) }
                                                      | _ -> None
                                              end
                            | _ -> None
                    end

      | Rsf r ->   begin match List.nth_opt c.env r with
                            | Some (In v) -> Some { env = Utils.update r (Out c.stream) c.env; stream = v; expr = c.expr; stock = [] }
                            | _ -> Format.printf "\x1b[1m\x1b[38;2;210;0;0mMultiple use of the same resource ''\x1b[0m%a\x1b[1m\x1b[38;2;210;0;0m'' !!\n\x1b[0m" Id.fmt r; None
                    end

      | Wh (i,sf) -> begin match functional {env = List.append c.env [In i;In Unit]; stream = c.stream; expr = sf} with
                              | Some ofu -> Some  {ofu with stock = { read = (List.length c.env); write = ((List.length c.env) + 1); value = i } :: ofu.stock } 
                              | _ -> None
                      end

      | _  -> if Term.value c.expr  then begin 
                                        Format.printf "\x1b[1m\x1b[38;2;210;0;0mThe evaluation is stuck because it is a value but not evaluable by the functional rules !!\n\x1b[0m";
                                        None 
                                        end
                                  else begin match Eval.evaluate (List.length c.env) c.expr with
                                               | Some t' -> functional {env = c.env; expr = t'; stream = c.stream}
                                               | _ -> None
                                        end



end