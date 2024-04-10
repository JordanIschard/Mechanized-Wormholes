open Term.Term
open Typ
open Utils
open Evaluation
open Functional
open Typing

let test1 = App (Abs("z",Typ.Prod (Typ.React (Typ.Unit,Typ.Unit,[]),Typ.Unit),Fst (Var "z")),Pair (App (Abs("x",Typ.Fun (Typ.Unit,Typ.Unit),Arr (Var "x")), Abs("y",Typ.Unit,Var "y")),Unit));;
let test2 = Abs("x",
                    Typ.React (Typ.Unit,Typ.Unit,[1;0]),
                    Comp (
                      Comp (Wh(Unit,Comp (Rsf 2,Rsf 0)),Var "x"),
                      Rsf 1));;
let test2 = App(
                      Abs("x",Typ.React (Typ.Unit,Typ.Unit,[0]),Wh (Unit,Comp(Rsf 0,Comp(Rsf 1,Var "x")))),
                      Rsf 0);;
let test3 = App(
                      Abs("x",Typ.React (Typ.Unit,Typ.Unit,[]),Wh (Unit,Comp(Rsf 0,Comp(Rsf 1,Var "x")))),
                      Wh(Unit,Rsf 0));;


let bench_shift_block expr lb sh =
  Format.printf "\x1b[1m\x1b[38;2;154;205;50m========================================\n";
  Format.printf "\x1b[1m\x1b[38;2;154;205;50m=                 Shift                =\n\n\x1b[0m";
  Format.printf "\x1b[1m\x1b[38;2;154;205;50m[>> %d < %d]\x1b[0m %a \n\t\t\x1b[1m\x1b[38;2;154;205;50m==\x1b[0m %a\n\n" lb sh fmt expr fmt (shift lb sh expr)
;;

let bench_beta_block expr lb =
  let e = ref expr in
  Format.printf "\x1b[1m\x1b[38;2;153;50;204m\x1b[1m========================================\n";
  Format.printf "\x1b[1m\x1b[38;2;153;50;204m=              Evaluate               =\n\n\x1b[0m";
  match Eval.normalize lb !e with
    | Some e' -> Format.printf " %a\n" (Eval.fmt lb !e) e';
                 Format.printf "\x1b[1m\x1b[38;2;0;128;0m Is valid? :\x1b[0m %b\n" (valid lb e');
                 Format.printf "\x1b[1m\x1b[38;2;0;128;0m Is value? :\x1b[0m %b\n\n" (value e');
    | _ -> Format.printf " None\n\n"
;;


let bench_typing env expr =
  Format.printf "\x1b[1m\x1b[38;2;255;140;0m========================================\n";
  Format.printf "=              Typing              =\x1b[0m\n\n";
  match Typing.typing [] env expr with
   | Some ty -> Format.printf "%a \u{22A2} %a :: %a\n" Typing.fmt_rcontext env fmt expr Typ.fmt ty
   | _ ->  Format.printf "%a \u{22AC} %a\n" Typing.fmt_rcontext env fmt expr
;;

let bench_functional (envr : Functional.cell list) expr =
  let e : Functional.in_func ref = ref {Functional.env = envr; stream = Unit; expr = expr} in
  Format.printf "\x1b[1m\x1b[38;2;255;140;0m========================================\n";
  Format.printf "=              Functional              =\x1b[0m\n\n";
  match Functional.functional !e with
   | Some e' -> Format.printf "%a\n" (Functional.fmt !e)  e';
                Format.printf "\x1b[1m\x1b[38;2;0;128;0m Is valid?   :\x1b[0m %b\n" (valid (List.length e'.env) e'.expr);
                Format.printf "\x1b[1m\x1b[38;2;0;128;0m Is value?   :\x1b[0m %b\n\n" (value e'.expr)
   | _ -> () 
;;


let bench expr (env : (Functional.cell * (Identifier.Id.t * (Typ.t * Typ.t))) list) =
  let ub = List.length env in
  let (vl_env,ty_env) = List.split env in
  Random.self_init ();
  Format.printf "\n\n\x1b[1m========================================\n";
  Format.printf "\x1b[1m=               Benchmark              =\n";
  Format.printf "\x1b[1m========================================\n\n";
  Format.printf "\x1b[1m\x1b[38;2;255;165;0m Expression          :\x1b[0m %a\n" fmt expr;
  Format.printf "\x1b[1m\x1b[38;2;0;128;0m Is valid?          :\x1b[0m %b\n" (valid ub expr);
  Format.printf "\x1b[1m\x1b[38;2;0;128;0m Is value?          :\x1b[0m %b\n\n" (value expr);
  bench_shift_block expr ub (Random.int 10);
  ignore (bench_beta_block expr ub );
  bench_typing ty_env expr;
  bench_functional vl_env expr
;;

(** basic expression *)
bench test1 [];; 

bench test2 [((Functional.In Unit),(0,(Typ.Unit,Typ.Unit)));(Functional.In Unit,(1,(Typ.Unit,Typ.Unit)))];;

(** Test of evaluation with an application *)
bench test2 [(Functional.In Unit,(0,(Typ.Unit,Typ.Unit)))];;

bench test3 [Functional.In Unit,(0,(Typ.Unit,Typ.Unit))];;
