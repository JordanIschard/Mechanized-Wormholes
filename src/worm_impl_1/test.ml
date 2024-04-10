open Wh.Wh
open Typ
open Utils
open Evaluation
open Functional

let test_lam = App (Abs("z",Typ.Prod (Typ.React (Typ.Unit,Typ.Unit,[]),Typ.Unit),Fst (Var "z")),Pair (App (Abs("x",Typ.Fun (Typ.Unit,Typ.Unit),Arr (Var "x")), Abs("y",Typ.Unit,Var "y")),Unit));;
let test_ast0 = App(Abs("x",Typ.React (Typ.Unit,Typ.Unit,[]) ,Comp(Wh("re","rw",Pair (Unit,Unit),Comp (Rsf (Tag "re"),Var "x")),Var "x")),Wh("r1","rw1",Unit,Rsf (Tag "r1")));;
let test1_ast0 = Abs("x",Typ.React (Typ.Unit,Typ.Unit,[(Tag "r");(Tag "w")]),Comp (Comp (Wh("re","rw",Unit,Comp (Rsf (Tag "re"),Rsf (Tag "w"))),Var "x"),Rsf (Tag "r")));;
let test_ast1 = BAbs("x",Typ.BReact (Typ.Unit,Typ.Unit,[(BTag 1);(BTag 0)]),Comp (Comp (BWh(Unit,Comp (BRsf (BTag 2),BRsf (BTag 0))),Var "x"),BRsf (BTag 1)));;
let test2_ast0 = Wh("re","rw",Unit,
                                  App(
                                    Abs("x",Typ.React (Typ.Unit,Typ.Unit,[(Tag "re")]),Comp(Wh("r1","rw1",Unit,Comp(Rsf(Tag "r1"),Var "x")),Var "x")),
                                    Wh("r2","rw2",Unit,Comp(Rsf (Tag "r2"),Rsf (Tag "re"))))
                                );;
let test3_ast0 = Wh("re","rw",Unit,
                                App(
                                  Abs("x",Typ.React (Typ.Unit,Typ.Unit,[(Tag "re")]),Comp(Wh("r1","rw1",Unit,Comp(Rsf(Tag "r1"),Var "x")),Var "x")),
                                  Wh("r2","rw2",Unit,Comp(Rsf (Tag "r2"),Comp(Rsf (Tag "rw1"),Rsf (Tag "re")))))
                              );;
let test1_ast1 = App(
                                BAbs("x",Typ.BReact (Typ.Unit,Typ.Unit,[(BTag 0)]),BWh (Unit,Comp(BRsf (BTag 0),Comp(BRsf (BTag 1),Var "x")))),
                                BRsf(BTag 0));;

                                
let bench_transition_block raw_expr reflist =

  Format.printf "\x1b[1m\x1b[38;2;210;0;0m========================================\n";
  Format.printf "\x1b[1m=              Transition              =\n\n\x1b[0m";
  Format.printf "\x1b[1m\x1b[38;2;210;0;0m [[\x1b[0m%a\x1b[1m\x1b[38;2;210;0;0m]]\x1b[0m \x1b[38;2;210;0;0musing %a\x1b[0m\n\t\t\x1b[1m\x1b[38;2;210;0;0m == \x1b[0m" fmt raw_expr fmt_var_list reflist;
  let lvl_expr = transition reflist raw_expr in
  (match lvl_expr with
    | Some expr ->  Format.printf "%a\n" fmt expr;
                    Format.printf "\x1b[1m\x1b[38;2;0;128;0m Is valid?          :\x1b[0m %b\n" (valid (List.length reflist) expr);
                    Format.printf "\x1b[1m\x1b[38;2;0;128;0m Is value?          :\x1b[0m %b\n\n" (value expr);
    | None -> Format.printf "None \n\n\n");
  lvl_expr
;;
     
let bench_compare_block expr1 expr2 =
  Format.printf "\x1b[1m========================================\n";
  Format.printf "\x1b[1m=                Compare               =\n\n";
  Format.printf "\x1b[1m\x1b[38;2;255;165;0m Expression 1  :\x1b[0m %a\n" fmt expr1;
  Format.printf "\x1b[1m\x1b[38;2;255;165;0m Expression 2  :\x1b[0m %a\n" fmt expr2;
  Format.printf "\x1b[1m\x1b[38;2;0;128;0m Are equal?    :\x1b[0m %b\n\n" (expr1 = expr2);;

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


let bench_functional (envr : Func.cell list) expr =
  let e : Func.in_func ref = ref {Func.env = envr; stream = Unit; expr = expr} in
  Format.printf "\x1b[1m\x1b[38;2;255;140;0m========================================\n";
  Format.printf "=              Functional              =\x1b[0m\n\n";
  match Func.functional !e with
   | Some e' -> Format.printf "%a\n" (Func.fmt !e)  e';
                Format.printf "\x1b[1m\x1b[38;2;0;128;0m Is valid?   :\x1b[0m %b\n" (valid (List.length e'.env) e'.expr);
                Format.printf "\x1b[1m\x1b[38;2;0;128;0m Is value?   :\x1b[0m %b\n\n" (value e'.expr)
   | _ -> () 
;;


let bench raw_expr lvl_expr reflist env =
  Random.self_init ();
  Format.printf "\n\n\x1b[1m========================================\n";
  Format.printf "\x1b[1m=               Benchmark              =\n";
  Format.printf "\x1b[1m========================================\n\n";
  match raw_expr,lvl_expr with
    | Some expr, Some expr' ->  Format.printf "\x1b[1m\x1b[38;2;114;159;207m Raw expression     :\x1b[0m %a\n" fmt expr;
                                Format.printf "\x1b[1m\x1b[38;2;114;159;207m Free resources     :\x1b[0m %a\n\n" fmt_var_list reflist;
                                begin match bench_transition_block expr reflist with
                                  | Some expr1 -> bench_compare_block expr1 expr'; bench_shift_block expr1 (List.length reflist) (Random.int 10);
                                                  ignore (bench_beta_block expr1 (List.length reflist) );
                                                  bench_functional env expr'
                                  | _ -> ()
                                end
    | Some expr,None -> Format.printf "\x1b[1m\x1b[38;2;114;159;207m Raw expression     :\x1b[0m %a\n" fmt expr;
                        Format.printf "\x1b[1m\x1b[38;2;114;159;207m Free resources     :\x1b[0m %a\n\n" fmt_var_list reflist;
                        begin match bench_transition_block expr reflist with
                          | Some expr1 -> bench_shift_block expr1 (List.length reflist) (Random.int 10);
                                          ignore (bench_beta_block expr1 (List.length reflist) );
                                          bench_functional env expr1
                          | _ -> ()
                        end
    | None, Some expr ->  Format.printf "\x1b[1m\x1b[38;2;255;165;0m Bruijn expression  :\x1b[0m %a\n" fmt expr;
                          Format.printf "\x1b[1m\x1b[38;2;0;128;0m Is valid?          :\x1b[0m %b\n" (valid (List.length reflist) expr);
                          Format.printf "\x1b[1m\x1b[38;2;0;128;0m Is value?          :\x1b[0m %b\n\n" (value expr);
                          bench_shift_block expr (List.length reflist) (Random.int 10);
                          ignore (bench_beta_block expr (List.length reflist) );
                          bench_functional env expr
    | None, None -> ()
;;

(** basic expression *)
bench (Some test_lam) None [] [];; 

(** Test of transition, already a value but not reactive *)
bench (Some test1_ast0) (Some test_ast1) (get_FRf test1_ast0) [Func.In Unit; Func.In Unit];;

(** Test of transition with wrong set of free resources *)
bench (Some test1_ast0) None [] [];;

(** Test of transition, application of a wormhole into another one and functional transition (perhaps the most important one) *)
bench (Some test_ast0) None (get_FRf test_ast0) [];;

(** Test of transition, application of a wormhole into another one and multiple use of a resource ! *)
bench (Some test2_ast0) None (get_FRf test2_ast0) [];;

(** Test of transition, application of a wormhole into another one and multiple use of a resource ! *)
bench (Some test3_ast0) None (get_FRf test3_ast0) [];;

(** Test of evaluation with an application *)
bench None (Some test1_ast1) [""] [Func.In Unit];;
