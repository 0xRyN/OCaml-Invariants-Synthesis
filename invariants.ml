open Printf

(* Définitions de terme, test et programme *)
type term = 
  | Const of int
  | Var of int
  | Add of term * term
  | Mult of term * term

type test = 
  | Equals of term * term
  | LessThan of term * term
  | NEquals of term * term
  | SupOrEqual of term * term

let tt = Equals (Const 0, Const 0)
let ff = LessThan (Const 0, Const 0)

type program = {nvars : int; 
                inits : term list; 
                mods : term list; 
                loopcond : test; 
                assertion : test}

let x n = "x" ^ string_of_int n


(* Question 1. Écrire des fonctions `str_of_term` et `str_of_term` qui
   convertissent des termes et des tests en chaînes de caractères du
   format SMTLIB.

   Par exemple, str_of_term (Var 3) retourne "x3", str_of_term (Add 
   (Var 1, Const 3)) retourne "(+ x1 3)" et str_of_test (Equals (Var
   2, Const 2)) retourne "(= x2 2)".  *)
let rec str_of_term (t:term) :string = match t with 
  | Const(i) -> string_of_int i
  | Var(i) -> "x" ^ (string_of_int i)
  | Add(t1, t2) -> "(" ^ "+ " ^ (str_of_term t1) ^ " " ^ (str_of_term t2) ^ ")"
  | Mult(t1, t2) -> "(" ^ "* " ^ (str_of_term t1) ^ " " ^ (str_of_term t2) ^ ")"

let str_of_test (t:test) :string = match t with 
  | Equals(t1, t2) -> "(" ^ "= " ^ (str_of_term t1) ^ " " ^ (str_of_term t2) ^ ")"
  | LessThan(t1, t2) -> "(" ^ "< " ^ (str_of_term t1) ^ " " ^ (str_of_term t2) ^ ")"
  | NEquals(t1, t2) -> "(" ^ "not (= " ^ (str_of_term t1) ^ " " ^ (str_of_term t2) ^ "))"
  | SupOrEqual(t1, t2) -> "(" ^ ">= " ^ (str_of_term t1) ^ " " ^ (str_of_term t2) ^ ")"

let string_repeat s n =
  Array.fold_left (^) "" (Array.make n s)

(* Question 2. Écrire une fonction str_condition qui prend une liste
   de termes t1, ..., tk et retourne une chaîne de caractères qui
   exprime que le tuple (t1, ..., tk) est dans l'invariant.  Par
   exemple, str_condition [Var 1; Const 10] retourne "(Invar x1 10)".
*)
let str_condition (l: term list) :string =
  let rec aux acc list = match list with
    | [] -> acc ^ ")"
    | hd :: tl -> aux (acc ^ " " ^ str_of_term hd) tl

  in aux ("(Invar") (l)

(* Question 3. Écrire une fonction str_assert_for_all qui prend en
   argument un entier n et une chaîne de caractères s, et retourne
   l'expression SMTLIB qui correspond à la formule "forall x1 ... xk
   (s)".

   Par exemple, str_assert_forall 2 "< x1 x2" retourne : 
   "(assert (forall ((x1 Int) (x2 Int)) (< x1 x2)))". 
*)
let str_assert s = "(assert " ^ s ^ ")"

let str_assert_forall (n: int) (s: string) :string =
  let rec aux acc k = match k with
    | 0 -> acc ^ ") (" ^ s ^ "))" (* Append the s string + it's parenthesis' *)
    | i -> 
      if i = 1 then ( aux (acc ^ "(" ^ str_of_term (Var(n-i+1)) ^ " Int)") (k-1) ) (* Last variable, don't put indentation *)
      else aux (acc ^ "(" ^ str_of_term (Var(n-i+1)) ^ " Int) ") (k-1) (* Normal variable, add indentation *)

  in 
  let res = aux "(forall (" n in
  str_assert res


(* FCT UTILITAIRE : *)

let invar_of_vars (i: int) :string = 
  let rec aux acc k = match k with
    | 0 -> acc ^ ")"
    | k' -> aux (acc ^ " " ^ str_of_term(Var(i-k+1))) (k-1)
  in aux "(Invar" i 

let opposite_of_test (t:test) :test = match t with
  | LessThan(e1, e2) -> SupOrEqual(e1, e2)
  | Equals(e1, e2) -> NEquals(e1, e2)
  | _ -> failwith "No no dont touch that"


(* Question 4. Nous donnons ci-dessous une définition possible de la
   fonction smt_lib_of_wa. Complétez-la en écrivant les définitions de
   loop_condition et assertion_condition. *)

let smtlib_of_wa p = 
  let declare_invariant n =
    "; synthèse d'invariant de programme\n"
    ^"; on déclare le symbole non interprété de relation Invar\n"
    ^"(declare-fun Invar (" ^ string_repeat "Int " n ^  ") Bool)" in
  let loop_condition p =
    "; la relation Invar est un invariant de boucle\n"
    ^ str_assert_forall (p.nvars) ("=> (and " ^ invar_of_vars p.nvars ^ " " ^ str_of_test p.loopcond ^ ") " ^ str_condition p.mods) in 
  let initial_condition p =
    "; la relation Invar est vraie initialement\n"
    ^str_assert (str_condition p.inits) in
  let assertion_condition p =
    "; l'assertion finale est vérifiée\n"
    ^ str_assert_forall (p.nvars) ("=> (and " ^ invar_of_vars p.nvars ^ " " ^ str_of_test (opposite_of_test p.loopcond) ^ ") " ^ str_of_test p.assertion) in
  let call_solver =
    "; appel au solveur\n(check-sat-using (then qe smt))\n(get-model)\n(exit)\n" in
  String.concat "\n" [declare_invariant p.nvars;
                      loop_condition p;
                      initial_condition p;
                      assertion_condition p;
                      call_solver]

let p1 = {nvars = 2;
          inits = [(Const 0) ; (Const 0)];
          mods = [Add ((Var 1), (Const 1)); Add ((Var 2), (Const 3))];
          loopcond = LessThan ((Var 1),(Const 3));
          assertion = Equals ((Var 2),(Const 9))}

let p2 = {nvars = 3;
          inits = [(Const 3) ; (Const 1); (Const 6)];
          mods = [Add ((Var 1), (Const 1)); Mult ((Var 2), (Const 2)); Mult ((Var 3), (Const 7))];
          loopcond = LessThan ((Var 2),(Const 60));
          assertion = NEquals ((Var 3),(Const 30))} (* p2 implémente NEquals aussi ! *)

(* RESULTAT DU TEST
   sat
   (
   (define-fun Invar ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (or (and (not (= x!0 7))
             (not (= x!0 6))
             (= x!0 5)
             (<= 1 x!1)
             (<= 2 x!1)
             (<= 4 x!1)
             (not (<= 8 x!1))
             (not (= x!2 14406))
             (not (= x!2 2058))
             (not (= x!2 42))
             (not (= x!2 100842))
             (not (= x!2 6))
             (= x!2 294))
        (and (not (= x!0 7))
             (not (= x!0 6))
             (not (= x!0 5))
             (not (= x!0 3))
             (not (= x!0 2))
             (not (= x!0 0))
             (= x!0 9)
             (<= 1 x!1)
             (<= 2 x!1)
             (<= 4 x!1)
             (<= 8 x!1)
             (<= 15 x!1)
             (<= 16 x!1)
             (<= 30 x!1)
             (<= 32 x!1)
             (<= 59 x!1)
             (<= 60 x!1)
             (<= 64 x!1)
             (not (= x!2 14406))
             (not (= x!2 2058))
             (not (= x!2 42))
             (not (= x!2 100842))
             (not (= x!2 6))
             (not (= x!2 294))
             (not (= x!2 30)))
        (and (not (= x!0 7))
             (not (= x!0 6))
             (not (= x!0 5))
             (not (= x!0 3))
             (not (= x!0 2))
             (not (= x!0 0))
             (not (= x!0 9))
             (not (= x!0 4))
             (not (= x!0 10))
             (not (= x!0 (- 1)))
             (= x!0 8)
             (<= 1 x!1)
             (<= 2 x!1)
             (<= 4 x!1)
             (<= 8 x!1)
             (<= 15 x!1)
             (<= 16 x!1)
             (<= 30 x!1)
             (<= 32 x!1)
             (not (<= 59 x!1))
             (not (= x!2 14406))
             (not (= x!2 2058))
             (not (= x!2 42))
             (= x!2 100842))
        (and (not (= x!0 7))
             (not (= x!0 6))
             (not (= x!0 5))
             (not (= x!0 3))
             (not (= x!0 2))
             (not (= x!0 0))
             (not (= x!0 9))
             (= x!0 4)
             (<= 1 x!1)
             (<= 2 x!1)
             (not (<= 4 x!1))
             (not (= x!2 14406))
             (not (= x!2 2058))
             (= x!2 42))
        (and (not (= x!0 7))
             (= x!0 6)
             (<= 1 x!1)
             (<= 2 x!1)
             (<= 4 x!1)
             (<= 8 x!1)
             (not (<= 15 x!1))
             (not (= x!2 14406))
             (= x!2 2058))
        (and (not (= x!0 7))
             (not (= x!0 6))
             (not (= x!0 5))
             (= x!0 3)
             (<= 1 x!1)
             (not (<= 2 x!1))
             (not (= x!2 14406))
             (not (= x!2 2058))
             (not (= x!2 42))
             (not (= x!2 100842))
             (= x!2 6))
        (and (= x!0 7)
             (<= 1 x!1)
             (<= 2 x!1)
             (<= 4 x!1)
             (<= 8 x!1)
             (<= 15 x!1)
             (<= 16 x!1)
             (not (<= 30 x!1))
             (= x!2 14406))))
   )
*)


let () = Printf.printf "%s" (smtlib_of_wa p2)

(* Question 5. Vérifiez que votre implémentation donne un fichier
   SMTLIB qui est équivalent au fichier que vous avez écrit à la main
   dans l'exercice 1. Ajoutez dans la variable p2 ci-dessous au moins
   un autre programme test, et vérifiez qu'il donne un fichier SMTLIB
   de la forme attendue. *)
