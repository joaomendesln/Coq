Require Import Nat.

Compute 3 + 4.


(* nat ::= O | S nat *)

Inductive nat: Set :=
  | O 
  | S (n : nat)
.

(* 'O' pertence ao conjunto 'nat'; *)
(* Se 'n' é uma expressão construtora pertencente ao conjunto 'nat', então o construtor 'S' aplicado ao argumento 'n' pertence ao conjunto 'nat'; *)
(* Essas são as únicas expressões construtoras que pertencem ao conjunto 'nat'. *)


Print nat_ind.




(* ----------------------------------------- *)




(* Deifinição 2.1. (pred) *)

(* pred : nat -> nat *)

(* Para um 'n' arbitrario no conjunto 'nat', 
   [predB] Caso n := O: pred (n) = O
   [predR] Caso n := S n': pred (n) = n' *)

Definition pred (n : nat) : nat :=
  match n with
  | O => O (* [predB] *)
  | S n => n (* [predR] *)
  end.




(* ----------------------------------------- *)




(* Definicao 2.2. (plus) *)

(* plus: nat X nat -> nat *)

(* [plusB] Para um 'm' arbitrário no conjunto 'nat', 
          plus (O, m) = m *)
(* [plusR] Para todos 'm' e 'n' do tipo 'nat',
          plus (S n, m) = S (plus (n, m)) *)


Fixpoint plus (n m : nat) : nat :=
  match n with
  | O => m (* [plusB] *)
  | S n => S (plus n m) (* [plusR] *)
  end.




(* ----------------------------------------- *)




(* Definicao 2.2. (mult) *)

(* mult: nat X nat -> nat *)

(* [multB] Para um 'm' arbitrário do conjunto 'nat', 
           mult (O, m) = O *)
(* [multR] Para todos 'm' e 'n' do conjunto 'nat', 
           mult (S (n), m) = plus (m, (mult (n, m))) *)


Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O (* [multB] *)
  | S n => plus m (mult n m) (* [multR] *)
  end.

Check mult.




(* ----------------------------------------- *)




Notation "x + y" := (plus x y)
(at level 50, left associativity).

Notation "x * y" := (mult x y)
(at level 40, left associativity).




(* ----------------------------------------- *)




(* Teorema 2.1. Verifique que, para qualquer 'n' do conjunto 'nat', n + O = n. *)
Theorem plus_n_O : forall (n : nat),
  n + O = n.
Proof.

  (* Seja 'n' um elemento arbitrário de 'nat'. *)
  intro n.

  (* Demonstremos por indução em 'n' que n + O = n *)
  induction n as [| k HI].

  (* OBS: O que essa tática faz é aplicar nat_ind *)


  (* [base: n := O] *)
  - (* [plusB] *)
    simpl.

    (* Reflexividade da '=' *)
    reflexivity.

  (* [passo indutivo] *)
  (* Seja 'k' um elemento qualquer de 'nat' tal que k + O = k. *)
  (* Demonstremos que Sk + O = Sk. *)
  - (* [plusR] *)
    simpl.

    (* Hipótese de indução *) 
    rewrite HI.

    (* Reflexividade da '=' *)
    reflexivity.

Qed.




(* ----------------------------------------- *)




(* Teorema 2.2. Verifique que, para qualquer 'n' do tipo 'nat', n * O = O. *)




(* ----------------------------------------- *)




(* Teorema 2.3. Verifique que n * O + m * O = 0 para 'n' e 'm' arbitrários em 'nat'. *)