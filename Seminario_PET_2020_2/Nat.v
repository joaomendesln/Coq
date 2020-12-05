(* nat ::= O | S nat *)

Inductive nat: Set :=
  | O 
  | S (n : nat)
.


Print nat_rect.
Print nat_ind.
Print nat_rec.
Print nat_sind.


(* 'O' pertence ao conjunto 'nat'; *)
(* Se 'n' e uma expressão construtora pertencente ao conjunto 'nat', então o construtor 'S' aplicado ao argumento 'n' pertence ao conjunto 'nat'; *)
(* Essas são as únicas expressões construtoras que pertencem ao conjunto 'nat'. *)




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


Compute pred (S (S (S O))).




(* ----------------------------------------- *)




(* Definicao 2.2. (add) *)

(* add: nat X nat -> nat *)

(* [addB] Para um 'm' arbitrario no conjunto 'nat', 
          soma (0, m) = m *)
(* [addR] Para todos 'm' e 'n' do tipo 'nat',
          soma (S n, m) = S (soma (n, m)) *)


Fixpoint add (n m : nat) : nat :=
  match n with
  | O => m (* [addB] *)
  | S n => S (add n m) (* [addR] *)
  end.


(*Calculemos soma (S (S O), S (S O)).*)

Compute add (S (S O)) (S (S O)).




(* ----------------------------------------- *)




(* Definicao 2.2. (mult) *)

(* mult: nat X nat -> nat *)

(* [multB] Para um 'm' arbitrario do conjunto 'nat', 
           mul (O, m) = O *)
(* [multR] Para todos 'm' e 'n' do conjunto 'nat', 
           mul (n, S (m)) = add ( mult (m, n) ) *)


Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O (* [mulB] *)
  | S n => add m (mult n m) (* [mulR] *)
  end.



Compute mult (S (S O)) (S (S (S O))).




(* ----------------------------------------- *)




Notation "x + y" := (add x y)
(at level 50, left associativity).

Notation "x * y" := (mult x y)
(at level 40, left associativity).




(* ----------------------------------------- *)




(* Teorema 2.1. Verifique que, para qualquer 'n' do conjunto 'nat', n + O = n. *)
Theorem soma_n_O : forall (n : nat),
  n + O = n.
Proof.

  (* Seja 'n' um elemento arbitrário de 'nat'. *)
  intro n.

  (* apply (nat_ind (fun n => n + O = n)).  *)

  (* Demonstremos por indução em 'n' que n + O = n *)
  induction n as [| k HI].

  (* [base: n := O] *)
  - (* [somaB] *)
    simpl.

    (* Reflexividade da '=' *)
    reflexivity.

  (* [passo indutivo] *)
  (* Seja 'k' um elemento de 'nat' tal que k + O = k. *)
  (* Demonstremos que Sk + O = Sk. *)
  - (* [somaR] *)
    simpl.

    (* Hipótese de indução*) 
    rewrite HI.

    (* Reflexividade da '=' *)
    reflexivity.

Qed.




(* ----------------------------------------- *)




(* Teorema 2.2. Verifique que, para qualquer 'n' do tipo 'nat', n * O = O. *)
Lemma mult_n_O : forall (n : nat),
  n * O = O.
Proof.
  
  (* Seja 'n' um elemento arbitrario de 'nat'. *)
  intro n.

  (* Demonstremos por inducao em 'n' que n * O = O *)
  induction n as [| j HI].

  (* [base: n := O] *)
  - (* [multB] *) 
    simpl.

    (* Reflexividade da '=' *)
    reflexivity.

  (* [passo indutivo] *)
  (* Seja 'j' um elemento de 'nat' tal que j * O = O. *)
  (* Demonstremos que Sj * O = Sj. *)
  - (* [multR] *) 
    simpl.

    (* Hipótese de indução *)      
    apply HI.

Qed.




(* ----------------------------------------- *)




(* Teorema 2.3. Verifique que n * O + m * O = 0 para 'n' e 'm' arbitrários em 'nat'. *)
Theorem mult_n_O_m_0 : forall (n m : nat),
  n * O + m * O = O.
Proof.

  (* Sejam 'n' e 'm' em nat. *)
  intros n m.

  (* Pelo Teorema 2.2., temos que n * O = O e m * O = O *)
  repeat rewrite mult_n_O.

  (* [somaB] *)
  simpl.

  (* Reflexividade da '=' *)
  reflexivity.

Qed.