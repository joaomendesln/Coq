From SP Require Export Nat.

(* ----------------------------------------- *)




(* natlist ::= [] | nat <+ natlist *)

Inductive natlist : Set :=
  | nil
  | cons (n : nat) (l : natlist)
.


Notation "h <+ t" := (cons h t)
                     (at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).




(* ----------------------------------------- *)




(* Deifinição 3.1. (append) *)

(* append : natlist X natlist -> natlist *)

(* Para um 'l1' e 'l2' arbitrárias no conjunto 'natlist', 
   [appendB] Caso l1 := []: append (l1, l2) = l2
   [appendR] Caso l1 := h <+ t: append (l1, l2) = h <+ append(t, l2) *)

Fixpoint append (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2 (* [appendB] *)
  | h <+ t => h <+ (append t l2) (* [appendR] *)
  end.


Notation "l1 ++ l2" := (append l1 l2)
                       (at level 60, right associativity).


(*  Teorema 3.1. Verifique que append é uma operação associativa, ou seja, (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3) para 'l1', 'l2' e 'l3' arbitrárias em 'natlist'. *)

Theorem append_assoc : forall (l1 l2 l3 : natlist),
  (l1 ++ l2) ++ l3 = l1 ++ l2 ++ l3.
Proof.

  (* Sejam 'l1', 'l2' e 'l3' elementos arbitrários de 'natlist'. *)
  intros l1 l2 l3.

   (* Demonstremos por indução estrutural em 'l1' que (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3) *)
  induction l1 as [| h t HI].

  (* [base: l1 := []] *)
  - (* [appendB] *)
    simpl.
    (* Reflexividade da '=' *)
    reflexivity.

  (* [passo indutivo] *)
  (* Seja 't' em 'natlist' tal que (t ++ l2) ++ l3 = t ++ (l2 ++ l3). *)
  (* Demonstremos que ((h <+ t) ++ l2) ++ l3 = (h <+ t) ++ (l2 ++ l3). *)
  - (* [appendR] *)
    simpl.
    (* Hipótese de indução *)
    rewrite HI.
    (* Reflexividade da '=' *)
    reflexivity.

Qed.




(* ----------------------------------------- *)




(* Deifinição 3.2. (length) *)

(* length : natlist -> nat *)

(* Para uma 'l' arbitrária no conjunto 'natlist', 
   [lengthB] Caso l := []: length (l) = O
   [lengthR] Caso l := h <+ t: length (l) = S length(t) *)

Fixpoint length (l : natlist) : nat :=
  match l with
  | nil => O (* [lengthB] *)
  | h <+ t => S (length t) (* [lengthB] *)
  end.


(* Teorema 3.2. Verifique que length (l1 ++ l2) = (length l1) + (length l2) para 'l1' e 'l2' arbitrárias em natlist. *)

Theorem append_length : forall (l1 l2 : natlist), 
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.

  (* Sejam 'l1' e 'l2' elementos arbitrários de 'natlist'. *)
  intros l1 l2.

  (* Demonstremos por indução estrutural em 'l1' que length (l1 ++ l2) = (length (l1)) + (length (l2)) *)
  induction l1 as [| h t HI].


  (* [base: l1 := []] *)
  - (* [lengthB] *)
    simpl.

    (* Reflexividade da '=' *)
    reflexivity.

  (* [passo indutivo] *)
  (* Seja 't' em 'natlist' tal que length (t ++ l2) = (length t) + (length l2). *)
  (* Demonstremos que length ((h <+ t) ++ l2) = (length h <+ t) + (length l2). *)
  - (* [appendR], [lengthR] e [plusR] *)
    simpl.

    (* Hipótese de indução *)
    rewrite HI.

    (* Reflexividade da '=' *)
    reflexivity.
Qed. 




(* ----------------------------------------- *)




(* Deifinição 3.3. (head) *)

(* head : natlist x nat -> nat *)

(* Para uma 'l' arbitrária no conjunto 'natlist' e um 'n' arbitrário no conjunto 'nat', 
   [head1] Caso l := []: head (l, n) = n
   [head2] Caso l := h <+ t: head (l, n) = h *)

Definition head (l : natlist) (n : nat) : nat :=
  match l with
  | nil => n (* [head1] *)
  | h <+ t => h (* [head2] *)
  end.


(* Teorema 3.3. Sejam 'l1' e 'l2' arbitrárias no conjunto 'natlist' e um 'n' arbitrário no conjunto 'nat'. Verifique que head ((l1 ++ l2), n) = head (l1, head(l2, n)). *)

Theorem head_append_assoc : forall (l1 l2 : natlist) (n : nat),
  head (l1 ++ l2) n = head l1 (head l2 n).
Proof.

  (* Sejam 'l1' e 'l2' elementos arbitrários de 'natlist' e 'n' um elemento arbitrário de 'nat'. *)
  intros l1 l2 n.

  destruct l1 as [| h t] eqn:E.

  (* Caso l1 = nil*)
  - (* [appendB] e [head1] *) 
    simpl.

    (* Reflexividade da '=' *)
    reflexivity.

  (* Caso l1 = h <+ t *)
  - (* [appendR] e [head2] *)
    simpl.

    (* Reflexividade da '=' *)
    reflexivity.
Qed.