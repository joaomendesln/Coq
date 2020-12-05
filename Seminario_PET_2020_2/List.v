(* natlist ::= [] | nat <+ natlist *)

Inductive natlist : Set :=
  | nil
  | cons (n : nat) (l : natlist).


Print natlist_rect.
Print natlist_ind.
Print natlist_rec.
Print natlist_sind.


Notation "h <+ t" := (cons h t)
                     (at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).




(* ----------------------------------------- *)




(* Definicao 3.1. (append) *)

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


(* Compute [1;2] ++ [4;5;6]. *)




(* ----------------------------------------- *)




(* Definicao 3.1. (length) *)

(* length : natlist -> nat *)

(* Para um 'l' arbitrária no conjunto 'natlist', 
   [lengthB] Caso l := []: length (l) = 0
   [lengthR] Caso l := h <+ t: length (l) = 1 + length(t) *)

Fixpoint length (l : natlist) : nat :=
  match l with
  | nil => O (* [lengthB] *)
  | h <+ t => S O + length t (* [lengthB] *)
  end.


(* Teorema 3.1. Verifique que length (l1 ++ l2) = (length l1) + (length l2) para 'l1' e 'l2' arbitrários em natlist.*)

Theorem app_length : forall (l1 l2 : natlist), 
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.

  (* Sejam 'l1' e 'l2' elementos arbitrários de 'natlist'. *)
  intros l1 l2.

  (* Demonstremos por indução estrutural em 'l1' que length (l1 ++ l2) = (length (l1)) + (length (l2)) *)
  induction l1 as [| h t IHt].

  
  (* [base: l1 := []] *)
  - (* [lengthB] *)
    simpl.

    (* Reflexividade da '=' *)
    reflexivity.

  (* [passo indutivo] *)
  (* Seja 't' em 'listnat' tal que length (t ++ l2) = (length t) + (length l2). *)
  (* Demonstremos que length ((h <+ t) ++ l2) = (length h <+ t) + (length l2). *)
  - (* [lengthR], soma? *)
    simpl.

    (* Hipótese de indução *)
    rewrite IHt.

    (* Reflexividade da '=' *)
    reflexivity.
Qed. 