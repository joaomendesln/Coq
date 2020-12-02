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

(* pred : natlist X natlist -> natlist *)

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


Compute [1;2] ++ [4;5;6].




(* ----------------------------------------- *)




(* Definicao 3.1. (length) *)

(* length : natlist -> nat *)

(* Para um 'l' arbitrária no conjunto 'natlist', 
   [lengthB] Caso l := []: length (l) = 0
   [lengthR] Caso l := h <+ t: length (l) = 1 + length(t) *)

Fixpoint length (l : natlist) : nat :=
  match l with
  | nil => 0 (* [lengthB] *)
  | h <+ t => 1 + length t (* [lengthB] *)
  end.

Compute length [0;7;4].


(* Teorema 3.1. Demonstre que 'length' distribui sobre 'append'.*)

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

    reflexivity.

  (* [passo indutivo] *)
  (* Seja 't' em 'listnat' tal que length (t ++ l2) = (length t) + (length l2). *)
  (* Demonstremos que length ((h <+ t) ++ l2) = (length h <+ t) + (length l2). *)
  - (* [lengthR], soma? *)
    simpl.

    (* Hipótese de indução *)
    rewrite IHt.

    reflexivity.
Qed. 




(* ----------------------------------------- *)




(* Definicao 3.2. (reverse) *)

(* length : natlist -> natlist *)

(* Para um 'l' arbitrária no conjunto 'natlist', 
   [reverseB] Caso l := []: reverse (l) = []
   [reverseR] Caso l := h <+ t: reverse (l) = append (reverse(t), h) *)

Fixpoint reverse (l : natlist) : natlist :=
  match l with
  | nil => nil (* [reverseB] *)
  | h <+ t => reverse t ++ [h] (* [reverseR] *)
  end.

Compute reverse [1;2;3].


(* Teorema 3.2. Seja 'l' um elemento de 'listnat'. Verifique que length (reverse (l)) = length (l) *)
Theorem rev_length : forall (l : natlist),
  length (reverse l) = length l.
Proof.
  (* Seja 'l' um elemento de 'listanat'. *)
  intro l.

  (* Demonstremos por indução estrutural em 'l' que length (reverse (l)) = length (l) *)
  induction l as [| h t IHt].

  (* [base: l1 := []] *)
  - (* [lengthB] *)
    simpl. 

    reflexivity.
  
  (* [passo indutivo] *)
  (* Seja 't' em 'listnat' tal que length (reverse (t)) = length (t). *)
  (* Demonstremos que length ((h <+ t) ++ l2) = length (h <+ t) + length (l2). *)
  - (* [lengthR] *)
    simpl.

    (* Teorema 3.1 *)
    rewrite app_length.

    (* Hipótese de indução *)
    rewrite IHt.

    (* [lengthR], [lengthB], soma??? *)
    simpl.
  assert (H : forall (n m : nat), n + m = m + n).
    + admit.
    + rewrite H. simpl. reflexivity.
  
