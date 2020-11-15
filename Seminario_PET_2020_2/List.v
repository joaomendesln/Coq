(*Importar*)

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "h <+ t" := (cons h t)
                     (at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


(*Reconsiderar estas duas funcoes*)

Definition head (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h <+ t => h
  end.

Definition tail (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h <+ t => t
  end.

(*Mostrar exemplos de head e tail e funcionando*)






Fixpoint append (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h <+ t => h <+ (append t l2)
  end.

Fixpoint length (l : natlist) : nat :=
  match l with
  | nil => 0
  | h <+ t => S (length t)
  end.

Notation "l1 ++ l2" := (append l1 l2)
                       (at level 60, right associativity).


Theorem app_length : forall (l1 l2 : natlist), 
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2.
  induction l1 as [| h t IHt].
  - simpl. reflexivity.
  - simpl. rewrite IHt.
    reflexivity.
Qed. 




Fixpoint reverse (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h <+ t => reverse t ++ [h]
  end.


Theorem rev_length : forall (l : natlist),
  length (reverse l) = length l.
Proof.
  intro l.
  induction l as [| h t IHt].
  - simpl. reflexivity.
  - simpl. rewrite app_length.
  rewrite IHt. 
  assert (H : forall (n m : nat), n + m = m + n).
    + admit.
    + rewrite H. simpl. reflexivity.
  
