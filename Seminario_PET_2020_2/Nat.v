Inductive nat: Type :=
  | O 
  | S (n : nat).


Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

Fixpoint plus (n m : nat) : nat :=
  match n with
  | O => m
  | S n => S (plus n m)
  end.

Compute plus (S (S O)) (S (S O)).

Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n => plus m (mult n m)
  end.

Compute mult (S (S O)) (S O).

Compute mult (S (S O)) (S (S O)).

Notation "x + y" := (plus x y)
(at level 50, left associativity).

Notation "x * y" := (mult x y)
(at level 40, left associativity).

Theorem plus_n_O : forall (n : nat),
  n + O = n.
Proof.
  intro n.
  induction n as [| k IHk].
  - simpl. reflexivity.
  - simpl. rewrite IHk.
    reflexivity.
Qed.



Lemma mult_n_O : forall (n : nat),
  n * O = O.
Proof.
  intro n.
  induction n as [| k' IHk'].
  - simpl. reflexivity.
  - simpl. apply IHk'.
Qed.

Theorem mult_n_O_m_0 : forall (x y : nat),
  x * O + y * O = O.
Proof.
  intros x y.
  rewrite mult_n_O;
  rewrite mult_n_O.
  simpl. reflexivity.
Qed.
