Inductive state: Set :=
  | s1
  | s2
.

Inductive bi: Set :=
  | O
  | I
.

Inductive bilist: Set :=
  | nil
  | cons (b: bi) (l: bilist)
.

Notation "h <+ t" := (cons h t)
                     (at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint append (l1 l2 : bilist) : bilist :=
  match l1 with
  | nil => l2
  | h <+ t => h <+ (append t l2)
  end.


Notation "l1 ++ l2" := (append l1 l2)
                       (at level 60, right associativity).

Theorem app_nil : forall (b : bilist),
  b ++ [] = b.
Proof.  
  intro b.
  induction b.
  - simpl. reflexivity.
  - simpl. rewrite IHb.
    reflexivity.
Qed.

Definition tr (b : bi) (s : state) : state :=
  match b, s with
  | O, s1 => s2
  | I, s1 => s1
  | O, s2 => s1
  | I, s2 => s2
  end.

Fixpoint trans (l : bilist) (s : state) : state :=
  match l with
  | nil => s
  | h <+ t => trans t (tr h s)
  end.

Class Monoid := {
  M : Set;
  e : M;
  op1 : M -> M -> M;
  op1_id1: forall x, op1 x e = x;
  op1_id2: forall x, op1 e x = x; 
  op_assoc: forall x y z, op1 (op1 x y) z = op1 x (op1 y z);
}.

Section Monoid_H.

Context `{Mo: Monoid}. 

Check M.

Class Monoid_H := {
  S : Set;
  op2 : M -> S -> S;
  op_assoc_h: forall x y z, op2 (op1 x y) z = op2 x (op2 y z);
  op2_id1: forall x, op2 e x = x;
}.
End Monoid_H.

Section InstanceMonoidH.
  Program Instance MApp : Monoid :=
    {|
      M := bilist;
      e:= nil;
      op1 := append
    |}.
  Next Obligation.
    apply app_nil.
  Qed.
  Next Obligation.
    simpl. reflexivity.
  Qed.
  Next Obligation.
    intros x y z.
    induction x.
    - simpl. reflexivity.
    - simpl. rewrite IHx.
      reflexivity.
  Qed. 

  Check  Monoid_H.

  Program Instance MAppH : Monoid_H :=
    {|
      S := state;
      op2 := trans
    |}.

    Next Obligation.
    (*  *)
End InstanceMonoidH.