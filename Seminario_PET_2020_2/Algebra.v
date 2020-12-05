Require Import Nat.
From SP Require Export List.


Class Monoid_H := {
  M : Set;
  e : M;
  op1 : M -> M -> M;
  op2 : M -> M -> M;
  op_assoc: forall x y z, op2 (op1 x y) z = op2 x (op2 y z);
  op_id1: forall x, op1 x e = x;
  op_id2: forall x, op1 e x = x; 
}.

Definition head (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h <+ t => h
  end.

Inductive tree : Set :=
| E
| T (l : tree) (v : nat) (r : tree).

Definition ex_tree : tree := T (T E 1 E) 2 (T E 3 E).
Compute ex_tree.
.

Fixpoint insert_element (x : nat) (t : tree) : tree :=
  match t with
  | E => T E x E
  | T l y r => if x <? y then T (insert_element x l) y r
                 else if y <? x then T l y (insert_element x r)
                      else T l x r
  end.

Compute insert_element 4 ex_tree.

Fixpoint insert_list (l : natlist) (t : tree) : tree :=
  match l with
  | nil => t
  | h <+ t' => insert_list t' (insert_element (head 0 l) t)
  end.


Inductive Dominio : Set :=
| s_natlist : natlist -> Dominio
| s_tree : tree -> Dominio


Definition concatD (l1 l2 : Dominio) : option Dominio :=
  match l1 with
  | s_natlist l1' => match l2 with
                     | s_natlist l2' => Some (s_natlist  (l1' ++ l2'))
                     | _ => None
                     end
  | _ => None
  end.



Definition insertD (l t: Dominio) : option Dominio :=
  match l with
  | s_natlist l' => match t with
                    | s_tree t' => Some ( s_tree (insert_list l' t'))
                    | _ => None
                    end
  | _ => None
  end.


Program Instance Monoid_H' :
  Monoid_H := {|
                M := Dominio;
                e := s_natlist [];
                op1 := concatD;
                op2 := insertD 
               |}.