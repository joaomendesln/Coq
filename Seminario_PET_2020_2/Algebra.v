From SP Require Export List.

(* ----------------------------------------- *)




(* Deifinição 4.1. (Monoid) *)

Class Monoid := {
  M : Set;
  e : M;
  op1 : M -> M -> M;
  op_assoc: forall x y z, op1 (op1 x y) z = op1 x (op1 y z);
  op1_id1: forall x, op1 x e = x;
  op1_id2: forall x, op1 e x = x;
}.




(* ----------------------------------------- *)




Section Monoid_Action.

(* Considere uma álgebra 'Mo' que satisfaça todas as equações de Monoid *)
Context {Mo: Monoid}.

(* Deifinição 4.2. (Monoid Action) *)
Class Monoid_Action := {
  S : Set;
  op2 : M -> S -> S;
  op_assoc_h: forall x y z, op2 (op1 x y) z = op2 x (op2 y z);
  op2_id1: forall x, op2 e x = x;
}.

End Monoid_Action.




(* ----------------------------------------- *)




Section Instance_Monoid_Action.
  Program Instance MApp : Monoid :=
    {|
      M := natlist;
      e := [];
      op1 := append
    |}.
  Next Obligation.
    (* Teorema 3.1. *)
    apply append_assoc.
  Qed.
  Next Obligation.
    (* Seja 'x' um elemento arbitrário de 'natlist'. *)
    intro x.

    (* Demonstremos por indução estrutural em 'x' que x ++ [] = x*)
    induction x as [| h t HI].

    (* [base: x := []] *)
    - (* [appendB] *)
      simpl.
      (* Reflexividade da '=' *)
      reflexivity.

    (* [passo indutivo] *)
    (* Seja 't' em 'listnat' tal que t ++ [] = t. *)
    (* Demonstremos que (h <+ t) ++ [] = (h <+ t). *)
    - (* [appendR] *)
      simpl.
      (* Hipótese de Indução *)
      rewrite HI.
      (* Reflexividade da '=' *)
      reflexivity.
  Qed.
  Next Obligation.
    (* Seja 'x' um elemento arbitrário de 'natlist'. *)
    intro x.
    (* [appendB] *)
    simpl. 
    (* Reflexividade da '=' *)
    reflexivity.
  Qed.



  Program Instance MApp_Action : Monoid_Action :=
    {|
      S := nat;
      op2 := head
    |}.
  Next Obligation.
    (* Teorema 3.3. *)
    apply head_append_assoc.
  Qed.
  Next Obligation.
    (* Seja 'x' um elemento arbitrário de 'natlist'. *)
    intro x.
    (* [head1] *)
    simpl.
    (* Reflexividade da '=' *)
    reflexivity. 
  Qed.
End Instance_Monoid_Action.