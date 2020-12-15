(* bool ::= true | false *)


Inductive bool: Set :=
  | true
  | false
.

(* Cada linha iniciada com um símbolo de pipeline, '|', representa um construtor; *)
(* 'true' e 'false' são do tipo 'bool' e são as únicas expressões construtoras que pertencem a tal conjunto. *)




(* ----------------------------------------- *)




(* Deifinição 1.1. (negb) *)

(* negb : bool -> bool *)

(* |-------------------| *)
(* |   b   | negb (b)  | *)
(* |-------------------| *)
(* | false |    true   | *)
(* |  true |   false   | *)
(* |-------------------| *)

Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.




(* Teorema 1.1. Demonstre que negb é um função involutiva, ou seja, que, para todo 'b' em 'bool', negb (negb (b)) = b*)
Theorem negb_involutive : forall (b : bool),
  negb (negb b) = b.
Proof.

  (*Seja 'b' em 'bool'.*)
  intro b.
  
  destruct b eqn:E.

  (*Caso b := true*)
  - (* Pela definição de 'negb', temos que negb (negb (true)) = true. *)
    simpl.
    (* Reflexividade da '=' *) 
    reflexivity.

  (*Caso b := false*)
  - (* Pela definição de 'negb', temos que negb (negb (false)) = false. *)
    simpl. 
    (* Reflexividade da '=' *)
    reflexivity.

Qed.