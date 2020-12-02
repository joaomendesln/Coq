(*bool ::= true | false *)


Inductive bool: Set :=
  | true
  | false.

(* Cada linha iniciada com um simbolo de pipeline, '|', representa um construtor; *)
(* 'true' e 'false' sao do tipo 'bool' e são as únicas expressões construtoras que pertencem a tal conjunto. *)




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

Compute negb true.
Compute negb false.




(* ----------------------------------------- *)




(* Deifinição 1.2. (andb) *)

(* andb : bool X bool -> bool *)

(* |--------------------------------| *)
(* |   b1  |   b2  | andb (b1, b2)  | *)
(* |--------------------------------| *)
(* | false | false |     false      | *)
(* | false |  true |     false      | *)
(* |  true | false |     false      | *)
(* |  true |  true |      true      | *)
(* |--------------------------------| *)

Definition andb (b1 b2 : bool) : bool :=
  match b1, b2 with
  | false, false => false
  | false, true => false
  | true, false => false
  | true, true => true
  end.


Check andb.
(*O Coq utiliza o formato 'Curryficado' da assinatura de funções*)

Compute andb true false.

Compute andb true true.




(* ----------------------------------------- *)




(* Deifinição 1.3. (orb) *)

(* orb : bool X bool -> bool *)

(* |--------------------------------| *)
(* |   b1  |   b2  |  orb (b1, b2)  | *)
(* |--------------------------------| *)
(* | false | false |     false      | *)
(* | false |  true |      true      | *)
(* |  true | false |      true      | *)
(* |  true |  true |      true      | *)
(* |--------------------------------| *)


Definition orb (b1 b2 : bool) : bool := 
  match b1, b2 with
  | false, false => false
  | false, true => true
  | true, false => true
  | true, true => true
  end.

Compute orb false false.
Compute orb false true.




(* ----------------------------------------- *)




(* Teorema 1.1. Demonstre que negb é um função involutiva, ou seja, que, para todo 'b' em 'bool', negb (negb b) = b*)
Theorem negb_involutive : forall (b : bool),
  negb (negb b) = b.
Proof.

  (*Seja 'b' em 'bool'.*)
  intro b.
  
  destruct b eqn:E.

  (*Caso b := true*)
  - (* Pela definição de 'negb', temos que ...*)
    simpl.
    (* o que escrever aqui? *) 
    reflexivity.

  (*Caso b := false*)
  - 
    simpl. 
    
    reflexivity.

Qed.




(* ----------------------------------------- *)




(* Recordemos a tabela de 'orb' *)

(* |--------------------------------| *)
(* |   b1  |   b2  |  orb (b1, b2)  | *)
(* |--------------------------------| *)
(* | false | false |     false      | *)
(* | false |  true |      true      | *)
(* |  true | false |      true      | *)
(* |  true |  true |      true      | *)
(* |--------------------------------| *)



(* Deifinição 1.4. (orb_simpb) *)

(* orb_simpb : bool X bool -> bool *)

Definition or_simpb (b1 b2 : bool) : bool :=  
  match b1 with
  | true => true
  | false => b2
  end.


(* Teorema 1.3. Demonstre que as funções 'orb' e 'or_simpb' são iguais.*)

Check orb.
Check or_simpb.

(* Para isso, verifiquemos que, para 'b1' e 'b2' arbitrários em 'bool', orb (b1, b2) = or_simpb (b1, b2). *)
Theorem orb_orb_simpb_equiv : forall (b1 b2 : bool),
  orb b1 b2 = or_simpb b1 b2.
Proof.

  (*Seja 'b1' e 'b2' em 'bool'.*)
  intros b1 b2.

  destruct b1 eqn:E1.

  (* Caso b1 := true *)
  - destruct b2 eqn:E2.

    (* Caso b2 := true *)
    + 
      simpl.

      reflexivity.

    (* Caso b2 := false *)
    + 
      simpl.

      reflexivity.

  (* Caso b1 := false *)
  - destruct b2 eqn:E2.

    (* Caso b2 := true *)
    +
      simpl. 

      reflexivity.
    (* Caso b2 := false *)
    + 
      simpl.

      reflexivity.
Qed.