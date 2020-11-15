(*bool ::= true | false *)


Inductive bool: Type :=
  | true
  | false.

(* Cada linha iniciadaa com um simbolo de pipeline, '|', representa um construtor *)

(* 'true' e 'false' sao do tipo bool e sao as unicas expressoes construtoras que pertencem a tal tipo*)



(* com base nas tabela-verdades apresentadas no slide,
   podemos definir as seguintes operacoes sobre objetos
   do tipo bool *)

(* negb : bool -> bool *)
Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

(* andb : bool x bool -> bool *)
Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

(* orb : bool x bool -> bool *)
Definition orb (b1 : bool) (b2 : bool) : bool := 
  match b1 with
  | true => b2
  | false => false
  end.


Check orb.
(*O Coq utilizar o formato 'Curryficado' da assinatura de funcoes*)

(*Reconsiderar essa parte*)

Example test1: negb true = false.
Proof. simpl. reflexivity. Qed.

(* explicar o que sao o simpl e reflexivity *)

Example test2: andb true false = false.
Proof. simpl. reflexivity. Qed.

Example test3: andb true true = true.
Proof. reflexivity. Qed.

(* reflexivity > simpl *)

Theorem test4: andb true true = true. 

Proof. reflexivity. Qed.




(* Demonstre que negb eh um funcao involutiva*)

(* Para todo b do tipo bool, negb (negb b) = b*)

Theorem negb_involutive : forall (b : bool),
  negb (negb b) = b.
Proof.
  (*Seja b do tipo Bool*)
  intro b.
  
  destruct b eqn:E.

  (*Caso b = true*)
  - simpl. reflexivity.

  (*Caso b = false*)
  - simpl. reflexivity.
Qed. 


(*Definition orb' (b1 : bool) (b2 : bool) : bool := 
  match b1 with
  | true => b2
  | false => false
  end. USAR DEMORGAN PARA DEFINIR*)

(*demonstrar que orb e orb' sao equivalentes*)