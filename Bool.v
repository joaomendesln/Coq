Inductive bool: Type :=
  | true
  | false.

(* Cada linha representa um construtor *)

(* 'true' e 'false' pertencem ao conjunto (ou tipo?)
   bool e sao as unicas expressoes construtoras que pertencem a tal conjunto*)

(* em breve, veremos conjuntos que têm, em seu conjunto de expressoes construtoras,
   construtores formados pela aplicacao de outro(s) construtore(s) *)


(* com base nas tabela-verdades apresentadas no slide,
   podemos definir as seguintes operacoes sobre objetos
   do tipo bool *)

Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

(* orb : bool -> bool -> bool *)
Definition orb (b1 : bool) (b2 : bool) : bool := 
  match b1 with
  | true => b2
  | false => false
  end.

Check orb.


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


(*RETIRAR*)

Definition impliesb (b1 : bool) (b2 : bool) : bool :=
  if (orb b1 (negb b2)) then false else true. (*reescrever: pode definir um operador derivado de outros*)

Example test5: ifthenb true false = false.
Proof. simpl. reflexivity. Qed. (* com o ifthenelse, nao eh possivel fazer simplificacoes *)

(*RETIRAR*)

(* um teorema usando destruct para finalizar *)

Theorem negb_involutive : forall (b : bool),
  negb (negb b) = b.
Proof.
  intro b. destruct b eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed. 


(*Definition orb' (b1 : bool) (b2 : bool) : bool := 
  match b1 with
  | true => b2
  | false => false
  end. USAR DEMORGAN PARA DEFINIR*)


(*demonstrar que orb e orb' sao equivalentes*)


