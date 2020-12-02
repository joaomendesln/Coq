Theorem example: forall n k : nat,
  k = 0 -> k + n = n.
Proof.
  intros.
  rewrite H.
  (* contradiction. *)
  simpl.
  reflexivity.
Qed.