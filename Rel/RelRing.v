Add LoadPath "C:\Users\Hp\Documents\CoqGit\Rel" as CoqRelDir.

Load RelReflect.

(** On définit sur rel une structure d'anneau *)
Definition rel_ring_th : @ring_theory 
  (rel : Type) (* R *)
  (O_Z : rel) (* r0 *)
  (One : rel) (* rI *)
  (rel_plus : rel -> rel -> rel) (* radd *)
  (rel_prod : rel -> rel -> rel) (* rmul *)
  (rel_sub : rel -> rel -> rel) (* rsub *)
  (rel_minus : rel -> rel) (* ropp *)
  (rel_eq : rel -> rel -> Prop) (* req *)
.
Proof.
  apply mk_rt.
  
  + move => [x_0 x_1].
    unfold rel_plus, O_Z, rel_eq.
    simpl. apply PeanoNat.Nat.add_comm.

  + move => [x_0 x_1] [y_0 y_1].
    unfold rel_plus, rel_eq. lia.

  + move => [x_0 x_1] [y_0 y_1] [z_0 z_1].
    unfold rel_plus, rel_eq. lia.

  + move => [x_0 x_1].
    unfold One, rel_prod, rel_eq.
    simpl. lia.
  
  + move => [x_0 x_1] [y_0 y_1].
    unfold rel_prod, rel_eq. lia.

  + move => [x_0 x_1] [y_0 y_1] [z_0 z_1].
    unfold rel_prod, rel_eq. lia.
  
  + move => [x_0 x_1] [y_0 y_1] [z_0 z_1].
    unfold rel_prod, rel_plus, rel_eq. lia.
    
  + move => [x_0 x_1] [y_0 y_1].
    unfold rel_sub, rel_minus, rel_plus, rel_eq. lia.

  + move => [x_0 x_1].
    unfold rel_minus, rel_plus, O_Z, rel_eq.
    do 2 rewrite PeanoNat.Nat.add_0_r.
    apply PeanoNat.Nat.add_comm.
Qed.

Add Ring RelRing : rel_ring_th
  (decidable rel_eq_dec).

Example test_ring_tactic : forall x y z : rel,
  (x * (y - z) + z * x) == One * y * x + O_Z.
Proof. move => x y z. ring. Qed.