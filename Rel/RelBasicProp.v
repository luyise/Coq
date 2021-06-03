Add LoadPath "C:\Users\Hp\Documents\CoqGit\Rel" as CoqRelDir.

Load RelRing.

Lemma rel_plus_minus {x : rel} : (x + ( - x ) == O_Z).
Proof.
  ring.
Qed.

Lemma rel_plusC {x y : rel} : (x + y == y + x).
Proof.
  ring.
Qed.

Lemma rel_minusminus {x : rel} : - - x == x.
Proof.
  ring.
Qed.

Proposition rel_minus_plus {x : rel} : ((- x) + x == O_Z).
Proof.
  ring.
Qed.

Proposition rel_eq_lele {x y : rel} : (x <= y) /\ (y <= x) <-> x == y.
Proof.
  case x as [x_0 x_1], y as [y_0 y_1].
  split.
  + move => [Lexy Leyx].
    unfold rel_le, rel_eq in *.
    lia.
  + move => Eqxy.
    split; unfold rel_le, rel_eq in *; lia.
Qed.

Proposition relspos_prod : ∀ x y : rel, O_Z < x -> O_Z < y -> O_Z < x * y.
Proof.
  move => [x_0 x_1] [y_0 y_1].
  unfold "<", O_Z, "*". simpl.
  nia.
Qed.

Proposition rel_spos_sneg_prod : ∀ x y : rel, x < O_Z -> O_Z < y -> x * y <= - y.
Proof.
  move => [x_0 x_1] [y_0 y_1].
  unfold "<", O_Z, "*". simpl.
  nia.
Qed.

Proposition rel_lelt_lt : ∀ x y z : rel, x <= y -> y < z -> x < z.
Proof.
  move => [x_0 x_1] [y_0 y_1] [z_0 z_1].
  unfold "<=", "<"; lia.
Qed.
