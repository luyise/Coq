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