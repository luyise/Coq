Add LoadPath "C:\Users\Hp\Documents\CoqGit\Rel" as CoqRelDir.

Load RelDef.

Definition rel_eqb (x y : rel) : bool :=
  match (x, y) return bool with (Zpair a b, Zpair c d) =>
    Nat.eqb (a + d) (b + c)
  end.

Notation "x ==? y" := (rel_eqb x y) (at level 69).

Lemma nat_eqP {x y : nat} : reflect (x = y) (Nat.eqb x y).
Proof.
  apply: (iffP idP).
  move: x y; induction x; induction y => //=; auto.
  move => ->; move: y; induction y => //.
Qed.

Lemma rel_eqP {x y : rel} : reflect (x == y) (x ==? y).
Proof.
  case x as [x_0 x_1], y as [y_0 y_1].
  apply: (iffP idP).
  + move => Eqb.
    unfold rel_eqb, rel_eq in *.
    apply /nat_eqP => //.
  + move => Eq.
    unfold rel_eqb, rel_eq in *.
    apply /nat_eqP => //.
Qed.

Notation "x '=/=?' y" := (not (rel_eqb x y)) (at level 68).

Definition rel_leb (x y : rel) : bool :=
  match x, y return bool with (Zpair a b), (Zpair c d) =>
    Nat.leb (a + d) (c + b)
  end.

Definition rel_ltb (x y : rel) : bool :=
  match x, y return bool with (Zpair a b), (Zpair c d) =>
    Nat.ltb (a + d) (c + b)
  end.

Notation "x '>=?' y" := (rel_leb y x) (at level 70, only parsing).
Notation "x '>?' y" := (rel_ltb y x) (at level 70, only parsing).
Notation "x '<=?' y" := (rel_leb x y) (at level 70).
Notation "x '<?' y" := (rel_ltb x y) (at level 70).

Lemma nat_leP {x y : nat} : reflect (le x y) (Nat.leb x y).
Proof.
  apply (iffP idP).
  apply PeanoNat.Nat.leb_le.
  apply PeanoNat.Nat.leb_le.
Qed.

Lemma rel_leP {x y : rel} : reflect (x <= y) (x <=? y).
Proof.
  case x as [x_0 x_1], y as [y_0 y_1].
  apply (iffP idP).
  all : unfold rel_leb, rel_le.
  move => /nat_leP => //.
  move => Le.
  apply /nat_leP => //.
Qed.

Lemma nat_ltP {x y : nat} : reflect (lt x y) (Nat.ltb x y).
Proof.
  apply (iffP idP).
  apply PeanoNat.Nat.ltb_lt.
  apply PeanoNat.Nat.ltb_lt.
Qed.

Lemma rel_ltP {x y : rel} : reflect (x < y) (x <? y).
Proof.
  case x as [x_0 x_1], y as [y_0 y_1].
  apply (iffP idP).
  all : unfold rel_ltb, rel_lt.
  move => /nat_ltP => //.
  move => Lt.
  apply /nat_ltP => //.
Qed.