Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Coq Require Import
     Morphisms
     Setoid
     Ring
     RelationClasses
     Lia
     ssreflect
     ssrbool
     ssrsearch
     Utf8
.

Inductive rel :=
  | Zpair : nat -> nat -> rel.

Definition O_Z := Zpair 0 0.
Definition One := Zpair 1 0.
Definition Two := Zpair 2 0.
Definition Three := Zpair 3 0.
Definition Four := Zpair 4 0.

Definition rel_eq (x y : rel) : Prop :=
  match (x, y) return Prop with (Zpair a b, Zpair c d) =>
      a + d = b + c
  end.

Notation "x == y" := (rel_eq x y) (at level 70).
Notation "x '=/=' y" := (not (rel_eq x y)) (at level 0).

Instance refl_rel_eq : Reflexive rel_eq.
Proof.
  unfold Reflexive.
  intros [x_0 x_1].
  unfold rel_eq.
  lia.
Qed.

Instance sym_rel_eq : Symmetric rel_eq.
Proof.
  unfold Symmetric.
  intros [x_0 x_1] [y_0 y_1]; unfold rel_eq.
  lia.
Qed.

Instance trans_rel_eq : Transitive rel_eq. 
Proof.
  unfold Transitive.
  intros [x_0 x_1] [y_0 y_1] [z_0 z_1].
  unfold rel_eq. 
  lia.
Qed.

Instance equiv_rel_eq : Equivalence rel_eq.
Proof.
  constructor.
  exact refl_rel_eq.
  exact sym_rel_eq.
  exact trans_rel_eq.
Qed.

Definition rel_plus (x y : rel) :=
  match (x, y) return rel with (Zpair a b, Zpair c d) =>
    Zpair (a + c) (b + d)
  end.

Notation "x + y" := (rel_plus x y).

Instance rel_plusProper : Proper (rel_eq ==> rel_eq ==> rel_eq) rel_plus.
Proof.
  move => [x_0 x_1] [x_0' x_1'] Eqxx' [y_0 y_1] [y_0' y_1'] Eqyy'.
  unfold rel_plus, rel_eq in * |- *.
  lia.
Qed.

Definition rel_minus (x : rel) :=
  match x return rel with (Zpair a b) =>
    Zpair b a
  end.

Notation "- x" := (rel_minus x).

Instance rel_minusProper : Proper (rel_eq ==> rel_eq) rel_minus.
Proof.
  move => [x_0 x_1] [x_0' x_1'] Eqxx'.
  unfold rel_minus, rel_eq in * |- *.
  lia.
Qed.

Definition rel_prod (x y : rel) :=
  match x, y return rel with (Zpair a b), (Zpair c d) =>
    Zpair (a*c + b*d) (b*c + a*d)
  end.

Notation "x * y" := (rel_prod x y).

Instance rel_prodProper : Proper (rel_eq ==> rel_eq ==> rel_eq) rel_prod.
Proof.
  move => [x_0 x_1] [x_0' x_1'] Eqxx' [y_0 y_1] [y_0' y_1'] Eqyy'.
  unfold rel_prod, rel_eq in * |- *.
  lia.
Qed.

Definition rel_le (x y : rel) :=
  match x, y return Prop with (Zpair a b), (Zpair c d) =>
    a + d <= c + b
  end.

Definition rel_lt (x y : rel) :=
  match x, y return Prop with (Zpair a b), (Zpair c d) =>
    a + d < c + b
  end.

Notation "x >= y" := (rel_le y x) (only parsing).
Notation "x > y" := (rel_lt y x) (only parsing).
Notation "x <= y" := (rel_le x y).
Notation "x < y" := (rel_lt x y).

Instance refl_rel_le : Reflexive rel_le.
Proof.
  move => [x_0 x_1].
  unfold rel_le.
  reflexivity.
Qed.

Instance trans_rel_le : Transitive rel_le.
Proof.
  move => [x_0 x_1] [y_0 y_1] [z_0 z_1].
  unfold rel_le.
  lia.
Qed.

Instance trans_rel_lt : Transitive rel_lt.
Proof.
  move => [x_0 x_1] [y_0 y_1] [z_0 z_1].
  unfold rel_lt.
  lia.
Qed.

Instance rel_leProper_eq : Proper (rel_eq ==> rel_eq ==> iff) rel_le.
Proof.
  move => [x_0 x_1] [x_0' x_1'] Eqxx' [y_0 y_1] [y_0' y_1'] Eqyy'.
  unfold rel_le, rel_eq in * |- *.
  lia.
Qed.

Instance rel_leProper_lt : Proper (rel_eq ==> rel_eq ==> iff) rel_lt.
Proof.
  move => [x_0 x_1] [x_0' x_1'] Eqxx' [y_0 y_1] [y_0' y_1'] Eqyy'.
  unfold rel_lt, rel_eq in * |- *.
  lia.
Qed.

Instance rel_plusProper_le : Proper (rel_le ==> rel_le ==> rel_le) rel_plus.
Proof.
  move => [x_0 x_1] [x_0' x_1'] Lexx' [y_0 y_1] [y_0' y_1'] Leyy'.
  unfold rel_le, rel_plus, rel_eq in * |- *.
  lia.
Qed.

Instance rel_plusProper_lelt : Proper (rel_le ==> rel_lt ==> rel_lt) rel_plus.
Proof.
  move => [x_0 x_1] [x_0' x_1'] Lexx' [y_0 y_1] [y_0' y_1'] Ltyy'.
  unfold rel_le, rel_lt, rel_plus, rel_eq in * |- *.
  lia.
Qed.

Instance rel_plusProper_ltle : Proper (rel_lt ==> rel_le ==> rel_lt) rel_plus.
Proof.
  move => [x_0 x_1] [x_0' x_1'] Ltxx' [y_0 y_1] [y_0' y_1'] Leyy'.
  unfold rel_le, rel_lt, rel_plus, rel_eq in * |- *.
  lia.
Qed.

Instance rel_plusProper_lt : Proper (rel_lt ==> rel_lt ==> rel_lt) rel_plus.
Proof.
  move => [x_0 x_1] [x_0' x_1'] Ltxx' [y_0 y_1] [y_0' y_1'] Ltyy'.
  unfold rel_le, rel_lt, rel_plus, rel_eq in * |- *.
  lia.
Qed.

Instance rel_minusProper_le : Proper (rel_le --> rel_le) rel_minus.
Proof.
  move => [x_0 x_1] [x_0' x_1'] Lexx'.
  unfold rel_minus, rel_le, Basics.flip in *.
  lia.
Qed.

Instance rel_minusProper_lt : Proper (rel_lt --> rel_lt) rel_minus.
Proof.
  move => [x_0 x_1] [x_0' x_1'] Lexx'.
  unfold rel_minus, rel_lt, Basics.flip in *.
  lia.
Qed.

Definition rel_sub (x y : rel) := x + (-y).
Notation "x - y" := (rel_sub x y).