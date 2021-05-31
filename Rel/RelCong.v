Add LoadPath "C:\Users\Hp\Documents\CoqGit\Rel" as CoqRelDir.

Load RelEuclDiv.

Definition CongMod (k : rel) (x y : rel) : Prop :=
  ( ∃ q : rel, x == q*k + y ).

Notation "x ≡ y [ k ]" := (CongMod k x y) (at level 70).

Instance refl_CongMod (k : rel) : Symmetric (CongMod k).
Proof.
  move => x y.
  case => q => Ck_xy.
  unfold "_ ≡ _ [ _ ]".
  exists (-q). ring [Ck_xy].
Qed.