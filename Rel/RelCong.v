Add LoadPath "C:\Users\Hp\Documents\CoqGit\Rel" as CoqRelDir.

Load RelEuclDiv.

Definition CongMod (k : rel) (x y : rel) : Prop :=
  ( ∃ q : rel, x == q*k + y ).

Notation "x ≡ y 'mod' k" := (CongMod k x y) (at level 50).

Instance sym_CongMod (k : rel) : Symmetric (CongMod k).
Proof.
  move => x y.
  case => q => Ck_xy.
  unfold "_ ≡ _ 'mod' _".
  exists (-q). ring [Ck_xy].
Qed.

Instance refl_CongMod (k : rel) : Reflexive (CongMod k).
Proof.
  move => x.
  exists O_Z. ring.
Qed.

Instance trans_CongMod (k : rel) : Transitive (CongMod k).
Proof.
  move => x y z.
  case => q_xy Ck_xy.
  case => q_yz Ck_yz.
  exists (q_xy + q_yz).
  ring [Ck_xy Ck_yz].
Qed.

Instance equiv_CongMod (k : rel) : Equivalence (CongMod k).
Proof.
  split.
  apply refl_CongMod.
  apply sym_CongMod.
  apply trans_CongMod.
Qed.

Instance CongMod_Proper (k : rel) : Proper (rel_eq ==> rel_eq ==> iff) (CongMod k).
Proof.
  move => x x' Eqxx' y y' Eqyy'.
  unfold "_ ≡ _ mod _ ".
  split.
    case => q H. exists q. 
    setoid_rewrite <-Eqxx'.
    setoid_rewrite <-Eqyy'.
    assumption.
    case => q H. exists q. 
    setoid_rewrite Eqxx'.
    setoid_rewrite Eqyy'.
    assumption.
Qed.

Example test_CongMod_Propper : forall k x y z t : rel,
  (x == y) -> (y == z) -> (z == t) -> ( x ≡ t mod k ) .
Proof.
  move => k x y z t.
  move => -> -> ->.
  reflexivity.
Qed.

(*
Lemma iggsrghio : forall y M : rel, M =/= O_Z -> O_Z <= y -> y < M -> O_Z ≡ y mod M -> O_Z == y.
Proof.
  move => y M MnotO y_pos y_infM.
  unfold CongMod.
  intro congr; inversion congr; clear congr.
  suff : x == O_Z.
  intro x_null; setoid_rewrite x_null in H.
  ring_simplify in H; fold O_Z in H.
  assumption.
  assert (-y == x * M).
  ring [H].
  *)
