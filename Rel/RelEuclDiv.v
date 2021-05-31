Add LoadPath "C:\Users\Hp\Documents\CoqGit\Rel" as CoqRelDir.

Load RelPosWF.

Lemma rel_minusneqO_Z {y : rel} : y =/= O_Z -> (- y) =/= O_Z.
Proof.
  case y as [y_0 y_1].
  unfold O_Z, rel_minus, rel_eq.
  lia.
Qed.

Lemma rel_le_minus_leO {x y : rel} : (x >= y) -> ((x + (- y)) >= O_Z).
Proof.
  case x as [x_0 x_1], y as [y_0 y_1].
  unfold O_Z, rel_minus, rel_plus, rel_le.
  lia.
Qed.

Definition relpos_typediv_by (y : rel) (x : rel) := (x >= O_Z) ->
  { div : rel * rel | let (q, r) := div in ( ( q * y + r == x ) /\ ( O_Z <= r) /\ ( r < y ) )}.

Definition ind_relpos_div_by (y : rel) (pi_y : y > O_Z) : 
  ∀ x, (∀ x', relpos_lt x' x -> relpos_typediv_by y x') -> relpos_typediv_by y x.
Proof.
  rename y into z.
  move => x.
  move => IHx.
  case_eq (x <? z).
  + move => /rel_ltP => Hxz Hx.
    assert (O_Z * z + x == x ∧ O_Z <= x ∧ x < z) as Goal.
      case x as [x_0 x_1],  z as [y_0 y_1].
      unfold relpos_lt, rel_minus, rel_plus, O_Z, rel_le, rel_lt, rel_prod, rel_eq.
      unfold O_Z, rel_lt, rel_le in pi_y, Hxz, Hx. lia.
    assert (let (q, r) := (O_Z, x) in q * z + r == x ∧ O_Z <= r ∧ r < z) by assumption.
    exact (exist _ (O_Z, x) H).
  + move => /rel_ltP => Hxz HxPos.
    assert (relpos_lt (x + (- z)) x) as Hx.
      case x as [x_0 x_1], z as [y_0 y_1].
      unfold relpos_lt, rel_minus, rel_plus, O_Z, rel_le, rel_lt.
      unfold O_Z, rel_lt in pi_y, Hxz, HxPos.
      lia.
    assert (O_Z <= (x + (- z))) as HPos.
      case x as [x_0 x_1], z as [y_0 y_1].
      unfold relpos_lt, rel_minus, rel_plus, O_Z, rel_le, rel_lt.
      unfold O_Z, rel_lt in pi_y, Hxz, HxPos.
      lia.
    pose div_aux := ((IHx (x + (- z)) Hx) HPos); clearbody div_aux.
    case div_aux as [x0 H] eqn: Eq.
    case x0 as [q r].
    assert ((q + One) * z + r == x ∧ O_Z <= r ∧ r < z) as Goal.
      case x as [x_0 x_1], z as [y_0 y_1], q as [q_0 q_1], r as [r_0 r_1].
      unfold relpos_lt, rel_minus, rel_plus, O_Z, One, rel_prod, rel_le, rel_lt, rel_eq.
      unfold relpos_lt, rel_minus, rel_plus, O_Z, One, rel_prod, rel_le, rel_lt, rel_eq in pi_y, Hxz, HxPos, H.
      lia.
    assert (let (q0, r0) := (q + One, r) in q0 * z + r0 == x ∧ O_Z <= r0 ∧ r0 < z) as FinalGoal by assumption.
    exact (exist _ (q + One, r) FinalGoal).
Qed.

Definition relpos_eucldiv (x y : rel) (pi_x : x >= O_Z) (pi_y : y > O_Z) : { div : rel * rel | let (q, r) := div in ( ( q * y + r == x ) /\ ( O_Z <= r) /\ ( r < y ) )}.
  pose R := relpos_lt.
  exact ( (@Fix rel R wf_relpos_lt (fun (x : rel) => (relpos_typediv_by y x)) (@ind_relpos_div_by y pi_y)) x pi_x).
Qed.

Lemma le_0_183 : O_Z <= rel_of_nat (183).
Proof.
  unfold O_Z, rel_of_nat, rel_le; lia.
Qed.
Lemma lt_0_22 : O_Z < rel_of_nat (22).
Proof.
  unfold O_Z, rel_of_nat, rel_lt; lia.
Qed.

Definition witness {A : Type} {P : A -> Prop} (S : @sig A P) : A.
  case S => x _.
  exact x.
Defined.

Proposition relpos_eucldiv_correct :
  forall x y : rel, forall pi_x : (x >= O_Z), forall pi_y : (y > O_Z),
    let (q, r) := witness (relpos_eucldiv pi_x pi_y) in q * y + r == x.
Proof.
  pose R := relpos_lt => x y pi_x pi_y.
  case (relpos_eucldiv pi_x pi_y).
  unfold witness. move => [q r].
  case => Goal _ => //.
Qed.

(** definition de la division euclidienne globale sur rel *)

Definition rel_abs (x : rel) :=
  if (x <? O_Z) is true then (- x)
  else x.

Notation "| x |" := (rel_abs x) (at level 100).

Lemma relspos_abs : forall x : rel, O_Z < x -> | x | == x.
Proof.
  move => x Hx.
  unfold rel_abs.
  assert ((x <? O_Z) = false) as Eq.
  apply /rel_ltP.
  case x as [x_0 x_1].
  unfold rel_lt, O_Z in *. lia.
  rewrite Eq. reflexivity.
Qed.

Lemma relsneg_abs : forall x : rel, (not (O_Z < x)) /\ (x =/= O_Z) -> | x | == - x.
Proof.
  move => x Hx.
  unfold rel_abs.
  assert ((x <? O_Z) = true) as Eq.
  apply /rel_ltP.
  case x as [x_0 x_1].
  unfold rel_lt, rel_eq, O_Z in *. lia.
  rewrite Eq. reflexivity.
Qed.

Definition rel_eucldiv_aux (x y : rel) (pi : y =/= O_Z) : { div : (rel * rel) | let (q, r) := div in ( ( q * y + r == x ) /\ ( O_Z <= r) /\ ( r < |y| ) )}.
  case (O_Z <? y) eqn: pi_y.
  move : pi_y=>/rel_ltP=>pi_y.
  + case (O_Z <=? x) eqn: pi_x.
    - move : pi_x=>/rel_leP=>pi_x.
      pose H := (relspos_abs pi_y); clearbody H.
      pose div_aux := ( (@relpos_eucldiv x y pi_x pi_y) ).
      case div_aux as [[q r] div_c].
      rewrite <-H in div_c at 2.
      exact (exist _ (q, r) div_c ).
    - move : pi_x=>/rel_leP=>Hx.
      assert (O_Z <= - x) as pi_x.
      case x as [x_0 x_1].
      unfold O_Z, rel_minus, rel_le.
      unfold O_Z, rel_le in Hx. lia.
      pose div_aux := ( (@relpos_eucldiv (-x) y pi_x pi_y) ).
      case div_aux as [[q r] [div_c0 [div_c1 div_c2]]].
      case (r ==? O_Z) eqn: Hr.
      * move: Hr=>/rel_eqP=>Hr.
        setoid_rewrite Hr in div_c0.
        assert (let (q0, r0) := (-q, O_Z) in q0 * y + r0 == x ∧ O_Z <= r0 ∧ r0 < |y|) as Goal.
        rewrite (relspos_abs). 2 : assumption.
        case x as [x_0 x_1], y as [y_0 y_1], q as [q_0 q_1], r as [r_0 r_1].
        unfold O_Z, rel_prod, rel_minus, rel_plus, rel_abs, rel_le, rel_lt, rel_eq in *.
        lia.
        exact (exist _ (-q, O_Z) Goal).
      * move: Hr=>/rel_eqP=>Hr.
        assert (let (q0, r0) := ((-q)+(-One), y + (-r)) in q0 * y + r0 == x ∧ O_Z <= r0 ∧ r0 < |y|) as Goal.
        rewrite (relspos_abs). 2 : assumption.
        case x as [x_0 x_1], y as [y_0 y_1], q as [q_0 q_1], r as [r_0 r_1].
        unfold O_Z, One, rel_prod, rel_minus, rel_plus, rel_le, rel_lt, rel_eq in *.
        lia.
        exact (exist _ (((-q) + ( - One )), ( y + ( - r ))) Goal).

  + move: pi_y=>/rel_ltP=>Hy.
    assert (O_Z < - y) as pi_y.
    case y as [y_0 y_1].
    unfold O_Z, rel_minus, rel_eq, rel_lt.
    unfold O_Z, rel_lt, rel_eq in Hy, pi. lia.

    case (O_Z <=? x) eqn: pi_x.
    - move: pi_x=>/rel_leP=>pi_x.
      pose div_aux := (@relpos_eucldiv x (-y) pi_x pi_y).
      case div_aux as [[q r] [div_c0 [div_c1 dv_c2]]].
      assert (let (q0, r0) := (-q, r) in q0 * y + r0 == x ∧ O_Z <= r0 ∧ r0 < |y|) as Goal.
      rewrite (relsneg_abs). 2 : split; assumption.
      case x as [x_0 x_1], y as [y_0 y_1], q as [q_0 q_1], r as [r_0 r_1].
      unfold O_Z, rel_prod, rel_minus, rel_plus, rel_le, rel_lt, rel_eq in *.
      lia.
      exact (exist _ (-q, r) Goal).
    - move: pi_x=>/rel_leP=>Hx.
      assert (O_Z <= -x) as pi_x.
      case x as [x_0 x_1].
      unfold O_Z, rel_minus, rel_le.
      unfold O_Z, rel_le in Hx. lia.
      pose div_aux := ( (@relpos_eucldiv (-x) (-y) pi_x pi_y) ).
      case div_aux as [[q r] [div_c0 [div_c1 div_c2]]].
      case (r ==? O_Z) eqn: Hr.
      * move: Hr=>/rel_eqP=>Hr.
        setoid_rewrite Hr in div_c0.
        assert (let (q0, r0) := (q, O_Z) in q0 * y + r0 == x ∧ O_Z <= r0 ∧ r0 < |y|) as Goal.
        rewrite (relsneg_abs). 2 : split; assumption.
        case x as [x_0 x_1], y as [y_0 y_1], q as [q_0 q_1], r as [r_0 r_1].
        unfold O_Z, rel_prod, rel_minus, rel_plus, rel_abs, rel_le, rel_lt, rel_eq in *.
        lia.
        exact (exist _ (q, O_Z) Goal).
      * move: Hr=>/rel_eqP=>Hr.
        assert (let (q0, r0) := (q+One, (-y) + (-r)) in q0 * y + r0 == x ∧ O_Z <= r0 ∧ r0 < |y|) as Goal.
        rewrite (relsneg_abs). 2 : split; assumption.
        case x as [x_0 x_1], y as [y_0 y_1], q as [q_0 q_1], r as [r_0 r_1].
        unfold O_Z, One, rel_prod, rel_minus, rel_plus, rel_le, rel_lt, rel_eq in *.
        lia.
        exact (exist _ (q+One, (-y) + (-r)) Goal).
Qed.

Definition rel_eucldiv (x y : rel) (pi : y =/= O_Z) := witness (rel_eucldiv_aux x pi).

(** Final theorem of this section *)

Theorem rel_eucldiv_ex : forall x y : rel, (y =/= O_Z) ->
  ∃ div : rel * rel, let (q, r) := div in
  ( ( q * y + r == x ) /\ ( O_Z <= r) /\ ( r < |y| ) ).
Proof.
  move => x y pi_y.
  pose div := rel_eucldiv_aux x pi_y.
  case: div.
  move => [q r] Goal.
  exists (q, r).
  assumption.
Qed.