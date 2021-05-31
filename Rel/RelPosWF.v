Add LoadPath "C:\Users\Hp\Documents\CoqGit\Rel" as CoqRelDir.

Load RelBasicProp.

Definition relpos_le (x y : rel) :=
  (O_Z <= x) /\ (x <= y).

Definition relpos_lt (x y : rel) :=
  (O_Z <= x) /\ (x < y).

Instance trans_relpos_le : Transitive relpos_le.
Proof.
  move => [x_0 x_1] [y_0 y_1] [z_0 z_1].
  unfold relpos_le, O_Z, rel_le.
  lia.
Qed.

Instance trans_relpos_lt : Transitive relpos_lt.
Proof.
  move => [x_0 x_1] [y_0 y_1] [z_0 z_1].
  unfold relpos_lt, O_Z, rel_le, rel_lt.
  lia.
Qed.

Definition nat_of_rel (x : rel) := match x with Zpair a b => a-b end.
Definition rel_of_nat (n : nat) := Zpair n 0.
Lemma rel_of_nat_of_relpos {x : rel} : (x >= O_Z) -> rel_of_nat (nat_of_rel x) == x.
Proof.
  case x as [x_0 x_1].
  unfold O_Z, rel_le => /= => H.
  unfold rel_of_nat, rel_eq.
  lia.
Qed.

Lemma relpos_lt_natlt {x y : rel} : relpos_lt x y <-> lt (nat_of_rel x) (nat_of_rel y) /\ x >= O_Z /\ y >= O_Z.
Proof.
  case x as [x_0 x_1], y as [y_0 y_1]; unfold relpos_lt, nat_of_rel, O_Z, rel_le, rel_lt => /=; split.
  + case => Le_0 Le_1; repeat split; lia.
  + case => Le_0; case => Le_1 Le_2. lia.
Qed.

Lemma well_founded_equiv {A : Type} {R : A -> A -> Prop} {S : A -> A -> Prop}:
  (forall x y : A, (R x y <-> S x y)) -> well_founded R -> well_founded S.
Proof.
  move => HRS.
  unfold well_founded.
  move => H a; pose Ha := H a.
  move : Ha. move : a.
  apply: Acc_ind.
  move => a HRAcc HRSAcc.
  constructor => b.
  move => /HRS.
  apply HRSAcc.
Qed.

Lemma wf_lt : well_founded lt.
Proof.
  unfold well_founded.
  induction a; constructor.
  lia.
  move => y.
  move => Hy; unfold lt in Hy.
  pose Hy' := Le.le_S_n _ _ Hy.
  assert (y = a \/ lt y a) by lia.
  destruct H.
    rewrite H; trivial.
    case IHa.
    move => IHa'.
    apply IHa'; trivial.
Qed.

Lemma wf_relpos_lt : well_founded relpos_lt.
Proof.
  suff: (well_founded (fun (x y : rel) => lt (nat_of_rel x) (nat_of_rel y) /\ x >= O_Z /\ y >= O_Z)).
  apply well_founded_equiv => x y.
  split. 
  apply relpos_lt_natlt.
  apply relpos_lt_natlt.
  unfold well_founded.
  move => a.
  assert (a < O_Z \/ a >= O_Z).
  unfold O_Z; case a as [a_0 a_1]; unfold rel_lt, rel_le; lia.
  case: H.
  + move => Ha.
    constructor.
    move => y [_ [_ Abs]].
    case a as [a_0 a_1].
    unfold O_Z, rel_le, rel_lt in * |-.
    lia.
  + move => Ha.
    pose n := nat_of_rel a.
    pose Eqan := rel_of_nat_of_relpos Ha.
    fold n in Eqan.
    move : Eqan. move : Ha.
    assert (nat_of_rel a = n) as Eq.
    fold n; reflexivity.
    move : Eq.
    move : n => n.
    move : a.
    induction n.
    - move => a _ _ EqO_Za.
      case a as [a_0 a_1].
      unfold rel_of_nat, rel_eq in EqO_Za.
      assert (a_0 = a_1) as Eqa0 by lia; clear EqO_Za.
      constructor.
      move => y.
      rewrite Eqa0.
      move => [Hy_0 [Hy_1 _]].
      case y as [y_0 y_1]; unfold nat_of_rel in Hy_0.
      unfold O_Z, rel_le in Hy_1.
      lia.
    - move => a EqaSn Ha EqSna.
      constructor.
      move => x [Ltxa [LeOx LeOa]].
      assert (x == a + (- One) \/ x < a + (- One)) as Disj.
      case a as [a_0 a_1], x as [x_0 x_1].
      unfold One, rel_minus, rel_plus, rel_eq, rel_lt => /=.
      unfold nat_of_rel in Ltxa.
      unfold O_Z, rel_le in LeOx.
      unfold O_Z, rel_le in LeOa.
      lia.
      case: Disj => Hx.
      * assert (nat_of_rel x = n) as Hx_0.
        case a as [a_0 a_1], x as [x_0 x_1].
        unfold rel_of_nat, One, rel_minus, rel_plus, rel_eq in Hx, EqSna.
        unfold nat_of_rel.
        lia.
        assert (rel_of_nat n == x) as Hx_1.
        case a as [a_0 a_1], x as [x_0 x_1].
        unfold rel_of_nat, rel_eq.
        unfold O_Z, One, rel_minus, nat_of_rel, rel_plus, rel_eq, rel_le in * |-; lia.
        apply (IHn x) => //.
      * pose b := a + (- One).
        assert (nat_of_rel b = n) as Hb_0.
        unfold b.
        case a as [a_0 a_1], x as [x_0 x_1].
        unfold rel_of_nat, O_Z, One, rel_minus, rel_plus, rel_eq, rel_lt, rel_le in Hx, EqSna, LeOx, LeOa.
        unfold rel_of_nat, One, rel_minus, rel_plus, rel_eq, nat_of_rel.
        lia.
        assert (O_Z <= b) as Hb_1.
        unfold b.
        case a as [a_0 a_1], x as [x_0 x_1].
        unfold rel_of_nat, O_Z, One, rel_minus, rel_plus, rel_eq, rel_lt, rel_le in Hx, EqSna, LeOx, LeOa.
        unfold rel_of_nat, O_Z, One, rel_minus, rel_plus, rel_eq, nat_of_rel, rel_le.
        lia.
        assert (rel_of_nat n == b) as Hb_2.
        unfold b.
        case a as [a_0 a_1], x as [x_0 x_1].
        unfold rel_of_nat, O_Z, One, rel_minus, rel_plus, rel_eq, rel_lt, rel_le in Hx, EqSna, LeOx, LeOa.
        unfold rel_of_nat, O_Z, One, rel_minus, rel_plus, rel_eq, nat_of_rel, rel_le.
        lia.
        pose IHb := IHn b Hb_0 Hb_1 Hb_2.
        case: IHb => IHb. clear IHn.
        fold b in Hx.
        assert (lt (nat_of_rel x) (nat_of_rel b)) as Hx_0.
        case b as [a_0 a_1], x as [x_0 x_1].
        unfold nat_of_rel, rel_lt.
        unfold rel_lt in Hx.
        unfold O_Z, rel_le in Hb_1, LeOx.
        lia.
        apply IHb.
        repeat split => //.
Qed.