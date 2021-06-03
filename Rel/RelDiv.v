Add LoadPath "C:\Users\Hp\Documents\CoqGit\Rel" as CoqRelDir.

Load RelCong.

Definition div x y := ∃ q : rel, q * x == y.
Notation "x '|Z' y" := (div x y) (at level 30).

Instance divProper : Proper (rel_eq ==> rel_eq ==> iff) div.
Proof.
  move => x x' Eqxx' y y' Eqyy'.
  unfold div. setoid_rewrite Eqxx'. setoid_rewrite Eqyy' => //.
Qed.

Instance refl_div : Reflexive div.
Proof.
  move => x; unfold div.
  exists One. ring.
Qed.

Instance trans_div : Transitive div.
Proof.
  move => x y z. unfold div.
  case => qxy Congxy.
  case => qyz Congyz.
  exists (qyz * qxy). ring [Congxy Congyz].
Qed.

Definition prime (p : rel) := 
  (p > One) ∧ ( ∀ d : rel, d > O_Z -> d |Z p -> ( d == One ∨ d == p ) ).

Lemma div_is_decidable (x y : rel) : y =/= O_Z -> div y x ∨ not (div y x).
Proof.
  intro neq.
  pose div := rel_eucldiv_aux x neq.
  case div; clear div.
  intro x0; case x0; clear x0.
  intro q; intro r.
  case_eq (r ==? O_Z).
  all: move =>/rel_eqP.
  all : intro eq.
  rewrite eq.
  all: intro H.
  all : destruct H; destruct H0.
  left.
  unfold div.
  exists q.
  ring [H].

  right.
  unfold div.
  intro is_div.
  inversion is_div.
  rewrite <-H in H2.
  suff : r == O_Z.
  exact eq.

  assert (r == y * (x0 - q)) as rVal.
  ring [H2].
  clear H2.
  assert (r ≡ O_Z mod y).
  unfold CongMod.
  exists (x0 - q).
  ring [rVal].
  clear rVal x0 is_div H eq q.

  assert (r ≡ O_Z mod |y|) as Cong.
  assert (y < O_Z ∨ y > O_Z) as Disj.
    case y as [y_0 y_1].
    unfold O_Z, rel_eq in neq.
    unfold rel_lt, O_Z.
    lia.
  
  case Disj.
    move /rel_ltP => Hy.
    unfold "| _ |"; rewrite Hy.
    unfold "_ ≡ _ mod _" in H2; unfold "_ ≡ _ mod _".
    case H2 => q Hq.
    exists (-q); ring_simplify; ring_simplify in Hq => //.

    move => Hy.
    unfold "_ ≡ _ mod _".
    setoid_rewrite (relspos_abs Hy).
    unfold "_ ≡ _ mod _" in H2 => //.

  rewrite (@simpl_CongMod0 r (|y|)) => //.
  reflexivity.
  apply (@rel_lelt_lt (O_Z) (r) (|y|)) => //.
  symmetry => //.
Qed.

Definition divb_set (y x : rel) : { b : bool | (b = true -> (y |Z x)) /\ (b = false -> not (y |Z x)) }.
  case_eq (y ==? O_Z).
  + move /rel_eqP => Eqy0.
    case_eq (x ==? O_Z).
    move /rel_eqP => Eqx0.
    assert ((true = true → y |Z x) ∧ (true = false → ¬ y |Z x)).
      split. 2 : discriminate.
      move => _. setoid_rewrite Eqy0. setoid_rewrite Eqx0.
      exists O_Z. ring.
      exact (exist _ true H).
    
    move /rel_eqP => Neqx0.
    assert ((false = true → y |Z x) ∧ (false = false → ¬ y |Z x)).
      split. 1 : discriminate.
      move => _. move => Abs.
      case Abs => q. rewrite Eqy0. move => H.
      assert (x == O_Z). ring_simplify in H. fold O_Z in H.
      rewrite H; reflexivity. apply Neqx0 => //.
      exact (exist _ false H).

  + move /rel_eqP => π.
    case_eq (rel_eucldiv_aux x π).
    move => [q r] Hqr _.
    case_eq (r ==? O_Z).
    * move /rel_eqP => Eqr0.
      case: Hqr => Hqr _.
      setoid_rewrite Eqr0 in Hqr.
      assert ((true = true → y |Z x) ∧ (true = false → ¬ y |Z x)) as Goal.
      split. 2 : discriminate.
      move => _. exists q.
      assert (q * y == x). ring [Hqr]; clear Hqr. assumption.
      exact (exist _ true Goal).
    * move /rel_eqP => Neqr0.
      case: Hqr. move => Hqr [Hr0 Hr1].
      assert ( (false = true → y |Z x) ∧ (false = false → ¬ y |Z x) ) as Goal.
      split. 1 : discriminate.
      move => _ Dxy.
      case: Dxy => q'.
      move => Hxy.
      assert (x ≡ r mod y); unfold CongMod. 
      exists q; rewrite Hqr; reflexivity.
      assert (x ≡ O_Z mod y); unfold CongMod.
      exists q'. ring [Hxy].
      setoid_rewrite H in H0; clear H. rename H0 into Cong0.

      assert (r ≡ O_Z mod |y|) as Cong.
      assert (y < O_Z ∨ y > O_Z) as Disj.
        case y as [y_0 y_1].
        unfold O_Z, rel_eq in π.
        unfold rel_lt, O_Z.
        lia.

        case Disj.
          move /rel_ltP => Hy.
          unfold "| _ |"; rewrite Hy.
          unfold "_ ≡ _ mod _" in Cong0; unfold "_ ≡ _ mod _".
          case: Cong0 => q'' => Hq''.
          exists (-q''); ring_simplify. ring_simplify in Hq''. assumption.

          move => Hy.
          unfold "_ ≡ _ mod _".
          setoid_rewrite (relspos_abs Hy).
          unfold "_ ≡ _ mod _" in Cong0. assumption.
          clear Cong0. clear Hxy q'.

      assert (O_Z < |y|).
      apply (rel_lelt_lt Hr0 Hr1).
      assert (O_Z ≡ r mod |y|) by symmetry => //.
      pose CCL := (@simpl_CongMod0 r (|y|) H Hr0 Hr1 H0).
      apply Neqr0. rewrite CCL. reflexivity.
      exact (exist _ false Goal).
Defined.

Definition divb y x := witness (divb_set y x).

Lemma divP {x y : rel} : reflect (div x y) (divb x y).
Proof.
  unfold divb.
  case_eq (divb_set x y) => b [HT HF] Hdivb.
  
  case b eqn: Eq. all : unfold witness.
  assert (true = true) by reflexivity.
  pose H' := HT H; clearbody H'.
    apply ReflectT => //.

  assert (false = false) by reflexivity.
  pose H' := HF H; clearbody H'.
    apply ReflectF => //.
Qed.

Notation "x '|Z?' y" := (divb x y) (at level 30).

Lemma div_le : ∀ x : rel, x > O_Z -> 
  ( ∀ y : rel, (y |Z x) -> y <= x ).
Proof.
  move => x Hx.
  move => y Dyx; unfold div in Dyx.
  case: Dyx => q Eq.
  
  assert ((y <= x) ∨ (x < y)).
    case x as [x_0 x_1], y as [y_0 y_1].
    unfold rel_le, rel_lt. lia.

  case H => //.
  move => Ltxy; clear H.

  assert (q >= One).
    case x as [x_0 x_1], y as [y_0 y_1], q as [q_0 q_1].
    unfold O_Z, One, rel_lt, rel_le, rel_prod, rel_eq in *.
    simpl. nia.

  case x as [x_0 x_1], y as [y_0 y_1], q as [q_0 q_1].
  unfold rel_le, O_Z, One, rel_eq, rel_prod, rel_lt in *.
  nia.
Qed.

(* 
Lemma composed_or_prime : ∀ x : rel, x > One ->
  ( ∃ n : rel, (One < n) ∧ (n < x) ∧ (n |Z x) ) ∨ ( prime x ).
*)

Definition prime_divisor_of (x : rel) := (x > One) ->
  { p : rel | prime p ∧ p |Z x }.

(*
Definition ind_prime_divisor : 
  ∀ x, (∀ x', relpos_lt x' x -> prime_divisor_of x') -> prime_divisor_of x.
Proof.
  move => x IHx.
  case (x >? One) eqn: Hx.
  + move: Hx=>/rel_ltP=>pi_x.
*)

(*
Lemma admit_prime_divisor (x : rel) : (x > One) -> ( ∃ p : rel, ( prime p ∧ p|x ) ).
*)