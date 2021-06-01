Add LoadPath "C:\Users\Hp\Documents\CoqGit\Rel" as CoqRelDir.

Load RelCong.

Definition div x y := ∃ q : rel, q * x == y.
Notation "x '|Z' y" := (div x y) (at level 30).

Definition prime (p : rel) := 
  (p > One) ∧ ( ∀ d : rel, d > O_Z -> d |Z p -> ( d == One ∨ d == p ) ).

(*
Lemma div_is_decidable: forall x y : rel, y =/= O_Z -> div y x \/ not (div y x).
Proof.
  intro x.
  intro y.
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
Qed.*)

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