Add LoadPath "C:\Users\Hp\Documents\CoqGit\Rel" as CoqRelDir.

Load RelCong.

Definition div x y := ∃ q : rel, q * x = y.
Notation "x '|Z' y" := (div x y) (at level 30).

Definition prime (p : rel) := 
  (p > One) ∧ ( ∀ d : rel, d > O_Z -> d |Z p -> ( d == One ∨ d == p ) ).

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