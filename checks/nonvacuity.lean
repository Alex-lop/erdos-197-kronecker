module

public import Solution
public import Mathlib.Order.OrderIsoNat
public import Mathlib.Analysis.Real.Sqrt

public section

/-! Non-vacuity of the statement of `Challenge.lean`.

* `hyps_sat`: the hypotheses hold for `α = √2`, any `β`, `(a, b) = (1/4, 3/4)`.
* `hf_sat` (copied from erdos-197-rho): the enumeration predicate, unfolded exactly as in
  `Challenge.lean`, is satisfiable: the powers of two, listed in increasing order, have no
  monotone 3-term AP. So `Erdos197Kron.main_result` is not true merely because the predicate is
  unsatisfiable.
* `coding_infinite`, `coding_enumerable`: every set of the statement is infinite, hence has
  enumerations `ℕ ≃ A`; so the conclusion (no enumeration without monotone 3-term APs) is not
  trivially true. -/

/-- The hypotheses of `Erdos197Kron.main_result` are satisfiable. -/
theorem hyps_sat : Irrational (Real.sqrt 2) ∧ (0 : ℝ) ≤ 1 / 4 ∧ (1 / 4 : ℝ) < 3 / 4 ∧
    (3 / 4 : ℝ) ≤ 1 :=
  ⟨irrational_sqrt_two, by norm_num, by norm_num, by norm_num⟩

/-- The enumeration predicate of `Challenge.lean` is satisfiable: `f k = 2 ^ k` enumerates the
powers of two, and they have no 3-term AP at all. -/
theorem hf_sat : ∃ S : Set ℕ, ∃ f : ℕ ≃ S, ¬ ∃ l : List ℕ, (∃ x d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => x + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => x + n • d)) ∧
        l.Pairwise (· < ·) := by
  refine ⟨_, Equiv.ofInjective (2 ^ ·) (Nat.pow_right_injective le_rfl), ?_⟩
  rintro ⟨l, ⟨a, d, h⟩, hl⟩
  rcases l with _ | ⟨i, _ | ⟨j, _ | ⟨k, _ | ⟨_, _⟩⟩⟩⟩ <;> simp [List.range_succ] at h
  simp at hl
  have hij : 2 ^ i < 2 ^ j := Nat.pow_lt_pow_right Nat.one_lt_two hl.1.1
  have hjk : 2 ^ (j + 1) ≤ 2 ^ k := Nat.pow_le_pow_right Nat.two_pos hl.2
  rw [pow_succ] at hjk
  have := Nat.one_le_two_pow (n := i)
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> omega

/-- Every set of the statement is infinite (`Erdos197Kron.dense_of_irrational`). -/
theorem coding_infinite (α β a b : ℝ) (hα : Irrational α) (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ 1) : Set.Infinite {n : ℕ | Int.fract (n * α + β) ∈ Set.Ioo a b} := by
  refine Set.infinite_of_forall_exists_gt fun N => ?_
  obtain ⟨n, hn, h⟩ := Erdos197Kron.dense_of_irrational hα β (N + 1) ha hab hb
  exact ⟨n, h, by omega⟩

/-- Every set of the statement has enumerations. -/
theorem coding_enumerable (α β a b : ℝ) (hα : Irrational α) (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ 1) : Nonempty (ℕ ≃ {n : ℕ | Int.fract (n * α + β) ∈ Set.Ioo a b}) := by
  have := (coding_infinite α β a b hα ha hab hb).to_subtype
  exact ⟨(Nat.Subtype.orderIsoOfNat _).toEquiv⟩

/-- The conclusion for the instance `α = √2`, `β = 0`, `(a, b) = (1/4, 3/4)`. -/
example : ¬ ∃ f : ℕ ≃ {n : ℕ | Int.fract (n * Real.sqrt 2 + 0) ∈ Set.Ioo (1 / 4) (3 / 4)},
      ¬ ∃ l : List ℕ, (∃ x d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => x + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => x + n • d)) ∧
        l.Pairwise (· < ·) :=
  Erdos197Kron.main_result _ _ _ _ irrational_sqrt_two (by norm_num) (by norm_num) (by norm_num)

#print axioms hyps_sat
#print axioms hf_sat
#print axioms coding_infinite
#print axioms coding_enumerable
