module

public import Solution
public import Mathlib.Algebra.Module.NatInt

public section

section FC

/-! Verbatim copies of the formal-conjectures definitions (commit
5d8b04d3d41b745cc3f2f3cdd5ed04b60c500983,
FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean, lines 36, 51-52, 129-130, 246-247),
at top level as there (Mathlib defines none of these names). Copied from erdos-197-rho's
`checks/fidelity.lean`. -/

variable {α : Type*} [AddCommMonoid α]

def List.IsAPOfLengthWith (s : List α) (l : ℕ) (a d : α) : Prop :=
  s = (List.range l).map (fun n ↦ a + n • d) ∨ s = (List.range l).reverse.map (fun n ↦ a + n • d)

def List.IsAPOfLength (s : List α) (l : ℕ) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d

def HasMonotoneAP {β : Type*} [Preorder β] (f : β → α) (k : ℕ) : Prop :=
  ∃ l : List β, (l.map f).IsAPOfLength k ∧ l.Pairwise (· < ·)

end FC

/-- Theorem K (d = 1) restated with the formal-conjectures predicate itself; accepted by `exact`
(definitional unfolding only), so the inlined predicate of `Challenge.lean` is the same
proposition. -/
theorem fc_main (α β a b : ℝ) (hα : Irrational α) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ¬ ∃ f : ℕ ≃ {n : ℕ | Int.fract (n * α + β) ∈ Set.Ioo a b},
      ¬HasMonotoneAP (Subtype.val ∘ f) 3 := by
  exact Erdos197Kron.main_result α β a b hα ha hab hb

/-- The link with formal-conjectures' `Erdos197.erdos_197`, whose witness would be a pair
`A, B` with `IsCompl A B`, `∃ f : ℕ ≃ A, ¬HasMonotoneAP (Subtype.val ∘ f) 3` and
`∃ g : ℕ ≃ B, ¬HasMonotoneAP (Subtype.val ∘ g) 3`. If `A` contains a rotation coding
`{n : fract(nα + β) ∈ (a, b)}` (α irrational, `0 ≤ a < b ≤ 1`), then the first enumeration does
not exist, so `A, B` is not a witness. (From `Erdos197Kron.kron_sub`, the superset form.) -/
theorem fc_erdos197_kron (α β a b : ℝ) (hα : Irrational α) (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ 1) (A : Set ℕ) (hA : ∀ n : ℕ, Int.fract (n * α + β) ∈ Set.Ioo a b → n ∈ A) :
    ¬ ∃ f : ℕ ≃ A, ¬HasMonotoneAP (Subtype.val ∘ f) 3 :=
  fun ⟨f, hf⟩ => Erdos197Kron.kron_sub hα ha hab hb A hA f hf

#print axioms fc_main
#print axioms fc_erdos197_kron
