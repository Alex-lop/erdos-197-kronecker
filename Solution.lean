module

public import Erdos197Kron

public section

/-!
# Proved solution

Comparator checks that the declaration below has exactly the statement of its counterpart in
`Challenge.lean` and uses only the permitted axioms. The proof lives in
`Erdos197Kron/Basic.lean` (`Erdos197Kron.main_thm`): the orbit lemma `orbit`, the invariant
interval `invariant`, density `dense_of_irrational` (Dirichlet approximation), and the
admissible-ranking toolkit `Adm`, `adm_of_enum`, `anchor`, `no_ap` copied verbatim from
erdos-197-rho.
-/

theorem Erdos197Kron.main_result (α β a b : ℝ) (hα : Irrational α) (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ 1) :
    ¬ ∃ f : ℕ ≃ {n : ℕ | Int.fract (n * α + β) ∈ Set.Ioo a b},
      ¬ ∃ l : List ℕ, (∃ x d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => x + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => x + n • d)) ∧
        l.Pairwise (· < ·) :=
  Erdos197Kron.main_thm α β a b hα ha hab hb
