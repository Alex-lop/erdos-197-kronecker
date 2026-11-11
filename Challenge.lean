module

public import Mathlib.Logic.Equiv.Set
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.NumberTheory.Real.Irrational

public section

/-!
# Advertised statement

Partial progress on Erdős Problem #197 (<https://www.erdosproblems.com/197>), which remains open.

Erdős #197 asks whether `ℕ` can be split into two sets, each admitting an enumeration (a listing
of order type `ω`) with no monotone 3-term arithmetic progression. A set with such an
enumeration is called *permutable*. The statement below is the case `d = 1` of Theorem K of
`docs/proof.md` (rotation / Sturmian codings), in interval form.

**Theorem K, d = 1 (`Erdos197Kron.main_result`).** Let `α` be irrational, `β` real and
`0 ≤ a < b ≤ 1`. The set `A = {n ∈ ℕ : fract(nα + β) ∈ (a, b)}` has no enumeration without a
monotone 3-term arithmetic progression. Consequently no partition of `ℕ` in which one class is
such a set answers Erdős #197 positively. (The proof shows more: no set `S ⊇ A` is permutable;
see `Erdos197Kron.kron_sub` in `Erdos197Kron/Basic.lean`.)

**Encoding.**
* `fract` is `Int.fract` (`r - ⌊r⌋ ∈ [0, 1)`), `n * α` casts `n : ℕ` to `ℝ`, and `(a, b)` is
  `Set.Ioo a b`; `Irrational α` is Mathlib's `α ∉ range ((↑) : ℚ → ℝ)`.
* An enumeration of a set `S ⊆ ℕ` is a bijection `f : ℕ ≃ S`, read as the list
  `f 0, f 1, f 2, …`.
* "No monotone 3-term AP" is the predicate `¬HasMonotoneAP (Subtype.val ∘ f) 3` of
  google-deepmind/formal-conjectures (`FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean`),
  written out by unfolding `HasMonotoneAP`, `List.IsAPOfLength` and `List.IsAPOfLengthWith`: no
  strictly increasing list of indices `l` is mapped by `Subtype.val ∘ f` onto `x, x + d, x + 2d`
  or onto `x + 2d, x + d, x`. This is the condition used in formal-conjectures'
  `Erdos197.erdos_197`; writing it out keeps this file Mathlib-only and free of new definitions.
  It is written exactly as in `Erdos197Rho.main_result` (the erdos-197-rho project of the same
  series: the exact ρ-partitions are not permutable), with the bound variable `a` renamed `x`
  (`a` is the left end of the window here); `checks/fidelity.lean` checks by `exact` that it
  agrees with formal-conjectures' predicate.
-/

/-- **Theorem K, d = 1.** For irrational `α`, real `β` and `0 ≤ a < b ≤ 1`, the rotation coding
`{n : ℕ | fract(nα + β) ∈ (a, b)}` has no enumeration without monotone 3-term arithmetic
progressions (formal-conjectures' predicate, unfolded). -/
theorem Erdos197Kron.main_result (α β a b : ℝ) (hα : Irrational α) (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ 1) :
    ¬ ∃ f : ℕ ≃ {n : ℕ | Int.fract (n * α + β) ∈ Set.Ioo a b},
      ¬ ∃ l : List ℕ, (∃ x d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => x + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => x + n • d)) ∧
        l.Pairwise (· < ·) := by
  sorry
