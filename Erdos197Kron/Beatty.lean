module

public import Erdos197Kron.Basic

public section

/-!
# Beatty parity classes are not permutable

For irrational `α` and real `β`, neither `{n : ⌊nα + β⌋ even}` nor `{n : ⌊nα + β⌋ odd}` has an
enumeration without monotone 3-term APs. Each contains the rotation coding
`{n : fract(n(α/2) + β/2) ∈ (r/2, (r+1)/2)}` (`r = 0, 1`), and Theorem K (`kron_sub`) covers
supersets of rotation codings.
-/

namespace Erdos197Kron

/-- If `fract (x/2) ∈ (r/2, (r+1)/2)` with `r ∈ {0, 1}`, then `⌊x⌋ ≡ r (mod 2)`. -/
theorem floor_parity (x : ℝ) (r : ℕ) (hr : r < 2)
    (h : Int.fract (x / 2) ∈ Set.Ioo ((r : ℝ) / 2) ((r + 1) / 2)) : ⌊x⌋ % 2 = r := by
  have hx : x = ((2 * ⌊x / 2⌋ : ℤ) : ℝ) + 2 * Int.fract (x / 2) := by
    rw [Int.fract]; push_cast; ring
  have hfl : ⌊2 * Int.fract (x / 2)⌋ = (r : ℤ) := by
    rw [Int.floor_eq_iff]
    obtain ⟨h1, h2⟩ := h
    push_cast
    constructor <;> linarith
  have e : ⌊x⌋ = 2 * ⌊x / 2⌋ + r := by
    conv_lhs => rw [hx]
    rw [Int.floor_intCast_add, hfl]
  omega

/-- **Beatty parity.** For irrational `α`, real `β` and `r ∈ {0, 1}`, the set
`{n : ⌊nα + β⌋ ≡ r (mod 2)}` has no enumeration without monotone 3-term APs. -/
theorem beatty_parity (α β : ℝ) (hα : Irrational α) (r : ℕ) (hr : r < 2) :
    ¬ ∃ f : ℕ ≃ {n : ℕ | ⌊(n : ℝ) * α + β⌋ % 2 = r},
      ¬ ∃ l : List ℕ, (∃ x d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => x + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => x + n • d)) ∧
        l.Pairwise (· < ·) := by
  rintro ⟨f, hf⟩
  have hα2 : Irrational (α / 2) := by
    simpa using hα.div_natCast (m := 2) (by norm_num)
  have hr1 : (r : ℝ) ≤ 1 := by exact_mod_cast (show r ≤ 1 by omega)
  refine kron_sub (α := α / 2) (β := β / 2) (a := (r : ℝ) / 2) (b := ((r : ℝ) + 1) / 2) hα2
    (by positivity) (by linarith) (by linarith) _ (fun n hn => ?_) f hf
  show ⌊(n : ℝ) * α + β⌋ % 2 = r
  apply floor_parity _ r hr
  rw [show ((n : ℝ) * α + β) / 2 = n * (α / 2) + β / 2 by ring]
  exact hn

end Erdos197Kron
