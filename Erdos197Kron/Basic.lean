module

public import Mathlib.Logic.Equiv.Set
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.NumberTheory.DiophantineApproximation.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

public section

/-!
# Rotation codings are not permutable (Theorem K, one frequency)

The proof follows `docs/proof.md`. Write `θ n = Int.fract (n * α + β)`.

* `no_ap`, `Adm`, `adm_of_enum`, `anchor`: copied verbatim from erdos-197-rho (see below).
* `orbit` (orbit lemma, two anchors): anchors `f₁, f₂ ∈ S` and an infinite chain
  `u (k + 1) = 2 u k - f` (`f ∈ {f₁, f₂}`, every `u k > f₁, f₂`) in `S` rule out an admissible
  ranking (infinite descent of positions).
* `fract_step` (K1): `θ (2u - f) = 2 θ u - θ f` when the right side lies in `[0, 1)`.
* `invariant`: if `θ f₁ < θ f₂` and `θ u ∈ [θ f₁, θ f₂]`, one of `2u - f₁`, `2u - f₂` lands in
  `[θ f₁, θ f₂]` again.
* `kron_adm_of_dense`, `main_of_dense`: the theorem with density as a hypothesis.
* `dense_of_irrational` (density with arbitrarily large `n`, Dirichlet approximation).
* `kron_adm` (superset form) and `main_thm` (the statement of `Challenge.lean`).
-/

namespace Erdos197Kron

/-! ### Copied from erdos-197-rho

`no_ap` is copied verbatim from `Erdos197Interval/Basic.lean` (lines 307-317) of
erdos-197-rho; `Adm`, `adm_of_enum` and `anchor` are copied verbatim from
`Erdos197Rho/Basic.lean` (lines 183-251). Only the namespace differs. -/

theorem no_ap {v : ℕ → ℕ}
    (hv : ¬ ∃ l : List ℕ, (∃ a d : ℕ,
        l.map v = (List.range 3).map (fun n => a + n • d) ∨
          l.map v = (List.range 3).reverse.map (fun n => a + n • d)) ∧
        l.Pairwise (· < ·))
    {p q r : ℕ} (hpq : p < q) (hqr : q < r) (hap : v p + v r = 2 * v q) : False := by
  rcases le_total (v p) (v q) with h | h
  · exact hv ⟨[p, q, r], ⟨v p, v q - v p, Or.inl (by simp [List.range_succ]; omega)⟩,
      by simp; omega⟩
  · exact hv ⟨[p, q, r], ⟨v r, v q - v r, Or.inr (by simp [List.range_succ]; omega)⟩,
      by simp; omega⟩

/-- `ρ` ranks the elements of `S` injectively, obeys the *midpoint rule* on `S` (the middle term
`y` of every 3-term AP `x < y < z` of `S` comes before both ends or after both), and only
finitely many elements of `S` have a position `≤ N`, for every `N` (an order of type `ω`). -/
structure Adm (S : Set ℕ) (ρ : ℕ → ℕ) : Prop where
  inj : ∀ x y, x ∈ S → y ∈ S → ρ x = ρ y → x = y
  mid : ∀ x y z, x ∈ S → y ∈ S → z ∈ S → x < y → x + z = 2 * y → (ρ y < ρ x ↔ ρ y < ρ z)
  fin : ∀ N, ∃ B, ∀ x, x ∈ S → ρ x ≤ N → x ≤ B

/-- The positions `f.symm` of an enumeration `f : ℕ ≃ S` with no monotone 3-term AP
(formal-conjectures' predicate, unfolded) form an admissible ranking of `S`. -/
theorem adm_of_enum (S : Set ℕ) (f : ℕ ≃ S)
    (hf : ¬ ∃ l : List ℕ, (∃ a d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => a + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => a + n • d)) ∧
        l.Pairwise (· < ·)) :
    ∃ ρ : ℕ → ℕ, Adm S ρ := by
  classical
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ → ℕ, ∀ x (hx : x ∈ S), ρ x = f.symm ⟨x, hx⟩ :=
    ⟨fun x => if hx : x ∈ S then f.symm ⟨x, hx⟩ else 0, fun x hx => by simp [hx]⟩
  have hfρ : ∀ x, x ∈ S → (f (ρ x) : ℕ) = x := fun x hx => by simp [hρ x hx]
  have inj : ∀ x y, x ∈ S → y ∈ S → ρ x = ρ y → x = y := fun x y hx hy h => by
    rw [← hfρ x hx, ← hfρ y hy, h]
  refine ⟨ρ, ⟨inj, fun x y z hx hy hz hxy hxz => ?_, fun N => ?_⟩⟩
  · have ex := hfρ x hx
    have ey := hfρ y hy
    have ez := hfρ z hz
    have n₁ : ρ y ≠ ρ x := fun e => by have := inj y x hy hx e; omega
    have n₂ : ρ y ≠ ρ z := fun e => by have := inj y z hy hz e; omega
    constructor
    · intro h
      by_contra h'
      exact no_ap hf (p := ρ z) (q := ρ y) (r := ρ x) (by omega) h
        (by simp only [Function.comp_apply, ex, ey, ez]; omega)
    · intro h
      by_contra h'
      exact no_ap hf (p := ρ x) (q := ρ y) (r := ρ z) (by omega) h
        (by simp only [Function.comp_apply, ex, ey, ez]; omega)
  · -- everything listed at positions `≤ N` is at most `B`
    have key : ∀ N, ∃ B, ∀ i, i ≤ N → (f i : ℕ) ≤ B := by
      intro N
      induction N with
      | zero => exact ⟨f 0, fun i hi => by rw [show i = 0 by omega]⟩
      | succ N ih =>
        obtain ⟨B, hB⟩ := ih
        refine ⟨max B (f (N + 1)), fun i hi => ?_⟩
        rcases Nat.lt_or_ge i (N + 1) with h | h
        · exact le_max_of_le_left (hB i (by omega))
        · obtain rfl : i = N + 1 := by omega
          exact le_max_right _ _
    obtain ⟨B, hB⟩ := key N
    exact ⟨B, fun x hx hxN => by rw [← hfρ x hx]; exact hB _ hxN⟩

variable {S : Set ℕ} {ρ : ℕ → ℕ}

/-- **Lemma 4.1 (anchor).** If `a ≺ w` and `z = 2w - a ∈ S` with `a < w`, then `z ≺ w`:
otherwise `a ≺ w ≺ z` is a monotone 3-term AP. -/
theorem anchor (hρ : Adm S ρ) {a w z : ℕ} (ha : a ∈ S) (hw : w ∈ S) (hz : z ∈ S) (haw : a < w)
    (hawz : a + z = 2 * w) (h : ρ a < ρ w) : ρ z < ρ w := by
  have m := hρ.mid a w z ha hw hz haw hawz
  have n : ρ z ≠ ρ w := fun e => by have := hρ.inj z w hz hw e; omega
  omega

/-! ### The orbit lemma -/

/-- **Orbit lemma** (`docs/proof.md` §2; Theorem RS Step 0 of the working notes), for two
anchors. If `f₁, f₂ ∈ S` and `u` is a chain in `S` above both anchors with
`u (k + 1) = 2 u k - f₁` or `2 u k - f₂` at every step, then `S` has no admissible ranking:
past the finitely many points that precede an anchor, the anchor rule makes every step go
strictly down in position. -/
theorem orbit (hρ : Adm S ρ) {f₁ f₂ : ℕ} (h₁ : f₁ ∈ S) (h₂ : f₂ ∈ S) (u : ℕ → ℕ)
    (hu : ∀ k, u k ∈ S) (hf₁ : ∀ k, f₁ < u k) (hf₂ : ∀ k, f₂ < u k)
    (hstep : ∀ k, u (k + 1) + f₁ = 2 * u k ∨ u (k + 1) + f₂ = 2 * u k) : False := by
  obtain ⟨B, hB⟩ := hρ.fin (ρ f₁ + ρ f₂)
  have hgrow : ∀ k, k ≤ u k := by
    intro k
    induction k with
    | zero => omega
    | succ k ih =>
      have := hstep k
      have := hf₁ k
      have := hf₂ k
      omega
  have late : ∀ k, B < u k → ρ (u (k + 1)) < ρ (u k) := by
    intro k hk
    have hlt : ¬ ρ (u k) ≤ ρ f₁ + ρ f₂ := fun h => by have := hB _ (hu k) h; omega
    rcases hstep k with h | h
    · exact anchor hρ h₁ (hu k) (hu (k + 1)) (hf₁ k) (by omega) (by omega)
    · exact anchor hρ h₂ (hu k) (hu (k + 1)) (hf₂ k) (by omega) (by omega)
  have desc : ∀ n, ρ (u (B + 1 + n)) + n ≤ ρ (u (B + 1)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := late (B + 1 + n) (by have := hgrow (B + 1 + n); omega)
      show ρ (u (B + 1 + n + 1)) + (n + 1) ≤ ρ (u (B + 1))
      omega
  have := desc (ρ (u (B + 1)) + 1)
  omega

/-! ### The invariant interval -/

/-- **(K1)** `θ (2u - f) = 2 θ u - θ f` whenever the right side lies in `[0, 1)`. -/
theorem fract_step (α β : ℝ) {u f : ℕ} (hfu : f ≤ u) {x y : ℝ}
    (hx : Int.fract (f * α + β) = x) (hy : Int.fract (u * α + β) = y)
    (h0 : 0 ≤ 2 * y - x) (h1 : 2 * y - x < 1) :
    Int.fract (((2 * u - f : ℕ) : ℝ) * α + β) = 2 * y - x := by
  rw [Int.fract_eq_iff]
  refine ⟨h0, h1, 2 * ⌊(u : ℝ) * α + β⌋ - ⌊(f : ℝ) * α + β⌋, ?_⟩
  rw [← hx, ← hy, Nat.cast_sub (by omega)]
  unfold Int.fract
  push_cast
  ring

/-- **Invariance (d = 1).** If `u > f₁, f₂` and `θ u ∈ [θ f₁, θ f₂]`, then
`v = 2u - f₁` (when `2 θ u ≤ θ f₁ + θ f₂`) or `v = 2u - f₂` (otherwise) satisfies `v > u` and
`θ v ∈ [θ f₁, θ f₂]`. -/
theorem invariant {α β : ℝ} {f₁ f₂ u : ℕ} (hf₁ : f₁ < u) (hf₂ : f₂ < u)
    (hy : Int.fract (u * α + β) ∈ Set.Icc (Int.fract (f₁ * α + β)) (Int.fract (f₂ * α + β))) :
    ∃ v, (v + f₁ = 2 * u ∨ v + f₂ = 2 * u) ∧ u < v ∧
      Int.fract (v * α + β) ∈ Set.Icc (Int.fract (f₁ * α + β)) (Int.fract (f₂ * α + β)) := by
  have l₁ := Int.fract_nonneg ((f₁ : ℝ) * α + β)
  have l₂ := Int.fract_lt_one ((f₂ : ℝ) * α + β)
  obtain ⟨hy1, hy2⟩ := hy
  by_cases h : 2 * Int.fract ((u : ℝ) * α + β) ≤ Int.fract ((f₁ : ℝ) * α + β) +
      Int.fract ((f₂ : ℝ) * α + β)
  · refine ⟨2 * u - f₁, Or.inl (by omega), by omega, ?_⟩
    rw [fract_step α β hf₁.le rfl rfl (by linarith) (by linarith)]
    constructor <;> linarith
  · refine ⟨2 * u - f₂, Or.inr (by omega), by omega, ?_⟩
    rw [fract_step α β hf₂.le rfl rfl (by linarith) (by linarith)]
    constructor <;> linarith

/-! ### Theorem K with the density statement as a hypothesis -/

/-- **Theorem K, d = 1, superset form, density assumed.** If every subinterval `(c, e)` of
`[0, 1]` contains `θ n` for arbitrarily large `n`, then no `S ⊇ {n : θ n ∈ (a, b)}` has an
admissible ranking. -/
theorem kron_adm_of_dense {α β a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hD : ∀ N : ℕ, ∀ c e : ℝ, 0 ≤ c → c < e → e ≤ 1 →
      ∃ n ≥ N, Int.fract (n * α + β) ∈ Set.Ioo c e)
    (S : Set ℕ) (hS : ∀ n : ℕ, Int.fract (n * α + β) ∈ Set.Ioo a b → n ∈ S)
    (hρ : Adm S ρ) : False := by
  -- two anchors, below and above the midpoint of `(a, b)`
  obtain ⟨f₁, -, h1⟩ := hD 0 a ((a + b) / 2) ha (by linarith) (by linarith)
  obtain ⟨f₂, -, h2⟩ := hD 0 ((a + b) / 2) b (by linarith) (by linarith) hb
  have h12 : Int.fract ((f₁ : ℝ) * α + β) < Int.fract ((f₂ : ℝ) * α + β) := by
    linarith [h1.2, h2.1]
  -- a starting point above both anchors in the invariant interval
  obtain ⟨u₀, hu₀N, hu₀⟩ := hD (max f₁ f₂ + 1) _ _ (Int.fract_nonneg _) h12
    (Int.fract_lt_one _).le
  let P : ℕ → Prop := fun u => f₁ < u ∧ f₂ < u ∧
    Int.fract ((u : ℝ) * α + β) ∈ Set.Icc (Int.fract ((f₁ : ℝ) * α + β))
      (Int.fract ((f₂ : ℝ) * α + β))
  have step : ∀ u, P u → ∃ v, (v + f₁ = 2 * u ∨ v + f₂ = 2 * u) ∧ P v := by
    rintro u ⟨hu1, hu2, hu⟩
    obtain ⟨v, hv, huv, hvI⟩ := invariant hu1 hu2 hu
    exact ⟨v, hv, by omega, by omega, hvI⟩
  choose! g hg using step
  have hP : ∀ k, P (g^[k] u₀) := by
    intro k
    induction k with
    | zero =>
      have := le_max_left f₁ f₂
      have := le_max_right f₁ f₂
      exact ⟨by simp only [Function.iterate_zero, id]; omega,
        by simp only [Function.iterate_zero, id]; omega, hu₀.1.le, hu₀.2.le⟩
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact (hg _ ih).2
  have memS : ∀ v, P v → v ∈ S := fun v hv =>
    hS v ⟨by linarith [h1.1, hv.2.2.1], by linarith [h2.2, hv.2.2.2]⟩
  refine orbit hρ (hS f₁ ⟨h1.1, by linarith [h1.2]⟩) (hS f₂ ⟨by linarith [h2.1], h2.2⟩)
    (fun k => g^[k] u₀) (fun k => memS _ (hP k)) (fun k => (hP k).1) (fun k => (hP k).2.1)
    (fun k => ?_)
  simp only [Function.iterate_succ_apply']
  exact (hg _ (hP k)).1

/-- **Theorem K, d = 1, density assumed** (enumeration form of `kron_adm_of_dense`). -/
theorem main_of_dense (α β a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hD : ∀ N : ℕ, ∀ c e : ℝ, 0 ≤ c → c < e → e ≤ 1 →
      ∃ n ≥ N, Int.fract (n * α + β) ∈ Set.Ioo c e) :
    ¬ ∃ f : ℕ ≃ {n : ℕ | Int.fract (n * α + β) ∈ Set.Ioo a b},
      ¬ ∃ l : List ℕ, (∃ x d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => x + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => x + n • d)) ∧
        l.Pairwise (· < ·) := by
  rintro ⟨f, hf⟩
  obtain ⟨ρ, hρ⟩ := adm_of_enum _ f hf
  exact kron_adm_of_dense ha hab hb hD _ (fun n h => h) hρ

/-! ### Density for irrational `α` (Dirichlet approximation) -/

/-- Stepping by `δ ≠ 0` with `|δ| < e - c` from any `t` hits `(c, e)` modulo `1`. -/
theorem step_hit (t δ : ℝ) {c e : ℝ} (hc : 0 ≤ c) (he : e ≤ 1) (hδ : δ ≠ 0)
    (hδe : |δ| < e - c) : ∃ m : ℕ, ∃ z : ℤ, t + m * δ - z ∈ Set.Ioo c e := by
  have hft := Int.floor_le t
  have hft' := Int.lt_floor_add_one t
  rcases hδ.lt_or_gt with hneg | hpos
  · rw [abs_of_neg hneg] at hδe
    set q := (t - (⌊t⌋ - 1) - e) / (-δ) with hq
    have hq0 : 0 ≤ q := div_nonneg (by linarith) (by linarith)
    have hqδ : q * (-δ) = t - (⌊t⌋ - 1) - e := div_mul_cancel₀ _ (by linarith)
    have a1 := Nat.floor_le hq0
    have a2 := Nat.lt_floor_add_one q
    have b1 : q * (-δ) < ((⌊q⌋₊ : ℝ) + 1) * (-δ) := mul_lt_mul_of_pos_right a2 (by linarith)
    have b2 : ((⌊q⌋₊ : ℝ) + 1) * (-δ) ≤ (q + 1) * (-δ) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    refine ⟨⌊q⌋₊ + 1, ⌊t⌋ - 1, ?_, ?_⟩ <;> push_cast <;> nlinarith
  · rw [abs_of_pos hpos] at hδe
    set q := ((⌊t⌋ + 1) + c - t) / δ with hq
    have hq0 : 0 ≤ q := div_nonneg (by linarith) hpos.le
    have hqδ : q * δ = (⌊t⌋ + 1) + c - t := div_mul_cancel₀ _ hpos.ne'
    have a1 := Nat.floor_le hq0
    have a2 := Nat.lt_floor_add_one q
    have b1 : q * δ < ((⌊q⌋₊ : ℝ) + 1) * δ := mul_lt_mul_of_pos_right a2 hpos
    have b2 : ((⌊q⌋₊ : ℝ) + 1) * δ ≤ (q + 1) * δ :=
      mul_le_mul_of_nonneg_right (by linarith) hpos.le
    refine ⟨⌊q⌋₊ + 1, ⌊t⌋ + 1, ?_, ?_⟩ <;> push_cast <;> nlinarith

/-- **Density with arbitrarily large `n`.** For irrational `α`, every real `β`, every `N` and
every `0 ≤ c < e ≤ 1`, some `n ≥ N` has `Int.fract (n * α + β) ∈ (c, e)`. -/
theorem dense_of_irrational {α : ℝ} (hα : Irrational α) (β : ℝ) (N : ℕ) {c e : ℝ}
    (hc : 0 ≤ c) (hce : c < e) (he : e ≤ 1) :
    ∃ n ≥ N, Int.fract (n * α + β) ∈ Set.Ioo c e := by
  have hε : 0 < e - c := by linarith
  obtain ⟨j, k, hk0, -, hjk⟩ := Real.exists_int_int_abs_mul_sub_le α
    (n := ⌈1 / (e - c)⌉₊) (Nat.ceil_pos.2 (by positivity))
  have hlt : |(k : ℝ) * α - j| < e - c := by
    have h1 : 1 / (e - c) ≤ ⌈1 / (e - c)⌉₊ := Nat.le_ceil _
    rw [div_le_iff₀ hε] at h1
    refine lt_of_le_of_lt hjk ?_
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hne : (k : ℝ) * α - j ≠ 0 := fun h =>
    (hα.intCast_mul (by omega : k ≠ 0)).ne_int j (by linarith)
  obtain ⟨K, rfl⟩ := Int.eq_ofNat_of_zero_le hk0.le
  obtain ⟨m, z, hmz⟩ := step_hit ((N : ℝ) * α + β) _ hc he hne hlt
  refine ⟨N + K * m, by omega, ?_⟩
  have hfr : Int.fract (((N + K * m : ℕ) : ℝ) * α + β) =
      (N : ℝ) * α + β + m * ((K : ℤ) * α - j) - z := by
    rw [Int.fract_eq_iff]
    refine ⟨by linarith [hmz.1], by linarith [hmz.2], z + m * j, ?_⟩
    push_cast
    ring
  rw [hfr]
  exact hmz

/-! ### Theorem K, d = 1 -/

/-- **Theorem K, d = 1, superset form.** For irrational `α`, real `β` and `0 ≤ a < b ≤ 1`, no
set `S ⊇ {n : Int.fract (n * α + β) ∈ (a, b)}` has an admissible ranking. -/
theorem kron_adm {α β a b : ℝ} (hα : Irrational α) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (S : Set ℕ) (hS : ∀ n : ℕ, Int.fract (n * α + β) ∈ Set.Ioo a b → n ∈ S)
    (hρ : Adm S ρ) : False :=
  kron_adm_of_dense ha hab hb (fun N _ _ hc hce he => dense_of_irrational hα β N hc hce he) S hS hρ

/-- **Theorem K, d = 1, superset/enumeration form.** No `S ⊇ {n : θ n ∈ (a, b)}` has an
enumeration without monotone 3-term APs. -/
theorem kron_sub {α β a b : ℝ} (hα : Irrational α) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (S : Set ℕ) (hS : ∀ n : ℕ, Int.fract (n * α + β) ∈ Set.Ioo a b → n ∈ S) (f : ℕ ≃ S)
    (hf : ¬ ∃ l : List ℕ, (∃ x d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => x + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => x + n • d)) ∧
        l.Pairwise (· < ·)) : False := by
  obtain ⟨ρ, hρ⟩ := adm_of_enum S f hf
  exact kron_adm hα ha hab hb S hS hρ

/-- The statement of `Erdos197Kron.main_result` in `Challenge.lean`. -/
theorem main_thm (α β a b : ℝ) (hα : Irrational α) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ¬ ∃ f : ℕ ≃ {n : ℕ | Int.fract (n * α + β) ∈ Set.Ioo a b},
      ¬ ∃ l : List ℕ, (∃ x d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => x + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => x + n • d)) ∧
        l.Pairwise (· < ·) :=
  fun ⟨f, hf⟩ => kron_sub hα ha hab hb _ (fun _ h => h) f hf

end Erdos197Kron
