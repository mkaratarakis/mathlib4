/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.Transcendental.Baker.AlgSize
public import Mathlib.NumberTheory.Transcendental.Baker.AuxiliaryFunction
public import Mathlib.NumberTheory.Transcendental.Baker.ExpIndep
public import Mathlib.NumberTheory.Transcendental.Baker.ExpPoly

/-!
# The criterion of Schneider–Lang: the transcendence argument

This file carries out §4.6 of Waldschmidt, *Diophantine Approximation on Linear Algebraic
Groups*: the direct proof of Corollary 4.2.

The auxiliary function is `F = ∑_λ p_λ z ^ τ exp ((t · x) · z)`, with `τ` ranging over
exponents in the first `d₀` coordinates and `t` over multiples of the `x i`.  Its Taylor
coefficients at the points `s · y = ∑ⱼ sⱼ yⱼ` are, up to `σ!`, algebraic numbers of controlled
size (`Transcendental.SchneiderLangProof.one_le_taylorCoeff`), which makes them either zero or
not too small.

## Notation

* `tauVec τ` is the exponent vector `τ` placed in the first `d₀` coordinates of `ℂⁿ`.
* `freq x t = ∑ᵢ tᵢ xᵢ` and `point y s = ∑ⱼ sⱼ yⱼ`.
* `auxF x T p` is the auxiliary function with coefficients `p`.
-/

@[expose] public section

open Finset MultiIndex NumberField

namespace Transcendental.SchneiderLangProof

variable {n d₀ d₁ : ℕ}

/-- The exponent vector `τ` placed in the first `d₀` coordinates. -/
def tauVec (τ : Fin d₀ → ℕ) : Fin n → ℕ := fun v => if h : (v : ℕ) < d₀ then τ ⟨v, h⟩ else 0

/-- The frequency `∑ᵢ tᵢ xᵢ`. -/
def freq (x : Fin d₁ → Fin n → ℂ) (t : Fin d₁ → ℕ) : Fin n → ℂ :=
  fun v => ∑ i, (t i : ℂ) * x i v

/-- The point `∑ⱼ sⱼ yⱼ`. -/
def point (y : Fin n → Fin n → ℂ) (s : Fin n → ℕ) : Fin n → ℂ :=
  fun v => ∑ j, (s j : ℂ) * y j v

/-- The index set of the auxiliary function. -/
abbrev Idx (d₀ d₁ T : ℕ) := (Fin d₀ → Fin (T + 1)) × (Fin d₁ → Fin (T + 1))

/-- The exponent vector of an index. -/
def τOf {T : ℕ} (l : Idx d₀ d₁ T) : Fin n → ℕ := tauVec fun h => (l.1 h : ℕ)

/-- The multiplicities of the `x i` in the frequency of an index. -/
def tOf {T : ℕ} (l : Idx d₀ d₁ T) : Fin d₁ → ℕ := fun i => (l.2 i : ℕ)

/-- The auxiliary function with coefficients `p`. -/
noncomputable def auxF (x : Fin d₁ → Fin n → ℂ) (T : ℕ) (p : Idx d₀ d₁ T → ℂ) :
    (Fin n → ℂ) → ℂ :=
  fun z => ∑ l, p l * expMonomial (τOf (n := n) l) (freq x (tOf l)) z

/-!
### The Taylor coefficients at `s · y`, as an algebraic expression
-/

/-- `σ! ∑_{k ≤ σ} (τ choose k) ξ ^ (τ - k) w ^ (σ - k) / (σ - k)!`, written without division. -/
lemma factorial_mul_expCoeff (τ : ℕ) (ξ w : ℂ) (σ : ℕ) :
    (σ.factorial : ℂ) * expCoeff τ ξ w σ =
      ∑ k ∈ range (σ + 1), ((τ.choose k * σ.descFactorial k : ℕ) : ℂ) *
        ξ ^ (τ - k) * w ^ (σ - k) := by
  rw [expCoeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkσ : k ≤ σ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  have hfac : (σ.factorial : ℂ) = ((σ - k).factorial : ℂ) * σ.descFactorial k := by
    exact_mod_cast (Nat.factorial_mul_descFactorial hkσ).symm
  have hne : ((σ - k).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  rw [hfac]
  push_cast
  field_simp

/-- The exponential factor at `s · y`: `exp ((∑ᵢ tᵢ xᵢ) · (∑ⱼ sⱼ yⱼ)) = ∏ᵢⱼ e_{ij} ^ (tᵢ sⱼ)`. -/
lemma cexp_freq_point (x : Fin d₁ → Fin n → ℂ) (y : Fin n → Fin n → ℂ) (t : Fin d₁ → ℕ)
    (s : Fin n → ℕ) :
    Complex.exp (∑ v, freq x t v * point y s v) =
      ∏ i, ∏ j, Complex.exp (∑ v, x i v * y j v) ^ (t i * s j) := by
  have hsum : ∑ v, freq x t v * point y s v =
      ∑ i, ∑ j, ((t i * s j : ℕ) : ℂ) * ∑ v, x i v * y j v := by
    calc ∑ v, freq x t v * point y s v
        = ∑ v, ∑ i, ∑ j, ((t i * s j : ℕ) : ℂ) * (x i v * y j v) := by
          refine Finset.sum_congr rfl fun v _ => ?_
          simp only [freq, point, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          push_cast
          ring
      _ = ∑ i, ∑ v, ∑ j, ((t i * s j : ℕ) : ℂ) * (x i v * y j v) := Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ v, ((t i * s j : ℕ) : ℂ) * (x i v * y j v) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i, ∑ j, ((t i * s j : ℕ) : ℂ) * ∑ v, x i v * y j v := by
          simp only [Finset.mul_sum]
  rw [hsum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Complex.exp_sum]
  exact Finset.prod_congr rfl fun j _ => Complex.exp_nat_mul _ _

end Transcendental.SchneiderLangProof

namespace Transcendental.SchneiderLangProof

variable {n d₀ d₁ : ℕ}

lemma tauVec_le {τ : Fin d₀ → ℕ} {T : ℕ} (hτ : ∀ h, τ h ≤ T) (v : Fin n) : tauVec τ v ≤ T := by
  unfold tauVec
  split_ifs with h
  · exact hτ _
  · exact Nat.zero_le _

lemma sum_tauVec_le {τ : Fin d₀ → ℕ} {T : ℕ} (hτ : ∀ h, τ h ≤ T) :
    ∑ v : Fin n, tauVec τ v ≤ d₀ * T := by
  have hzero : ∀ v ∈ (Finset.univ : Finset (Fin n)), v ∉ Finset.univ.filter
      (fun v : Fin n => (v : ℕ) < d₀) → tauVec τ v = 0 := by
    intro v _ hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simp [tauVec, hv]
  rw [← Finset.sum_subset (Finset.filter_subset _ _) hzero]
  refine (Finset.sum_le_card_nsmul _ _ T fun v _ => tauVec_le hτ v).trans ?_
  rw [smul_eq_mul]
  refine Nat.mul_le_mul_right _ ?_
  have : (Finset.univ.filter fun v : Fin n => (v : ℕ) < d₀).card ≤ (Finset.range d₀).card :=
    Finset.card_le_card_of_injOn (fun v => (v : ℕ))
      (fun v hv => by simpa using (Finset.mem_filter.1 hv).2)
      (fun a _ b _ h => Fin.ext h)
  simpa using this

lemma tauVec_eq_zero {τ : Fin d₀ → ℕ} {v : Fin n} (hv : ¬ (v : ℕ) < d₀) : tauVec τ v = 0 := by
  simp [tauVec, hv]

section Arithmetic

variable {K : Type*} [Field K] [NumberField K]

/-- The number `σ! · taylorCoeff (auxF x T p) (point y s) σ`, computed in the number field. -/
noncomputable def thetaK (X : Fin d₁ → Fin n → K) (Yg : Fin n → Fin d₀ → K)
    (Eg : Fin d₁ → Fin n → K) (T : ℕ) (p : Idx d₀ d₁ T → ℤ) (s σ : Fin n → ℕ) : K :=
  ∑ l, (p l : K) * ((∏ i, ∏ j, Eg i j ^ (tOf l i * s j)) *
    ∏ v : Fin n, ∑ k ∈ range (σ v + 1),
      (((τOf (n := n) l v).choose k * (σ v).descFactorial k : ℕ) : K) *
        (if h : (v : ℕ) < d₀ then ∑ j, (s j : K) * Yg j ⟨v, h⟩ else 0) ^ (τOf l v - k) *
        (∑ i, (tOf l i : K) * X i v) ^ (σ v - k))

/-- **The Taylor coefficients at `s · y` are algebraic.**  Under an embedding of `K` sending
the generators to the `x i v`, the `y j v` (`v < d₀`) and the `exp (x i · y j)`, `thetaK` is
`σ! · taylorCoeff (auxF x T p) (point y s) σ`. -/
theorem map_thetaK (ι₀ : K →+* ℂ) {x : Fin d₁ → Fin n → ℂ} {y : Fin n → Fin n → ℂ}
    {X : Fin d₁ → Fin n → K} {Yg : Fin n → Fin d₀ → K} {Eg : Fin d₁ → Fin n → K}
    (hX : ∀ i v, ι₀ (X i v) = x i v)
    (hY : ∀ j (v : Fin n) (h : (v : ℕ) < d₀), ι₀ (Yg j ⟨v, h⟩) = y j v)
    (hE : ∀ i j, ι₀ (Eg i j) = Complex.exp (∑ v, x i v * y j v))
    (T : ℕ) (p : Idx d₀ d₁ T → ℤ) (s σ : Fin n → ℕ) :
    ι₀ (thetaK X Yg Eg T p s σ) = (∏ v, ((σ v).factorial : ℂ)) *
      taylorCoeff (auxF x T fun l => (p l : ℂ)) (point y s) σ := by
  have htc := taylorCoeff_linComb (fun l : Idx d₀ d₁ T => (p l : ℂ)) (fun l => τOf (n := n) l)
    (fun l => freq x (tOf l)) (point y s) σ
  rw [show auxF x T (fun l => (p l : ℂ)) = fun z => ∑ l, (p l : ℂ) *
    expMonomial (τOf (n := n) l) (freq x (tOf l)) z from rfl, htc, Finset.mul_sum, thetaK,
    map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [map_mul, map_intCast, map_prod, map_pow, hE, map_sum, map_natCast, hX]
  rw [expMonomialCoeff, cexp_freq_point x y (tOf l) s]
  have hfac : (∏ v, ((σ v).factorial : ℂ)) *
      ∏ v, expCoeff (τOf (n := n) l v) (point y s v) (freq x (tOf l) v) (σ v) =
      ∏ v : Fin n, ∑ k ∈ range (σ v + 1),
        (((τOf (n := n) l v).choose k * (σ v).descFactorial k : ℕ) : ℂ) *
          ι₀ (if h : (v : ℕ) < d₀ then ∑ j, (s j : K) * Yg j ⟨v, h⟩ else 0) ^
            (τOf (n := n) l v - k) * (∑ i, (tOf l i : ℂ) * x i v) ^ (σ v - k) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [factorial_mul_expCoeff]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hv : (v : ℕ) < d₀
    · simp only [hv, ↓reduceDIte, map_sum, map_mul, map_natCast, hY]
      rfl
    · simp only [hv, ↓reduceDIte, map_zero, tauVec_eq_zero hv, τOf, Nat.zero_sub, pow_zero]
      rfl
  rw [← hfac]
  ring

/-- **The size of the Taylor coefficients at `s · y`.**  If the generators have size
`(1, Hg)`, then `thetaK` has size `(A, H)` with `A = d₀T + |σ| + d₁ n T S₁` and
`H = card Λ · δ ^ A e ^ N (δ² |σ| + n S₁ Hg + 1) ^ (d₀ T) (d₁ T Hg + 1) ^ |σ| Hg ^ (d₁ n T S₁)`.
-/
theorem algSize_thetaK {δ : ℕ} {Hg : ℝ} (hδ : 1 ≤ δ) (hHg : 1 ≤ Hg)
    {X : Fin d₁ → Fin n → K} {Yg : Fin n → Fin d₀ → K} {Eg : Fin d₁ → Fin n → K}
    (hXs : ∀ i v, AlgSize δ (X i v) 1 Hg) (hYs : ∀ j h, AlgSize δ (Yg j h) 1 Hg)
    (hEs : ∀ i j, AlgSize δ (Eg i j) 1 Hg) (T S₁ : ℕ) (p : Idx d₀ d₁ T → ℤ) {N : ℝ}
    (hp : ∀ l, |(p l : ℝ)| ≤ Real.exp N) (s : Fin n → ℕ) (hs : ∀ j, s j ≤ S₁)
    (σ : Fin n → ℕ) :
    AlgSize δ (thetaK X Yg Eg T p s σ) (d₀ * T + ∑ v, σ v + d₁ * n * T * S₁)
      (Fintype.card (Idx d₀ d₁ T) * ((δ : ℝ) ^ (d₀ * T + ∑ v, σ v + d₁ * n * T * S₁) *
        Real.exp N * ((δ : ℝ) ^ 2 * (∑ v, σ v : ℕ) + n * S₁ * Hg + 1) ^ (d₀ * T) *
        (d₁ * T * Hg + 1) ^ (∑ v, σ v) * Hg ^ (d₁ * n * T * S₁))) := by
  set M : ℕ := ∑ v, σ v with hM
  set A : ℕ := d₀ * T + M + d₁ * n * T * S₁ with hA
  set C1 : ℝ := (δ : ℝ) ^ 2 * (M : ℕ) + n * S₁ * Hg + 1 with hC1
  set HW : ℝ := d₁ * T * Hg + 1 with hHW
  have hδR : (1 : ℝ) ≤ δ := by exact_mod_cast hδ
  have hC1_1 : 1 ≤ C1 := by
    have : (0 : ℝ) ≤ (δ : ℝ) ^ 2 * M + n * S₁ * Hg := by positivity
    rw [hC1]
    linarith
  have hHW1 : 1 ≤ HW := by
    have : (0 : ℝ) ≤ d₁ * T * Hg := by positivity
    rw [hHW]
    linarith
  -- the coordinates of the point
  have hξ : ∀ v : Fin n, AlgSize δ
      (if h : (v : ℕ) < d₀ then ∑ j, (s j : K) * Yg j ⟨v, h⟩ else 0) 1 (n * S₁ * Hg) := by
    intro v
    by_cases hv : (v : ℕ) < d₀
    · simp only [hv, ↓reduceDIte]
      have hsum := AlgSize.sum (δ := δ) (a := 1) Finset.univ
        (f := fun j => (s j : K) * Yg j ⟨v, hv⟩) (F := fun j => (s j : ℝ) * Hg) fun j _ =>
          ((AlgSize.natCast (s j)).mul (hYs j ⟨v, hv⟩)).congr_exp (by simp)
      refine hsum.mono ?_
      calc ∑ j, (s j : ℝ) * Hg ≤ ∑ _j : Fin n, (S₁ : ℝ) * Hg :=
            Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (by exact_mod_cast hs j)
              (by linarith)
        _ = n * S₁ * Hg := by simp; ring
    · simp only [hv, ↓reduceDIte]
      exact AlgSize.zero.mono (by positivity)
  -- the frequencies
  have hW : ∀ (l : Idx d₀ d₁ T) (v : Fin n), AlgSize δ (∑ i, (tOf l i : K) * X i v) 1 HW := by
    intro l v
    have hsum := AlgSize.sum (δ := δ) (a := 1) Finset.univ (f := fun i => (tOf l i : K) * X i v)
      (F := fun i => (tOf l i : ℝ) * Hg) fun i _ =>
        ((AlgSize.natCast (tOf l i)).mul (hXs i v)).congr_exp (by simp)
    refine hsum.mono ?_
    calc ∑ i, (tOf l i : ℝ) * Hg ≤ ∑ _i : Fin d₁, (T : ℝ) * Hg :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
            (by exact_mod_cast Nat.lt_succ_iff.1 (l.2 i).2) (by linarith)
      _ ≤ HW := by simp [hHW]; nlinarith
  -- one factor of the product over coordinates
  have hfactor : ∀ (l : Idx d₀ d₁ T) (v : Fin n), AlgSize δ
      (∑ k ∈ range (σ v + 1), (((τOf (n := n) l v).choose k * (σ v).descFactorial k : ℕ) : K) *
        (if h : (v : ℕ) < d₀ then ∑ j, (s j : K) * Yg j ⟨v, h⟩ else 0) ^ (τOf (n := n) l v - k) *
        (∑ i, (tOf l i : K) * X i v) ^ (σ v - k))
      (τOf (n := n) l v + σ v) (C1 ^ τOf (n := n) l v * HW ^ σ v) := by
    intro l v
    set τv := τOf (n := n) l v
    set bound : ℕ → ℝ := fun k => if k ≤ τv then (δ : ℝ) ^ (2 * k) *
      (τv.choose k * (σ v).descFactorial k : ℕ) * (n * S₁ * Hg) ^ (τv - k) * HW ^ (σ v - k)
      else 0 with hbound
    have hterm : ∀ k ∈ range (σ v + 1), AlgSize δ
        ((((τv.choose k * (σ v).descFactorial k : ℕ) : K)) *
          (if h : (v : ℕ) < d₀ then ∑ j, (s j : K) * Yg j ⟨v, h⟩ else 0) ^ (τv - k) *
          (∑ i, (tOf l i : K) * X i v) ^ (σ v - k)) (τv + σ v) (bound k) := by
      intro k hk
      have hkσ : k ≤ σ v := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      by_cases hkτ : k ≤ τv
      · simp only [hbound, hkτ, ↓reduceIte]
        have h1 := (AlgSize.natCast (δ := δ) (K := K)
          (τv.choose k * (σ v).descFactorial k)).raise (Nat.zero_le (2 * k))
        have h2 := (h1.mul ((hξ v).pow (τv - k))).mul ((hW l v).pow (σ v - k))
        refine (h2.congr_exp (by omega)).mono (le_of_eq ?_)
        simp only [Nat.sub_zero]
      · have hc : τv.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
        simp only [hbound, hkτ, ↓reduceIte, hc, zero_mul, Nat.cast_zero]
        exact AlgSize.zero
    refine (AlgSize.sum _ hterm).mono ?_
    -- `∑ₖ bound k ≤ C1 ^ τv * HW ^ σ v`
    have hb : ∀ k ∈ range (σ v + 1), bound k ≤
        (if k ≤ τv then (τv.choose k : ℝ) * ((δ : ℝ) ^ 2 * M) ^ k *
          (n * S₁ * Hg) ^ (τv - k) else 0) * HW ^ σ v := by
      intro k hk
      have hkσ : k ≤ σ v := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      by_cases hkτ : k ≤ τv
      · simp only [hbound, hkτ, ↓reduceIte]
        have hdesc : ((σ v).descFactorial k : ℝ) ≤ (M : ℝ) ^ k := by
          have h1 : (σ v).descFactorial k ≤ σ v ^ k := Nat.descFactorial_le_pow _ _
          have h2 : σ v ≤ M := Finset.single_le_sum (fun w _ => Nat.zero_le (σ w))
            (Finset.mem_univ v)
          exact_mod_cast h1.trans (Nat.pow_le_pow_left h2 k)
        have hHWp : HW ^ (σ v - k) ≤ HW ^ σ v := pow_le_pow_right₀ hHW1 (Nat.sub_le _ _)
        have hkey : ((τv.choose k * (σ v).descFactorial k : ℕ) : ℝ) ≤
            τv.choose k * (M : ℝ) ^ k := by
          push_cast
          exact mul_le_mul_of_nonneg_left hdesc (by positivity)
        calc (δ : ℝ) ^ (2 * k) * ((τv.choose k * (σ v).descFactorial k : ℕ) : ℝ) *
              (n * S₁ * Hg) ^ (τv - k) * HW ^ (σ v - k)
            ≤ (δ : ℝ) ^ (2 * k) * (τv.choose k * (M : ℝ) ^ k) *
              (n * S₁ * Hg) ^ (τv - k) * HW ^ σ v := by gcongr
          _ = τv.choose k * ((δ : ℝ) ^ 2 * M) ^ k * (n * S₁ * Hg) ^ (τv - k) * HW ^ σ v := by
              ring
      · simp [hbound, hkτ]
    refine (Finset.sum_le_sum hb).trans ?_
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    -- the binomial sum
    have hsub : ∑ k ∈ range (σ v + 1), (if k ≤ τv then (τv.choose k : ℝ) *
        ((δ : ℝ) ^ 2 * M) ^ k * (n * S₁ * Hg) ^ (τv - k) else 0) ≤
        ∑ k ∈ range (τv + 1), (τv.choose k : ℝ) * ((δ : ℝ) ^ 2 * M) ^ k *
          (n * S₁ * Hg) ^ (τv - k) := by
      rw [← Finset.sum_filter]
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) (fun k _ _ => by positivity)
      simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
      omega
    refine hsub.trans ?_
    rw [show ∑ k ∈ range (τv + 1), (τv.choose k : ℝ) * ((δ : ℝ) ^ 2 * M) ^ k *
        (n * S₁ * Hg) ^ (τv - k) = ∑ k ∈ range (τv + 1), ((δ : ℝ) ^ 2 * M) ^ k *
        (n * S₁ * Hg) ^ (τv - k) * (τv.choose k : ℝ) from
      Finset.sum_congr rfl fun k _ => by ring, ← add_pow]
    exact pow_le_pow_left₀ (by positivity) (by rw [hC1]; linarith) _
  -- one term of the sum over indices
  have hlterm : ∀ l : Idx d₀ d₁ T, AlgSize δ ((p l : K) * ((∏ i, ∏ j, Eg i j ^ (tOf l i * s j)) *
      ∏ v : Fin n, ∑ k ∈ range (σ v + 1),
        (((τOf (n := n) l v).choose k * (σ v).descFactorial k : ℕ) : K) *
          (if h : (v : ℕ) < d₀ then ∑ j, (s j : K) * Yg j ⟨v, h⟩ else 0) ^ (τOf l v - k) *
          (∑ i, (tOf l i : K) * X i v) ^ (σ v - k))) A
      ((δ : ℝ) ^ A * Real.exp N * C1 ^ (d₀ * T) * HW ^ M * Hg ^ (d₁ * n * T * S₁)) := by
    intro l
    have hE' := AlgSize.prod Finset.univ fun i _ =>
      AlgSize.prod Finset.univ fun j _ => (hEs i j).pow (tOf l i * s j)
    have hV := AlgSize.prod Finset.univ fun v _ => hfactor l v
    have hall := (AlgSize.intCast (δ := δ) (K := K) (p l)).mul (hE'.mul hV)
    set a := 0 + (∑ i, ∑ j, 1 * (tOf l i * s j) + ∑ v, (τOf (n := n) l v + σ v)) with ha
    have hts : ∑ i, ∑ j, 1 * (tOf l i * s j) ≤ d₁ * n * T * S₁ := by
      calc ∑ i, ∑ j, 1 * (tOf l i * s j) ≤ ∑ _i : Fin d₁, ∑ _j : Fin n, T * S₁ :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
              rw [one_mul]
              exact Nat.mul_le_mul (Nat.lt_succ_iff.1 (l.2 i).2) (hs j)
        _ = d₁ * n * T * S₁ := by simp; ring
    have hτ : ∑ v, τOf (n := n) l v ≤ d₀ * T :=
      sum_tauVec_le fun h => Nat.lt_succ_iff.1 (l.1 h).2
    have haA : a ≤ A := by
      rw [ha, hA, Finset.sum_add_distrib]
      omega
    refine (hall.raise haA).mono ?_
    have hEb : (∏ i, ∏ j, Hg ^ (tOf l i * s j)) ≤ Hg ^ (d₁ * n * T * S₁) := by
      rw [show (∏ i, ∏ j, Hg ^ (tOf l i * s j)) = Hg ^ (∑ i, ∑ j, 1 * (tOf l i * s j)) by
        simp_rw [one_mul, ← Finset.prod_pow_eq_pow_sum]]
      exact pow_le_pow_right₀ hHg hts
    have hVb : (∏ v, C1 ^ τOf (n := n) l v * HW ^ σ v) ≤ C1 ^ (d₀ * T) * HW ^ M := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC1_1 hτ) (by positivity)
    have hδa : (δ : ℝ) ^ (A - a) ≤ (δ : ℝ) ^ A := pow_le_pow_right₀ hδR (Nat.sub_le _ _)
    have hpl := hp l
    have h0 : (0 : ℝ) ≤ |(p l : ℝ)| := abs_nonneg _
    calc (δ : ℝ) ^ (A - a) * (|(p l : ℝ)| * ((∏ i, ∏ j, Hg ^ (tOf l i * s j)) *
          ∏ v, C1 ^ τOf (n := n) l v * HW ^ σ v))
        ≤ (δ : ℝ) ^ A * (Real.exp N * (Hg ^ (d₁ * n * T * S₁) * (C1 ^ (d₀ * T) * HW ^ M))) := by
          gcongr
      _ = (δ : ℝ) ^ A * Real.exp N * C1 ^ (d₀ * T) * HW ^ M * Hg ^ (d₁ * n * T * S₁) := by ring
  have htot := AlgSize.sum Finset.univ fun l _ => hlterm l
  refine htot.mono (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Arithmetic

end Transcendental.SchneiderLangProof
