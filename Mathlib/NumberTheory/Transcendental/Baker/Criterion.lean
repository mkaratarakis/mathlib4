/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.NumberTheory.Transcendental.Baker.AlgSize
public import Mathlib.NumberTheory.Transcendental.Baker.AuxiliaryFunction
public import Mathlib.NumberTheory.Transcendental.Baker.ExpIndep
public import Mathlib.NumberTheory.Transcendental.Baker.ExpPoly
public import Mathlib.NumberTheory.Transcendental.Baker.SchwarzProduct

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

namespace Transcendental.SchneiderLangProof

variable {n d₀ d₁ : ℕ}

/-- **Liouville's inequality for the Taylor coefficients at `s · y`.**  A nonzero Taylor
coefficient `c` of order `σ`, with `M = |σ|`, satisfies `1 ≤ M ^ M δ ^ A ‖c‖ H ^ (d - 1)` with
`A` and `H` as in `algSize_thetaK` and `d = [K : ℚ]`. -/
theorem one_le_taylorCoeff {K : Type*} [Field K] [NumberField K] (ι₀ : K →+* ℂ)
    {x : Fin d₁ → Fin n → ℂ} {y : Fin n → Fin n → ℂ}
    {X : Fin d₁ → Fin n → K} {Yg : Fin n → Fin d₀ → K} {Eg : Fin d₁ → Fin n → K}
    (hX : ∀ i v, ι₀ (X i v) = x i v)
    (hY : ∀ j (v : Fin n) (h : (v : ℕ) < d₀), ι₀ (Yg j ⟨v, h⟩) = y j v)
    (hE : ∀ i j, ι₀ (Eg i j) = Complex.exp (∑ v, x i v * y j v))
    {δ : ℕ} {Hg : ℝ} (hδ : 1 ≤ δ) (hHg : 1 ≤ Hg)
    (hXs : ∀ i v, AlgSize δ (X i v) 1 Hg) (hYs : ∀ j h, AlgSize δ (Yg j h) 1 Hg)
    (hEs : ∀ i j, AlgSize δ (Eg i j) 1 Hg) (T S₁ : ℕ) (p : Idx d₀ d₁ T → ℤ) {N : ℝ}
    (hp : ∀ l, |(p l : ℝ)| ≤ Real.exp N) (s : Fin n → ℕ) (hs : ∀ j, s j ≤ S₁)
    (σ : Fin n → ℕ)
    (hne : taylorCoeff (auxF x T fun l => (p l : ℂ)) (point y s) σ ≠ 0) :
    1 ≤ ((∑ v, σ v : ℕ) : ℝ) ^ (∑ v, σ v) * (δ : ℝ) ^ (d₀ * T + ∑ v, σ v + d₁ * n * T * S₁) *
      ‖taylorCoeff (auxF x T fun l => (p l : ℂ)) (point y s) σ‖ *
      (Fintype.card (Idx d₀ d₁ T) * ((δ : ℝ) ^ (d₀ * T + ∑ v, σ v + d₁ * n * T * S₁) *
        Real.exp N * ((δ : ℝ) ^ 2 * (∑ v, σ v : ℕ) + n * S₁ * Hg + 1) ^ (d₀ * T) *
        (d₁ * T * Hg + 1) ^ (∑ v, σ v) * Hg ^ (d₁ * n * T * S₁))) ^
          (Module.finrank ℚ K - 1) := by
  set θ := thetaK X Yg Eg T p s σ with hθ
  have hmap := map_thetaK ι₀ hX hY hE T p s σ
  have hfac0 : (∏ v, ((σ v).factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ => by exact_mod_cast (Nat.factorial_pos _).ne'
  have hθ0 : θ ≠ 0 := by
    intro h0
    rw [← hθ, h0, map_zero] at hmap
    exact hne ((mul_eq_zero.1 hmap.symm).resolve_left hfac0)
  have h := (algSize_thetaK hδ hHg hXs hYs hEs T S₁ p hp s hs σ).one_le hθ0 (by omega) ι₀
  rw [← hθ, hmap, norm_mul, norm_prod] at h
  have hfact : ∏ v, ‖((σ v).factorial : ℂ)‖ ≤ ((∑ v, σ v : ℕ) : ℝ) ^ (∑ v, σ v) := by
    simp only [Complex.norm_natCast]
    have h1 : ∏ v, (σ v).factorial ≤ (∑ v, σ v).factorial :=
      Nat.le_of_dvd (Nat.factorial_pos _) (Nat.prod_factorial_dvd_factorial_sum _ _)
    have h2 := (∑ v, σ v).factorial_le_pow
    exact_mod_cast h1.trans h2
  refine h.trans ?_
  have hH0 : 0 ≤ (Fintype.card (Idx d₀ d₁ T) * ((δ : ℝ) ^ (d₀ * T + ∑ v, σ v + d₁ * n * T * S₁) *
        Real.exp N * ((δ : ℝ) ^ 2 * (∑ v, σ v : ℕ) + n * S₁ * Hg + 1) ^ (d₀ * T) *
        (d₁ * T * Hg + 1) ^ (∑ v, σ v) * Hg ^ (d₁ * n * T * S₁))) := by positivity
  calc (δ : ℝ) ^ (d₀ * T + ∑ v, σ v + d₁ * n * T * S₁) *
        ((∏ v, ‖((σ v).factorial : ℂ)‖) *
          ‖taylorCoeff (auxF x T fun l => (p l : ℂ)) (point y s) σ‖) * _
      ≤ (δ : ℝ) ^ (d₀ * T + ∑ v, σ v + d₁ * n * T * S₁) *
        (((∑ v, σ v : ℕ) : ℝ) ^ (∑ v, σ v) *
          ‖taylorCoeff (auxF x T fun l => (p l : ℂ)) (point y s) σ‖) * _ := by gcongr
    _ = _ := by ring

/-!
### Growth bounds
-/


lemma norm_point_le (y : Fin n → Fin n → ℂ) {S₁ : ℕ} {s : Fin n → ℕ} (hs : ∀ j, s j ≤ S₁) :
    ‖point y s‖ ≤ S₁ * ∑ j, ∑ v, ‖y j v‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun v => ?_
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [norm_mul, Complex.norm_natCast]
  exact mul_le_mul (by exact_mod_cast hs j)
    (Finset.single_le_sum (fun w _ => norm_nonneg (y j w)) (Finset.mem_univ v))
    (norm_nonneg _) (by positivity)

lemma sum_norm_freq_le (x : Fin d₁ → Fin n → ℂ) {T : ℕ} {t : Fin d₁ → ℕ}
    (ht : ∀ i, t i ≤ T) : ∑ v, ‖freq x t v‖ ≤ T * ∑ i, ∑ v, ‖x i v‖ := by
  calc ∑ v, ‖freq x t v‖ ≤ ∑ v, ∑ i, (T : ℝ) * ‖x i v‖ := by
        refine Finset.sum_le_sum fun v _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun i _ => ?_)
        rw [norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast ht i) (norm_nonneg _)
    _ = T * ∑ i, ∑ v, ‖x i v‖ := by
        rw [Finset.sum_comm, Finset.mul_sum]
        simp_rw [Finset.mul_sum]

/-- The growth of the auxiliary function. -/
lemma norm_auxF_le (x : Fin d₁ → Fin n → ℂ) (T : ℕ) {p : Idx d₀ d₁ T → ℂ} {N : ℝ}
    (hp : ∀ l, ‖p l‖ ≤ Real.exp N) (z : Fin n → ℂ) :
    ‖auxF x T p z‖ ≤ Fintype.card (Idx d₀ d₁ T) * (Real.exp N * (1 + ‖z‖) ^ (d₀ * T) *
      Real.exp (T * (∑ i, ∑ v, ‖x i v‖) * ‖z‖)) := by
  unfold auxF
  refine (norm_sum_le _ _).trans ?_
  rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
  refine Finset.sum_le_sum fun l _ => ?_
  rw [norm_mul]
  have hτ := sum_tauVec_le (n := n) fun h => Nat.lt_succ_iff.1 (l.1 h).2
  have hw := sum_norm_freq_le x (T := T) (t := tOf l) fun i => Nat.lt_succ_iff.1 (l.2 i).2
  calc ‖p l‖ * ‖expMonomial (τOf (n := n) l) (freq x (tOf l)) z‖
      ≤ Real.exp N * ((1 + ‖z‖) ^ (∑ v, τOf (n := n) l v) *
          Real.exp ((∑ v, ‖freq x (tOf l) v‖) * ‖z‖)) :=
        mul_le_mul (hp l) (norm_expMonomial_le _ _ z) (norm_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp N * ((1 + ‖z‖) ^ (d₀ * T) *
          Real.exp (T * (∑ i, ∑ v, ‖x i v‖) * ‖z‖)) := by
        gcongr
        · linarith [norm_nonneg z]
        · exact hτ
    _ = Real.exp N * (1 + ‖z‖) ^ (d₀ * T) * Real.exp (T * (∑ i, ∑ v, ‖x i v‖) * ‖z‖) := by
        ring

end Transcendental.SchneiderLangProof

namespace Transcendental.SchneiderLangProof

variable {n d₀ d₁ : ℕ}

/-!
### A linear change of variables preserves vanishing in each total degree
-/

theorem coeff_compContinuousLinearMap_eq_zero {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (P : FormalMultilinearSeries ℂ (ι → ℂ) ℂ)
    (A : (κ → ℂ) →L[ℂ] (ι → ℂ)) {k : ℕ} (h : ∀ α : ι → ℕ, ∑ i, α i = k → coeff P α = 0) :
    ∀ β : κ → ℕ, ∑ j, β j = k → coeff (P.compContinuousLinearMap A) β = 0 := by
  have hdiag : ∀ u : κ → ℂ, (P.compContinuousLinearMap A) k (fun _ => u) = 0 := by
    intro u
    rw [FormalMultilinearSeries.compContinuousLinearMap_apply]
    change P k (fun _ => A u) = 0
    rw [apply_diag_eq_sum_piAntidiag]
    refine Finset.sum_eq_zero fun α hα => ?_
    rw [Finset.mem_piAntidiag] at hα
    rw [h α hα.1, smul_zero]
  intro β hβ
  refine eq_zero_of_forall_sum_monomial_eq_zero (K := ℂ) (s := Finset.univ.piAntidiag k)
    (c := fun β => coeff (P.compContinuousLinearMap A) β) (fun u => ?_) β
    (by simp [Finset.mem_piAntidiag, hβ])
  rw [← apply_diag_eq_sum_piAntidiag, hdiag]

/-!
### The auxiliary function is not zero
-/

lemma freq_injective {x : Fin d₁ → Fin n → ℂ} (hxli : LinearIndependent ℚ x)
    {t t' : Fin d₁ → ℕ} (h : freq x t = freq x t') : t = t' := by
  have hsum : ∑ i, ((t i : ℚ) - t' i) • x i = 0 := by
    funext v
    have hv := congrFun h v
    simp only [freq] at hv
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at hv
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply]
    refine (Finset.sum_congr rfl fun i _ => ?_).trans hv
    rw [Rat.smul_def]
    push_cast
    ring
  funext i
  have := Fintype.linearIndependent_iff.1 hxli _ hsum i
  exact_mod_cast sub_eq_zero.1 this

lemma tauVec_injective (hd₀ : d₀ ≤ n) : Function.Injective (tauVec (n := n) (d₀ := d₀)) := by
  intro τ τ' h
  funext k
  have := congrFun h (Fin.castLE hd₀ k)
  simpa [tauVec] using this

/-- **The auxiliary function of a nonzero coefficient vector is not zero**: some Taylor
coefficient at the origin is nonzero.  This is the linear independence of the functions
`z ^ τ exp ((t · x) · z)`, from `ExpPoly.eq_zero_of_sum_eval_mul_cexp_pi'`. -/
theorem exists_taylorCoeff_ne_zero (hd₀ : d₀ ≤ n) {x : Fin d₁ → Fin n → ℂ}
    (hxli : LinearIndependent ℚ x) (T : ℕ) {p : Idx d₀ d₁ T → ℂ} (hp : p ≠ 0) :
    ∃ σ, taylorCoeff (auxF x T p) 0 σ ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hF : ∀ z, auxF x T p z = 0 := by
    intro z
    have hs := hasSum_linComb p (fun l => τOf (n := n) l) (fun l => freq x (tOf l)) 0 z
    rw [zero_add] at hs
    have h0 : ∀ σ, ∑ l, p l * expMonomialCoeff (τOf (n := n) l) (freq x (tOf l)) 0 σ = 0 :=
      fun σ => by rw [← taylorCoeff_linComb]; exact h σ
    simp only [h0, smul_zero] at hs
    exact hs.unique hasSum_zero
  set P : (Fin d₁ → Fin (T + 1)) → MvPolynomial (Fin n) ℂ := fun t =>
    ∑ τ : Fin d₀ → Fin (T + 1),
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (tauVec fun h => (τ h : ℕ)))
        (p (τ, t)) with hP
  have hid : ∀ z : Fin n → ℂ, ∑ t ∈ Finset.univ, MvPolynomial.eval z (P t) *
      Complex.exp (∑ v, freq x (fun i => (t i : ℕ)) v * z v) = 0 := by
    intro z
    rw [← hF z]
    unfold auxF
    rw [Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [hP, map_sum, MvPolynomial.eval_monomial, Finset.sum_mul]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [expMonomial, Finsupp.prod_fintype _ _ fun i => pow_zero _]
    simp only [Finsupp.coe_equivFunOnFinite_symm, τOf]
    rw [mul_assoc]
    rfl
  have hinj : Set.InjOn (fun t : Fin d₁ → Fin (T + 1) => freq x fun i => (t i : ℕ))
      ((Finset.univ : Finset (Fin d₁ → Fin (T + 1))) : Set (Fin d₁ → Fin (T + 1))) := by
    intro t _ t' _ htt
    have := freq_injective hxli htt
    funext i
    exact Fin.ext (congrFun this i)
  have hP0 := ExpPoly.eq_zero_of_sum_eval_mul_cexp_pi' Finset.univ _ hinj P hid
  apply hp
  funext l
  obtain ⟨τ, t⟩ := l
  have hc := congrArg (fun q : MvPolynomial (Fin n) ℂ =>
    q.coeff (Finsupp.equivFunOnFinite.symm (tauVec fun h => (τ h : ℕ)))) (hP0 t (Finset.mem_univ t))
  simp only [hP, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, AddMonoidAlgebra.coeff_zero]
    at hc
  rw [Finset.sum_eq_single τ (fun τ' _ hne => ?_) (fun h => absurd (Finset.mem_univ τ) h)] at hc
  · simpa using hc
  · rw [ite_eq_right_iff]
    intro heq
    exfalso
    apply hne
    have h1 := tauVec_injective hd₀ (Finsupp.equivFunOnFinite.symm.injective heq)
    funext k
    exact Fin.ext (congrFun h1 k)

end Transcendental.SchneiderLangProof

namespace Transcendental.SchneiderLangProof

variable {n d₀ d₁ : ℕ}


theorem exists_hasFPowerSeriesOnBall_expMonomial (τ : Fin n → ℕ) (w : Fin n → ℂ) {ρ : NNReal}
    (hρ : 0 < ρ) : ∃ P : FormalMultilinearSeries ℂ (Fin n → ℂ) ℂ,
      HasFPowerSeriesOnBall (expMonomial τ w) P 0 ρ := by
  obtain ⟨P, hP, -⟩ := exists_hasFPowerSeriesOnBall_linComb (Λ := Unit) (fun _ => 1)
    (fun _ => τ) (fun _ => w) 0 hρ
  exact ⟨P, by simpa using hP⟩

/-- The Liouville factor: a nonzero Taylor coefficient `c` of order of total degree `M` at a
point `s · y` satisfies `1 ≤ liouvilleFactor … M * ‖c‖`. -/
noncomputable def liouvilleFactor (d₀ d₁ n T S₁ δ D : ℕ) (N Hg : ℝ) (M : ℕ) : ℝ :=
  (M : ℝ) ^ M * (δ : ℝ) ^ (d₀ * T + M + d₁ * n * T * S₁) *
    (((T + 1) ^ d₀ * (T + 1) ^ d₁ : ℕ) * ((δ : ℝ) ^ (d₀ * T + M + d₁ * n * T * S₁) *
      Real.exp N * ((δ : ℝ) ^ 2 * M + n * S₁ * Hg + 1) ^ (d₀ * T) *
      (d₁ * T * Hg + 1) ^ M * Hg ^ (d₁ * n * T * S₁))) ^ (D - 1)

/-- A bound for the auxiliary function on the polydisc of polyradius `ρ`. -/
noncomputable def growth (d₀ d₁ T : ℕ) (N Ax ρ : ℝ) : ℝ :=
  ((T + 1) ^ d₀ * (T + 1) ^ d₁ : ℕ) * (Real.exp N * (1 + ρ) ^ (d₀ * T) * Real.exp (T * Ax * ρ))

lemma card_idx (T : ℕ) : Fintype.card (Idx d₀ d₁ T) = (T + 1) ^ d₀ * (T + 1) ^ d₁ := by
  simp [Idx, Fintype.card_prod]

end Transcendental.SchneiderLangProof

namespace Transcendental.SchneiderLangProof

variable {n d₀ d₁ : ℕ}

/-- **The transcendence argument** (steps 3 to 6 of §4.6 of [waldschmidt2000]), with the choice
of parameters left as hypotheses.

The auxiliary function of Proposition 4.10 is small on the polydisc of radius `r`; by
Liouville's inequality its Taylor coefficients of order `< S₀` in each coordinate vanish at
the points `s · y`, `s ∈ [0, S₁)ⁿ` (`hvan`).  Let `M₀ ≥ S₀` be the first total order at which
some Taylor coefficient at some `s · y` is nonzero.  Schwarz's lemma for Cartesian products,
applied to `F ∘ Y` with vanishing of order `M₀ / n` in each coordinate on `[0, S₁)ⁿ`, makes that
coefficient too small for Liouville's inequality (`hbig`).

The first nonvanishing order is measured by total degree, not by the order in each coordinate as
in Waldschmidt's step 5: the linear change of variables `z ↦ ∑ⱼ zⱼ yⱼ` preserves vanishing in
each total degree (`coeff_compContinuousLinearMap_eq_zero`) but not in each coordinate.
Vanishing in total degree `< M₀` gives vanishing of order `M₀ / n` in each coordinate, which is
what Proposition 4.7 needs; the loss of the factor `n` is absorbed in the choice of `S₁`. -/
theorem core (hn1 : 1 ≤ n) (hd₀ : d₀ ≤ n)
    {x : Fin d₁ → Fin n → ℂ} (hxli : LinearIndependent ℚ x) {y : Fin n → Fin n → ℂ}
    (Yl : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ)) (hYl : ∀ z, Yl z = fun v => ∑ j, z j * y j v)
    {K : Type*} [Field K] [NumberField K] (ι₀ : K →+* ℂ)
    {X : Fin d₁ → Fin n → K} {Yg : Fin n → Fin d₀ → K} {Eg : Fin d₁ → Fin n → K}
    (hX : ∀ i v, ι₀ (X i v) = x i v)
    (hY : ∀ j (v : Fin n) (h : (v : ℕ) < d₀), ι₀ (Yg j ⟨v, h⟩) = y j v)
    (hE : ∀ i j, ι₀ (Eg i j) = Complex.exp (∑ v, x i v * y j v))
    {δ : ℕ} {Hg : ℝ} (hδ : 1 ≤ δ) (hHg : 1 ≤ Hg)
    (hXs : ∀ i v, AlgSize δ (X i v) 1 Hg) (hYs : ∀ j h, AlgSize δ (Yg j h) 1 Hg)
    (hEs : ∀ i j, AlgSize δ (Eg i j) 1 Hg)
    (T S₁ S₀ : ℕ) (hS₁ : 1 ≤ S₁) {U N r : ℝ} {R : NNReal} (hN : 0 < N) (hr0 : 0 < r)
    (hr : S₁ * (∑ j, ∑ v, ‖y j v‖) + 2 ≤ r)
    (hW : 12 * (n : ℝ) ^ 2 ≤ N + U + U) (hRr : Real.exp 1 ≤ R / r)
    (hRr' : R / r ≤ Real.exp ((N + U + U) / 6))
    (hL : (2 * (N + U + U)) ^ (n + 1) ≤
      ((T + 1) ^ d₀ * (T + 1) ^ d₁ : ℕ) * N * Real.log (R / r) ^ n)
    (hMU : ((T + 1) ^ d₀ * (T + 1) ^ d₁ : ℕ) * ((1 + (R : ℝ)) ^ (d₀ * T) *
      Real.exp (T * (∑ i, ∑ v, ‖x i v‖) * R)) ≤ Real.exp U)
    (hvan : ∀ M : ℕ, M ≤ n * S₀ →
      liouvilleFactor d₀ d₁ n T S₁ δ (Module.finrank ℚ K) N Hg M * Real.exp (-U) < 1)
    (Ep : ℕ → ℝ) (hEp : ∀ M, 1 ≤ Ep M)
    (hbig : ∀ M : ℕ, S₀ ≤ M → liouvilleFactor d₀ d₁ n T S₁ δ (Module.finrank ℚ K) N Hg M *
      (n * (1 / Ep M) ^ (M / n * S₁) * growth d₀ d₁ T N (∑ i, ∑ v, ‖x i v‖)
        ((∑ j, ∑ v, ‖y j v‖) *
          (5 * 3 ^ n * Ep M * (S₁ + 2 * ‖(Yl.symm : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))‖)))) < 1) :
    False := by
  classical
  set Ax := ∑ i, ∑ v, ‖x i v‖ with hAx
  set Ay := ∑ j, ∑ v, ‖y j v‖ with hAy
  set D := Module.finrank ℚ K with hD
  set B := ‖(Yl.symm : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))‖ with hB
  have hcard : Fintype.card (Idx d₀ d₁ T) = (T + 1) ^ d₀ * (T + 1) ^ d₁ := card_idx T
  have hAx0 : 0 ≤ Ax := by positivity
  have hAy0 : 0 ≤ Ay := by positivity
  have hR0 : (0 : ℝ) < R := by
    have h1 : (0 : ℝ) < R / r := (Real.exp_pos 1).trans_le hRr
    have := mul_pos h1 hr0
    rwa [div_mul_cancel₀ _ hr0.ne'] at this
  have hRpos : (0 : NNReal) < R := by exact_mod_cast hR0
  -- step 3: the auxiliary function
  choose P hP using fun l : Idx d₀ d₁ T =>
    exists_hasFPowerSeriesOnBall_expMonomial (τOf (n := n) l) (freq x (tOf l)) hRpos
  have hMφ : ∀ (l : Idx d₀ d₁ T) (z : Fin n → ℂ), ‖z‖ < R →
      ‖expMonomial (τOf (n := n) l) (freq x (tOf l)) z‖ ≤
        (1 + (R : ℝ)) ^ (d₀ * T) * Real.exp (T * Ax * R) := by
    intro l z hz
    have hτ := sum_tauVec_le (n := n) fun h => Nat.lt_succ_iff.1 (l.1 h).2
    have hw := sum_norm_freq_le x (T := T) (t := tOf l) fun i => Nat.lt_succ_iff.1 (l.2 i).2
    have hR1 : (1 : ℝ) ≤ 1 + R := by linarith [R.2]
    calc ‖expMonomial (τOf (n := n) l) (freq x (tOf l)) z‖
        ≤ (1 + ‖z‖) ^ (∑ v, τOf (n := n) l v) *
            Real.exp ((∑ v, ‖freq x (tOf l) v‖) * ‖z‖) := norm_expMonomial_le _ _ z
      _ ≤ (1 + (R : ℝ)) ^ (∑ v, τOf (n := n) l v) * Real.exp (T * Ax * R) :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith [hz.le]) _)
            (Real.exp_le_exp.2 (mul_le_mul hw hz.le (norm_nonneg _) (by positivity)))
            (by positivity) (by positivity)
      _ ≤ (1 + (R : ℝ)) ^ (d₀ * T) * Real.exp (T * Ax * R) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hR1 hτ) (by positivity)
  obtain ⟨p, hp0, hpN, hpF⟩ := ThueSiegel.exists_auxiliary_function (ι := Fin n)
    (by rw [Fintype.card_fin]; omega) hP hMφ hN hr0
    (by simpa [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul] using hMU)
    (by simpa using hW) hRr hRr' (by simpa [hcard] using hL)
  set F : (Fin n → ℂ) → ℂ := auxF x T fun l => (p l : ℂ) with hF
  have hFbound : ∀ z, ‖z‖ ≤ r → ‖F z‖ ≤ Real.exp (-U) := fun z hz => hpF z hz
  have hpC : ∀ l, ‖(p l : ℂ)‖ ≤ Real.exp N := fun l => by
    rw [Complex.norm_intCast]
    exact hpN l
  -- expansions, Liouville and Cauchy
  have hexp : ∀ (ξ : Fin n → ℂ) (ρ : NNReal), 0 < ρ →
      ∃ Q : FormalMultilinearSeries ℂ (Fin n → ℂ) ℂ,
        HasFPowerSeriesOnBall (fun h => F (ξ + h)) Q 0 ρ ∧
          ∀ σ, coeff Q σ = taylorCoeff F ξ σ := by
    intro ξ ρ hρ
    obtain ⟨Q, hQ, hQc⟩ := exists_hasFPowerSeriesOnBall_linComb (fun l => (p l : ℂ))
      (fun l => τOf (n := n) l) (fun l => freq x (tOf l)) ξ hρ
    exact ⟨Q, hQ, fun σ => by rw [hQc, hF]; exact (taylorCoeff_linComb _ _ _ ξ σ).symm⟩
  have hliou : ∀ s : Fin n → ℕ, (∀ j, s j ≤ S₁) → ∀ σ, taylorCoeff F (point y s) σ ≠ 0 →
      1 ≤ liouvilleFactor d₀ d₁ n T S₁ δ D N Hg (∑ v, σ v) *
        ‖taylorCoeff F (point y s) σ‖ := by
    intro s hs σ hne
    have h := one_le_taylorCoeff ι₀ hX hY hE hδ hHg hXs hYs hEs T S₁ p hpN s hs σ hne
    rw [hcard] at h
    refine h.trans (le_of_eq ?_)
    unfold liouvilleFactor
    push_cast
    ring
  have hcauchy : ∀ (ξ : Fin n → ℂ) (Mb : ℝ), (∀ h : Fin n → ℂ, ‖h‖ < 2 → ‖F (ξ + h)‖ ≤ Mb) →
      ∀ σ, ‖taylorCoeff F ξ σ‖ ≤ Mb := by
    intro ξ Mb hMb σ
    obtain ⟨Q, hQ, hQc⟩ := hexp ξ 2 (by norm_num)
    have := norm_coeff_mul_pow_le hQ (M := Mb) (fun h hh => hMb h (by exact_mod_cast hh)) σ
      zero_le_one (by norm_num)
    rwa [hQc, one_pow, mul_one] at this
  have hLF0 : ∀ M, 0 ≤ liouvilleFactor d₀ d₁ n T S₁ δ D N Hg M := fun M => by
    unfold liouvilleFactor
    have : (0 : ℝ) ≤ Hg := by linarith
    positivity
  -- step 4: vanishing to order `S₀` in each coordinate
  have hvan4 : ∀ s : Fin n → ℕ, (∀ j, s j < S₁) → ∀ σ : Fin n → ℕ, (∀ v, σ v < S₀) →
      taylorCoeff F (point y s) σ = 0 := by
    intro s hs σ hσ
    by_contra hne
    have hs' : ∀ j, s j ≤ S₁ := fun j => (hs j).le
    have h1 := hliou s hs' σ hne
    have hup : ‖taylorCoeff F (point y s) σ‖ ≤ Real.exp (-U) := hcauchy _ _ (fun h hh =>
      hFbound _ (calc ‖point y s + h‖ ≤ ‖point y s‖ + ‖h‖ := norm_add_le _ _
        _ ≤ S₁ * Ay + 2 := add_le_add (norm_point_le y hs') hh.le
        _ ≤ r := hr)) σ
    have hM : ∑ v, σ v ≤ n * S₀ := by
      calc ∑ v, σ v ≤ ∑ _v : Fin n, S₀ := Finset.sum_le_sum fun v _ => (hσ v).le
        _ = n * S₀ := by simp
    have h2 := hvan _ hM
    nlinarith [mul_le_mul_of_nonneg_left hup (hLF0 (∑ v, σ v))]
  -- step 5: the first nonvanishing order
  have hp0C : (fun l => (p l : ℂ)) ≠ 0 := by
    intro h
    apply hp0
    funext l
    have := congrFun h l
    simp only [Pi.zero_apply, Int.cast_eq_zero] at this
    simpa using this
  obtain ⟨σ₀, hσ₀⟩ := exists_taylorCoeff_ne_zero hd₀ hxli T hp0C
  have hpoint0 : point y (fun _ => 0) = 0 := by
    funext v
    simp [point]
  have hex : ∃ M, ∃ s : Fin n → ℕ, (∀ j, s j < S₁) ∧ ∃ σ : Fin n → ℕ, ∑ v, σ v = M ∧
      taylorCoeff F (point y s) σ ≠ 0 :=
    ⟨_, fun _ => 0, fun _ => hS₁, σ₀, rfl, by rw [hpoint0]; exact hσ₀⟩
  set M₀ := Nat.find hex with hM₀def
  obtain ⟨s₀, hs₀, σ₁, hσ₁M, hσ₁⟩ := Nat.find_spec hex
  have hmin : ∀ s : Fin n → ℕ, (∀ j, s j < S₁) → ∀ σ : Fin n → ℕ, ∑ v, σ v < M₀ →
      taylorCoeff F (point y s) σ = 0 := by
    intro s hs σ hσ
    by_contra hne
    exact Nat.find_min hex hσ ⟨s, hs, σ, rfl, hne⟩
  have hM₀S₀ : S₀ ≤ M₀ := by
    by_contra hlt
    push Not at hlt
    apply hσ₁
    refine hvan4 s₀ hs₀ σ₁ fun v => ?_
    have := Finset.single_le_sum (fun w _ => Nat.zero_le (σ₁ w)) (Finset.mem_univ v)
    rw [hσ₁M] at this
    omega
  -- step 6: the change of variables and Schwarz's lemma for Cartesian products
  have hYnorm : ∀ z : Fin n → ℂ, ‖Yl z‖ ≤ Ay * ‖z‖ := by
    intro z
    rw [hYl]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun v => ?_
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j, ‖z j * y j v‖ ≤ ∑ j, ‖z‖ * ∑ w, ‖y j w‖ := Finset.sum_le_sum fun j _ => by
          rw [norm_mul]
          exact mul_le_mul (norm_le_pi_norm z j)
            (Finset.single_le_sum (fun w _ => norm_nonneg (y j w)) (Finset.mem_univ v))
            (norm_nonneg _) (norm_nonneg _)
      _ = Ay * ‖z‖ := by rw [← Finset.mul_sum, mul_comm]
  have hYsymm : ∀ w : Fin n → ℂ, ‖Yl.symm w‖ ≤ B * ‖w‖ := fun w =>
    (Yl.symm : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)).le_opNorm w
  have hYs' : ∀ s : Fin n → ℕ, Yl (fun j => (s j : ℂ)) = point y s := fun s => by
    rw [hYl]
    rfl
  set f : (Fin n → ℂ) → ℂ := fun z => F (Yl z) with hfdef
  set m := M₀ / n with hm
  have hFan : ∀ z, AnalyticAt ℂ F z := fun z => by
    rw [hF]
    unfold auxF
    exact Finset.analyticAt_fun_sum _ fun l _ => analyticAt_const.mul (analyticAt_expMonomial _ _ z)
  have hfan : ∀ z, AnalyticAt ℂ f z := fun z =>
    (hFan (Yl z)).comp ((Yl : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)).analyticAt z)
  have hvanf : ∀ s : Fin n → ℕ, (∀ j, s j < S₁) → ∀ κ : Fin n → ℕ, (∀ v, κ v < m) →
      taylorCoeff f (fun j => (s j : ℂ)) κ = 0 := by
    intro s hs κ hκ
    obtain ⟨Q, hQ, hQc⟩ := hexp (point y s) 1 one_pos
    set zs : Fin n → ℂ := fun j => (s j : ℂ) with hzs
    have hQ0 : HasFPowerSeriesOnBall (fun h => F (point y s + h)) Q
        ((Yl : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) 0) 1 := by simpa using hQ
    have hQY := hQ0.compContinuousLinearMap
    have hfun : ((fun h => F (point y s + h)) ∘ (Yl : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))) =
        fun h => f (zs + h) := by
      funext h
      simp only [Function.comp_apply, hfdef, map_add, ContinuousLinearEquiv.coe_coe, hzs, hYs']
    rw [hfun] at hQY
    have hQat := hQY.comp_sub zs
    simp only [add_sub_cancel, zero_add] at hQat
    rw [taylorCoeff_eq hQat.hasFPowerSeriesAt]
    have hsum : ∑ v, κ v < M₀ := by
      have h1 : ∑ v, (κ v + 1) ≤ n * m := by
        calc ∑ v, (κ v + 1) ≤ ∑ _v : Fin n, m := Finset.sum_le_sum fun v _ => hκ v
          _ = n * m := by simp
      have h2 : n * m ≤ M₀ := by
        rw [hm, mul_comm]
        exact Nat.div_mul_le_self M₀ n
      have h3 : ∑ v, (κ v + 1) = ∑ v, κ v + n := by
        rw [Finset.sum_add_distrib]
        simp
      omega
    exact coeff_compContinuousLinearMap_eq_zero Q _ (k := ∑ v, κ v)
      (fun α hα => by rw [hQc]; exact hmin s hs α (hα ▸ hsum)) κ rfl
  set r' : ℝ := S₁ + 2 * B with hr'
  set R' : ℝ := 5 * 3 ^ n * Ep M₀ * r' with hR'
  set E₀ : Finset ℂ := (Finset.range S₁).image (fun k : ℕ => (k : ℂ)) with hE₀
  have hE₀card : E₀.card = S₁ := by
    rw [hE₀, Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  have hB0 : 0 ≤ B := norm_nonneg _
  have hS₁R : (1 : ℝ) ≤ S₁ := by exact_mod_cast hS₁
  have hr'1 : 1 ≤ r' := by rw [hr']; linarith
  have hEp1 := hEp M₀
  have h3n : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  have hR'0 : 0 < R' := by
    rw [hR']
    have : (0 : ℝ) < Ep M₀ := by linarith
    positivity
  have h5 : 5 * r' ≤ R' := by
    rw [hR']
    have h1 : (1 : ℝ) ≤ 3 ^ n * Ep M₀ := one_le_mul_of_one_le_of_one_le h3n hEp1
    nlinarith
  have hEr : ∀ i : Fin n, ∀ ζ ∈ E₀, ‖ζ‖ ≤ r' := by
    intro i ζ hζ
    rw [hE₀, Finset.mem_image] at hζ
    obtain ⟨k, hk, rfl⟩ := hζ
    rw [Complex.norm_natCast]
    have : (k : ℝ) ≤ S₁ := by exact_mod_cast (Finset.mem_range.1 hk).le
    linarith
  have hMf : ∀ z : Fin n → ℂ, ‖z‖ ≤ R' → ‖f z‖ ≤ growth d₀ d₁ T N Ax (Ay * R') := by
    intro z hz
    have h1 := norm_auxF_le x T hpC (Yl z)
    rw [hcard] at h1
    refine h1.trans ?_
    have hYz : ‖Yl z‖ ≤ Ay * R' := (hYnorm z).trans (mul_le_mul_of_nonneg_left hz hAy0)
    unfold growth
    gcongr
  have hvan' : ∀ ξ : Fin n → ℂ, (∀ i, ξ i ∈ E₀) → ∀ κ : Fin n → ℕ, (∀ i, κ i < m) →
      taylorCoeff f ξ κ = 0 := by
    intro ξ hξ κ hκ
    choose s hs hsξ using fun i => Finset.mem_image.1 (hξ i)
    have hξeq : ξ = fun j => (s j : ℂ) := funext fun j => (hsξ j).symm
    rw [hξeq]
    exact hvanf s (fun j => Finset.mem_range.1 (hs j)) κ hκ
  have : Nonempty (Fin n) := ⟨⟨0, hn1⟩⟩
  have hsmall : ∀ z : Fin n → ℂ, ‖z‖ ≤ r' →
      ‖f z‖ ≤ n * (1 / Ep M₀) ^ (m * S₁) * growth d₀ d₁ T N Ax (Ay * R') := by
    intro z hz
    have h := MultiIndex.norm_le_of_taylorCoeff_eq_zero_of_five_mul_le (E := fun _ => E₀)
      (S := S₁) (m := m) (fun _ => hE₀card) (by linarith) hR'0 h5 hEr (fun y _ => hfan y) hMf
      hvan' hz
    have hratio : 5 * 3 ^ Fintype.card (Fin n) * r' / R' = 1 / Ep M₀ := by
      rw [Fintype.card_fin, hR']
      have : (0 : ℝ) < Ep M₀ := by linarith
      field_simp
    rwa [hratio, Fintype.card_fin] at h
  -- the first nonvanishing coefficient is too small
  have hs₀' : ∀ j, s₀ j ≤ S₁ := fun j => (hs₀ j).le
  have hlow := hliou s₀ hs₀' σ₁ hσ₁
  rw [hσ₁M] at hlow
  have hup : ‖taylorCoeff F (point y s₀) σ₁‖ ≤
      n * (1 / Ep M₀) ^ (m * S₁) * growth d₀ d₁ T N Ax (Ay * R') := by
    refine hcauchy _ _ (fun h hh => ?_) σ₁
    have hw : point y s₀ + h = Yl ((fun j => (s₀ j : ℂ)) + Yl.symm h) := by
      rw [map_add, hYs', ContinuousLinearEquiv.apply_symm_apply]
    rw [hw]
    refine hsmall _ ?_
    have hzs : ‖(fun j => (s₀ j : ℂ))‖ ≤ S₁ :=
      (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => by
        rw [Complex.norm_natCast]
        exact_mod_cast hs₀' j
    calc ‖(fun j => (s₀ j : ℂ)) + Yl.symm h‖
        ≤ ‖(fun j => (s₀ j : ℂ))‖ + ‖Yl.symm h‖ := norm_add_le _ _
      _ ≤ S₁ + B * 2 := add_le_add hzs
          ((hYsymm h).trans (mul_le_mul_of_nonneg_left hh.le hB0))
      _ = r' := by rw [hr']; ring
  have hfinal := hbig M₀ hM₀S₀
  nlinarith [mul_le_mul_of_nonneg_left hup (hLF0 M₀)]

end Transcendental.SchneiderLangProof
