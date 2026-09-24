/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.NumberTheory.Transcendental.Baker.Interpolation
public import Mathlib.NumberTheory.Transcendental.Baker.ThueSiegel

/-!
# Construction of an auxiliary function

Given entire functions `φ₁, …, φ_L` on `ℂⁿ` whose moduli on the polydisc of radius `R` add up to
at most `e ^ U`, there are rational integers `p₁, …, p_L`, not all zero and of modulus at most
`e ^ N`, such that `F = p₁ φ₁ + ⋯ + p_L φ_L` has modulus at most `e ^ (-V)` on the polydisc of
radius `r`, provided the number `L` of functions is large enough compared with
`W = N + U + V` and `log (R / r)`.  This is Proposition 4.10 of Waldschmidt, *Diophantine
Approximation on Linear Algebraic Groups*.

The integers are found by Thue-Siegel's lemma (`ThueSiegel.exists_int_vec_norm_le_of_pow_le`),
applied to the Taylor coefficients of degree `< T` at the origin, which makes the Taylor
polynomial of `F` small; truncated Taylor interpolation
(`MultiIndex.norm_le_of_hasFPowerSeriesOnBall`) then makes `F` itself small.

## Main statements

* `ThueSiegel.exists_auxiliary_function`: Proposition 4.10.
-/

@[expose] public section

open Real Finset
open scoped NNReal

/-!
### Two elementary inequalities
-/

/-- `3 (y² + 1) < eʸ` for `y ≥ 4`.  At `y = 4` this reads `51 < e⁴ ≈ 54.6`. -/
lemma three_mul_sq_add_one_lt_exp {y : ℝ} (hy : 4 ≤ y) : 3 * (y ^ 2 + 1) < exp y := by
  have h4 : (54.5 : ℝ) < exp 4 := by
    have h := pow_lt_pow_left₀ exp_one_gt_d9 (by norm_num) (four_ne_zero (α := ℕ))
    rw [exp_one_pow] at h
    norm_num at h ⊢
    linarith
  have ht : 0 ≤ y - 4 := by linarith
  have hq := quadratic_le_exp_of_nonneg ht
  have hsplit : exp y = exp 4 * exp (y - 4) := by rw [← exp_add]; ring_nf
  rw [hsplit]
  nlinarith [exp_pos 4, sq_nonneg (y - 4)]

/-- `3 ((4/3) W + 1) ^ n < e ^ (W / 3)` whenever `n ≥ 1` and `W ≥ 12 n²`.  This is the
inequality behind the choice of parameters in Proposition 4.10. -/
lemma three_mul_pow_lt_exp {n : ℕ} (hn : 1 ≤ n) {W : ℝ} (hW : 12 * (n : ℝ) ^ 2 ≤ W) :
    3 * (4 / 3 * W + 1) ^ n < exp (W / 3) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set y : ℝ := W / (3 * n) with hy
  have hWy : W = 3 * n * y := by rw [hy]; field_simp
  have hy4n : 4 * n ≤ y := by
    rw [hy, le_div_iff₀ (by positivity)]
    nlinarith
  have hy4 : 4 ≤ y := by nlinarith
  have hbase : 4 / 3 * W + 1 ≤ y ^ 2 + 1 := by rw [hWy]; nlinarith
  have hW0 : 0 ≤ 4 / 3 * W + 1 := by nlinarith
  calc 3 * (4 / 3 * W + 1) ^ n ≤ 3 ^ n * (y ^ 2 + 1) ^ n :=
        mul_le_mul (le_self_pow₀ (by norm_num) (by omega)) (pow_le_pow_left₀ hW0 hbase n)
          (by positivity) (by positivity)
    _ = (3 * (y ^ 2 + 1)) ^ n := by rw [mul_pow]
    _ < exp y ^ n :=
        pow_lt_pow_left₀ (three_mul_sq_add_one_lt_exp hy4) (by positivity) (by omega)
    _ = exp (W / 3) := by
        rw [← exp_nat_mul, hWy]
        congr 1
        field_simp

/-!
### Linear combinations of power series
-/

section LinearCombination

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E W : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup W] [NormedSpace 𝕜 W] {Λ : Type*}

/-- A finite linear combination of functions with power series on a common ball has the
corresponding linear combination of power series there. -/
theorem hasFPowerSeriesOnBall_finset_sum_smul (s : Finset Λ) (c : Λ → 𝕜) {φ : Λ → E → W}
    {P : Λ → FormalMultilinearSeries 𝕜 E W} {x : E} {r : ENNReal} (hr : 0 < r)
    (h : ∀ l ∈ s, HasFPowerSeriesOnBall (φ l) (P l) x r) :
    HasFPowerSeriesOnBall (fun y => ∑ l ∈ s, c l • φ l y) (∑ l ∈ s, c l • P l) x r := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 := (hasFPowerSeriesOnBall_const (𝕜 := 𝕜) (c := (0 : W)) (e := x)).mono hr le_top
    rwa [constFormalMultilinearSeries_zero] at h0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact ((h a (Finset.mem_insert_self a s)).const_smul (c := c a)).add
      (ih fun l hl => h l (Finset.mem_insert_of_mem hl))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace MultiIndex

@[simp] lemma coeff_zero (α : ι → ℕ) : coeff (0 : FormalMultilinearSeries 𝕜 (ι → 𝕜) W) α = 0 := by
  simp [coeff, coeffAt]

@[simp] lemma coeff_add (p q : FormalMultilinearSeries 𝕜 (ι → 𝕜) W) (α : ι → ℕ) :
    coeff (p + q) α = coeff p α + coeff q α := by
  simp [coeff, coeffAt, Finset.sum_add_distrib]

@[simp] lemma coeff_smul (c : 𝕜) (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) W) (α : ι → ℕ) :
    coeff (c • p) α = c • coeff p α := by
  simp [coeff, coeffAt, Finset.smul_sum]

/-- The multi-index coefficients depend linearly on the series. -/
lemma coeff_finset_sum_smul (s : Finset Λ) (c : Λ → 𝕜)
    (P : Λ → FormalMultilinearSeries 𝕜 (ι → 𝕜) W) (α : ι → ℕ) :
    coeff (∑ l ∈ s, c l • P l) α = ∑ l ∈ s, c l • coeff (P l) α := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

end MultiIndex

end LinearCombination

/-- `(8/3) (3/2) ^ n ≤ 2 ^ (n + 1)` for `n ≥ 1`. -/
lemma eight_thirds_mul_pow_le {n : ℕ} (hn : 1 ≤ n) : (8 / 3 : ℝ) * (3 / 2) ^ n ≤ 2 ^ (n + 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 2) (by norm_num : (3 / 2 : ℝ) ≤ 2) m
  rw [pow_succ, pow_succ, pow_succ]
  nlinarith

namespace ThueSiegel

variable {ι Λ : Type*} [Fintype ι] [Fintype Λ]

/-- **Construction of an auxiliary function** (Proposition 4.10 of [waldschmidt2000]).

Let `φ_λ` (`λ ∈ Λ`, `L = card Λ` of them) have power series on the polydisc of polyradius `R`
in `ℂⁿ`, with `‖φ_λ‖ ≤ M_λ` there and `∑ M_λ ≤ e ^ U`.  Put `W = N + U + V` and assume
`W ≥ 12 n²`, `e ≤ R / r ≤ e ^ (W / 6)` and `(2W) ^ (n + 1) ≤ L N (log (R / r)) ^ n`.  Then there
are rational integers `p_λ`, not all zero, with `|p_λ| ≤ e ^ N`, such that
`F = ∑ p_λ φ_λ` satisfies `‖F‖ ≤ e ^ (-V)` on the polydisc of polyradius `r`. -/
theorem exists_auxiliary_function (hι : 0 < Fintype.card ι)
    {φ : Λ → (ι → ℂ) → ℂ} {P : Λ → FormalMultilinearSeries ℂ (ι → ℂ) ℂ} {R : ℝ≥0}
    (hφ : ∀ l, HasFPowerSeriesOnBall (φ l) (P l) 0 R)
    {M : Λ → ℝ} (hM : ∀ l (y : ι → ℂ), ‖y‖ < R → ‖φ l y‖ ≤ M l)
    {N U V r : ℝ} (hN : 0 < N) (hr : 0 < r) (hMU : ∑ l, M l ≤ exp U)
    (hW : 12 * (Fintype.card ι : ℝ) ^ 2 ≤ N + U + V)
    (hRr : exp 1 ≤ R / r) (hRr' : R / r ≤ exp ((N + U + V) / 6))
    (hL : (2 * (N + U + V)) ^ (Fintype.card ι + 1) ≤
      Fintype.card Λ * N * log (R / r) ^ Fintype.card ι) :
    ∃ p : Λ → ℤ, p ≠ 0 ∧ (∀ l, |(p l : ℝ)| ≤ exp N) ∧
      ∀ z : ι → ℂ, ‖z‖ ≤ r → ‖∑ l, (p l : ℂ) * φ l z‖ ≤ exp (-V) := by
  classical
  set n := Fintype.card ι with hn
  set L := Fintype.card Λ with hLdef
  set W := N + U + V with hWdef
  set ℓ := log (R / r) with hℓ
  have hn1 : 1 ≤ n := hι
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  -- the radii
  have hRr0 : 0 < R / r := (exp_pos 1).trans_le hRr
  have hR0 : (0 : ℝ) < R := by
    have := mul_pos hRr0 hr
    rwa [div_mul_cancel₀ _ hr.ne'] at this
  have hrR : r < R := by
    have h2 : (1 : ℝ) < R / r := by linarith [add_one_lt_exp (one_ne_zero (α := ℝ))]
    exact (one_lt_div hr).1 h2
  have hℓ1 : 1 ≤ ℓ := (le_log_iff_exp_le hRr0).2 hRr
  have hℓ0 : 0 < ℓ := one_pos.trans_le hℓ1
  have hℓW : ℓ ≤ W / 6 := (log_le_iff_le_exp hRr0).2 hRr'
  have hW12 : 12 ≤ W := by nlinarith
  have hW0 : 0 < W := by linarith
  -- the number `T` of Taylor coefficients to kill: `(4/3) W ≤ T ℓ < (3/2) W`
  set T : ℕ := ⌈4 / 3 * W / ℓ⌉₊ with hT
  have hTℓ : 4 / 3 * W ≤ T * ℓ := by
    have := Nat.le_ceil (4 / 3 * W / ℓ)
    rwa [div_le_iff₀ hℓ0] at this
  have hTlt : (T : ℝ) < 4 / 3 * W / ℓ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hTℓ' : T * ℓ ≤ 3 / 2 * W := by
    calc (T : ℝ) * ℓ ≤ (4 / 3 * W / ℓ + 1) * ℓ := by gcongr
      _ = 4 / 3 * W + ℓ := by field_simp
      _ ≤ 3 / 2 * W := by linarith
  have hTW : (T : ℝ) ≤ 4 / 3 * W + 1 := by
    have : 4 / 3 * W / ℓ ≤ 4 / 3 * W := div_le_self (by positivity) hℓ1
    linarith
  have hT8 : (8 : ℝ) ≤ T := by
    have h6 : 8 ≤ 4 / 3 * W / ℓ := by
      rw [le_div_iff₀ hℓ0]
      linarith
    exact h6.trans (Nat.le_ceil _)
  have hT1 : 1 ≤ T := by exact_mod_cast (by linarith : (1 : ℝ) ≤ T)
  have hTn0 : (0 : ℝ) < (T : ℝ) ^ n := by positivity
  have hTn1 : (1 : ℝ) ≤ (T : ℝ) ^ n := one_le_pow₀ (by exact_mod_cast hT1)
  have h3T : 3 * (T : ℝ) ^ n < exp (W / 3) :=
    calc 3 * (T : ℝ) ^ n ≤ 3 * (4 / 3 * W + 1) ^ n := by gcongr
      _ < exp (W / 3) := three_mul_pow_lt_exp hn1 hW
  -- the multi-indices of degree `< T`
  set S : Finset (ι → ℕ) :=
    (Finset.range T).biUnion fun k => (Finset.univ : Finset ι).piAntidiag k with hS
  have hSsub : S ⊆ Fintype.piFinset fun _ : ι => Finset.range T := by
    intro α hα
    simp only [hS, Finset.mem_biUnion, Finset.mem_range, Finset.mem_piAntidiag] at hα
    obtain ⟨k, hk, hαk, -⟩ := hα
    simp only [Fintype.mem_piFinset, Finset.mem_range]
    intro i
    have hαk' : ∑ j, α j = k := hαk
    have := Finset.single_le_sum (fun j _ => Nat.zero_le (α j)) (Finset.mem_univ i)
    omega
  have hScard : S.card ≤ T ^ n :=
    (Finset.card_le_card hSsub).trans (by simp [Fintype.card_piFinset, hn])
  have hSdisj : (↑(Finset.range T) : Set ℕ).PairwiseDisjoint
      fun k => (Finset.univ : Finset ι).piAntidiag k := by
    intro a _ b _ hab
    refine Finset.disjoint_left.2 fun α ha hb => hab ?_
    rw [Finset.mem_piAntidiag] at ha hb
    rw [← ha.1, ← hb.1]
  -- the linear forms: Taylor coefficients of degree `< T`, scaled to the radius `r`
  set u : Λ → S → ℂ := fun l τ =>
    MultiIndex.coeff (P l) (τ : ι → ℕ) * (r : ℂ) ^ (∑ i, (τ : ι → ℕ) i) with hu
  have hMnn : ∀ l, 0 ≤ M l := fun l => (norm_nonneg _).trans (hM l 0 (by simpa using hR0))
  have hU' : ∀ τ : S, ∑ l, ‖u l τ‖ ≤ exp U := by
    intro τ
    refine (Finset.sum_le_sum fun l _ => ?_).trans hMU
    rw [hu, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.le]
    exact MultiIndex.norm_coeff_mul_pow_le (hφ l) (hM l) _ hr.le hrR
  -- the size of the integers
  set X : ℕ := ⌊exp N⌋₊ with hXdef
  have hX1 : 1 ≤ X := Nat.le_floor (by rw [Nat.cast_one]; exact one_le_exp hN.le)
  have hXle : (X : ℝ) ≤ exp N := Nat.floor_le (exp_pos N).le
  have hXlt : exp N < X + 1 := Nat.lt_floor_add_one _
  -- Thue-Siegel with `V' = V + log (2 T ^ n)`
  set V' : ℝ := V + log (2 * (T : ℝ) ^ n) with hV'
  have hexpUV' : exp (U + V') = 2 * (T : ℝ) ^ n * exp (U + V) := by
    rw [show U + V' = (U + V) + log (2 * (T : ℝ) ^ n) by rw [hV']; ring, exp_add,
      exp_log (by positivity)]
    ring
  have h83 : 8 / 3 * W * (T : ℝ) ^ n ≤ L * N := by
    have hkey : 8 / 3 * W * (T : ℝ) ^ n * ℓ ^ n ≤ L * N * ℓ ^ n := by
      calc 8 / 3 * W * (T : ℝ) ^ n * ℓ ^ n = 8 / 3 * W * ((T : ℝ) * ℓ) ^ n := by
            rw [mul_pow]; ring
        _ ≤ 8 / 3 * W * (3 / 2 * W) ^ n := by gcongr
        _ = (8 / 3 * (3 / 2) ^ n) * W ^ (n + 1) := by rw [mul_pow, pow_succ]; ring
        _ ≤ 2 ^ (n + 1) * W ^ (n + 1) := by gcongr; exact eight_thirds_mul_pow_le hn1
        _ = (2 * W) ^ (n + 1) := by rw [mul_pow]
        _ ≤ L * N * ℓ ^ n := hL
    exact le_of_mul_le_mul_right hkey (by positivity)
  have hL0 : 0 < L := by
    have hpos : (0 : ℝ) < (2 * W) ^ (n + 1) := by positivity
    refine Nat.pos_of_ne_zero fun h => ?_
    rw [h] at hL
    simp only [Nat.cast_zero, zero_mul] at hL
    linarith
  have hcard : (Real.sqrt 2 * X * exp (U + V') + 1) ^ (2 * Fintype.card S)
      ≤ ((X : ℝ) + 1) ^ L := by
    set B := Real.sqrt 2 * X * exp (U + V') + 1 with hB
    have hB1 : 1 ≤ B := by
      have : 0 ≤ Real.sqrt 2 * X * exp (U + V') := by positivity
      rw [hB]
      linarith
    have hs2 : Real.sqrt 2 < 1.415 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    have hA : 13 ≤ (T : ℝ) ^ n * exp W := by
      have := add_one_le_exp W
      nlinarith
    have hBle : B ≤ exp (4 / 3 * W) := by
      calc B = 2 * Real.sqrt 2 * X * (T : ℝ) ^ n * exp (U + V) + 1 := by rw [hB, hexpUV']; ring
        _ ≤ 2 * Real.sqrt 2 * exp N * (T : ℝ) ^ n * exp (U + V) + 1 := by gcongr
        _ = 2 * Real.sqrt 2 * ((T : ℝ) ^ n * exp W) + 1 := by
            rw [hWdef, show N + U + V = N + (U + V) by ring, exp_add N (U + V)]; ring
        _ ≤ 3 * ((T : ℝ) ^ n * exp W) := by
            have hA0 : (0 : ℝ) ≤ (T : ℝ) ^ n * exp W := by positivity
            nlinarith [mul_le_mul_of_nonneg_right hs2.le hA0]
        _ ≤ exp (W / 3) * exp W := by
            rw [← mul_assoc]; gcongr
        _ = exp (4 / 3 * W) := by rw [← exp_add]; ring_nf
    have hSc : 2 * Fintype.card S ≤ 2 * T ^ n := by
      rw [Fintype.card_coe]; omega
    calc B ^ (2 * Fintype.card S) ≤ B ^ (2 * T ^ n) := pow_le_pow_right₀ hB1 hSc
      _ ≤ exp (4 / 3 * W) ^ (2 * T ^ n) := pow_le_pow_left₀ (by linarith) hBle _
      _ = exp (8 / 3 * W * (T : ℝ) ^ n) := by
          rw [← exp_nat_mul]; push_cast; ring_nf
      _ ≤ exp (L * N) := exp_le_exp.2 h83
      _ = exp N ^ L := by rw [← exp_nat_mul]
      _ ≤ ((X : ℝ) + 1) ^ L := pow_le_pow_left₀ (exp_pos N).le hXlt.le L
  obtain ⟨ξ, hξ0, hξX, hξ⟩ := exists_int_vec_norm_le_of_pow_le u hU' hX1 hL0 hcard
  refine ⟨ξ, hξ0, fun l => ?_, fun z hz => ?_⟩
  · have h := hξX l
    calc |(ξ l : ℝ)| = ((|ξ l| : ℤ) : ℝ) := by rw [Int.cast_abs]
      _ ≤ X := by exact_mod_cast h
      _ ≤ exp N := hXle
  -- the auxiliary function and its power series
  set F : (ι → ℂ) → ℂ := fun y => ∑ l, (ξ l : ℂ) • φ l y with hFdef
  have hF : HasFPowerSeriesOnBall F (∑ l, (ξ l : ℂ) • P l) 0 R :=
    hasFPowerSeriesOnBall_finset_sum_smul Finset.univ (fun l => (ξ l : ℂ))
      (ENNReal.coe_pos.2 (by exact_mod_cast hR0)) fun l _ => hφ l
  have hξN : ∀ l, ‖(ξ l : ℂ)‖ ≤ exp N := fun l => by
    have h := hξX l
    rw [Complex.norm_intCast]
    calc |(ξ l : ℝ)| = ((|ξ l| : ℤ) : ℝ) := by rw [Int.cast_abs]
      _ ≤ X := by exact_mod_cast h
      _ ≤ exp N := hXle
  have hFM : ∀ y : ι → ℂ, ‖y‖ < R → ‖F y‖ ≤ exp (N + U) := by
    intro y hy
    calc ‖F y‖ ≤ ∑ l, ‖(ξ l : ℂ) • φ l y‖ := norm_sum_le _ _
      _ ≤ ∑ l, exp N * M l := by
          refine Finset.sum_le_sum fun l _ => ?_
          rw [norm_smul]
          exact mul_le_mul (hξN l) (hM l y hy) (norm_nonneg _) (exp_pos N).le
      _ = exp N * ∑ l, M l := by rw [Finset.mul_sum]
      _ ≤ exp N * exp U := by gcongr
      _ = exp (N + U) := by rw [exp_add]
  have h413 := MultiIndex.norm_le_of_hasFPowerSeriesOnBall hF hFM T hrR hz
  -- the remainder term
  have hterm1 : (1 + T) * exp (N + U) * (r / R) ^ T ≤ exp (-V) / 2 := by
    have hrR' : r / R = exp (-ℓ) := by
      rw [exp_neg, hℓ, exp_log hRr0, inv_div]
    have hpow : (r / R) ^ T ≤ exp (-(4 / 3 * W)) := by
      rw [hrR', ← exp_nat_mul]
      exact exp_le_exp.2 (by linarith)
    have hTTn : (T : ℝ) ≤ (T : ℝ) ^ n := le_self_pow₀ (by exact_mod_cast hT1) (by omega)
    have h1T : 1 + (T : ℝ) ≤ exp (W / 3) / 2 := by linarith [exp_pos (W / 3)]
    calc (1 + T) * exp (N + U) * (r / R) ^ T
        ≤ exp (W / 3) / 2 * exp (N + U) * exp (-(4 / 3 * W)) := by gcongr
      _ = exp (W / 3 + (N + U) + -(4 / 3 * W)) / 2 := by
          rw [exp_add (W / 3 + (N + U)), exp_add (W / 3)]; ring
      _ = exp (-V) / 2 := by rw [hWdef]; ring_nf
  -- the Taylor polynomial term
  have hterm2 : ∑ k ∈ Finset.range T, ∑ α ∈ (Finset.univ : Finset ι).piAntidiag k,
      ‖MultiIndex.coeff (∑ l, (ξ l : ℂ) • P l) α‖ * r ^ k ≤ exp (-V) / 2 := by
    have hterm : ∀ α : ι → ℕ,
        ‖MultiIndex.coeff (∑ l, (ξ l : ℂ) • P l) α‖ * r ^ (∑ i, α i)
          = ‖∑ l, MultiIndex.coeff (P l) α * (r : ℂ) ^ (∑ i, α i) * (ξ l : ℂ)‖ := by
      intro α
      rw [show ‖MultiIndex.coeff (∑ l, (ξ l : ℂ) • P l) α‖ * r ^ (∑ i, α i)
          = ‖MultiIndex.coeff (∑ l, (ξ l : ℂ) • P l) α * (r : ℂ) ^ (∑ i, α i)‖ by
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.le],
        MultiIndex.coeff_finset_sum_smul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_eq_mul]
      ring
    have hconv : ∑ k ∈ Finset.range T, ∑ α ∈ (Finset.univ : Finset ι).piAntidiag k,
        ‖MultiIndex.coeff (∑ l, (ξ l : ℂ) • P l) α‖ * r ^ k
        = ∑ τ : S, ‖∑ l, u l τ * (ξ l : ℂ)‖ := by
      calc ∑ k ∈ Finset.range T, ∑ α ∈ (Finset.univ : Finset ι).piAntidiag k,
            ‖MultiIndex.coeff (∑ l, (ξ l : ℂ) • P l) α‖ * r ^ k
          = ∑ α ∈ S, ‖MultiIndex.coeff (∑ l, (ξ l : ℂ) • P l) α‖ * r ^ (∑ i, α i) := by
            rw [hS, Finset.sum_biUnion hSdisj]
            refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun α hα => ?_
            rw [Finset.mem_piAntidiag] at hα
            rw [← hα.1]
        _ = ∑ τ : S, ‖MultiIndex.coeff (∑ l, (ξ l : ℂ) • P l) (τ : ι → ℕ)‖ *
              r ^ (∑ i, (τ : ι → ℕ) i) := (Finset.sum_coe_sort S _).symm
        _ = _ := Finset.sum_congr rfl fun τ _ => by rw [hterm, hu]
    have hV'e : exp (-V') = exp (-V) / (2 * (T : ℝ) ^ n) := by
      rw [hV', neg_add, exp_add, exp_neg (log _), exp_log (by positivity), div_eq_mul_inv]
    rw [hconv]
    calc ∑ τ : S, ‖∑ l, u l τ * (ξ l : ℂ)‖ ≤ ∑ _τ : S, exp (-V') :=
          Finset.sum_le_sum fun τ _ => hξ τ
      _ = Fintype.card S * exp (-V') := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ ≤ (T : ℝ) ^ n * exp (-V') := by
          gcongr
          rw [Fintype.card_coe]
          exact_mod_cast hScard
      _ = exp (-V) / 2 := by rw [hV'e]; field_simp
  have hFz : ∑ l, (ξ l : ℂ) * φ l z = F z := by simp [hFdef, smul_eq_mul]
  rw [hFz]
  linarith

end ThueSiegel
