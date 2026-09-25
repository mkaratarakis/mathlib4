/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.NumberTheory.NumberField.House
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Valuation.Integral
public import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# Liouville's inequality and Schwarz's lemma at an ultrametric place

The two estimates that drive a `p`-adic transcendence proof.

* **Liouville's inequality.** A nonzero algebraic integer `x` of a number field `K` of degree `d`
  satisfies `1 ≤ house x ^ d * ‖σ x‖` for every embedding `σ` of `K` into an algebraically closed
  ultrametric field `L` in which a nonzero integer `n` has `1 ≤ |n| * ‖n‖`, such as `ℂ_[p]`.
  The proof is Waldschmidt's (*Diophantine Approximation on Linear Algebraic Groups*,
  Proposition 3.14, for an ultrametric place) specialised to algebraic integers: the norm of `x`
  is the product of its conjugates in `L`, each of norm at most one, and it is a nonzero integer.
* **Schwarz's lemma.** A power series vanishing to order `T` at the origin whose terms are
  bounded by `M` on the sphere of radius `r` is bounded by `M (‖z‖ / r) ^ T` inside it. In an
  ultrametric space this is immediate from the fact that the norm of a sum is at most the
  largest norm of its terms.

## Main statements

* `IsUltrametricDist.norm_le_one_of_isIntegral`: an element integral over `ℤ` has norm at most
  one in an ultrametric normed field.
* `PadicComplex.one_le_abs_mul_norm_intCast`: `1 ≤ |n| * ‖(n : ℂ_[p])‖` for a nonzero integer `n`.
* `NumberField.one_le_house_pow_mul_norm_embedding`: Liouville's inequality for an algebraic
  integer.
* `NumberField.one_le_pow_mul_norm_embedding`: the same for `x` with `δ ^ a * x` an algebraic
  integer of house at most `H`.
* `HasFPowerSeriesOnBall.norm_le_mul_div_pow_of_isUltrametricDist`: Schwarz's lemma.
-/

@[expose] public section

open NumberField

namespace IsUltrametricDist

variable {L : Type*} [NormedField L] [IsUltrametricDist L]

/-- An element integral over `ℤ` has norm at most one in an ultrametric normed field: the closed
unit ball is the valuation ring of the valuation `‖·‖₊`, which is integrally closed. -/
theorem norm_le_one_of_isIntegral {x : L} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have hv := Valuation.integer.integers (NormedField.valuation (K := L))
  have h : IsIntegral (NormedField.valuation (K := L)).integer x := hx.tower_top
  have := hv.isIntegral_iff_v_le_one.mp h
  rw [NormedField.valuation_apply] at this
  exact_mod_cast this

end IsUltrametricDist

namespace PadicComplex

variable {p : ℕ} [Fact p.Prime]

/-- A nonzero integer `n` has `p`-adic norm at least `1 / |n|`. -/
theorem one_le_abs_mul_norm_intCast {n : ℤ} (hn : n ≠ 0) : 1 ≤ |(n : ℝ)| * ‖(n : ℂ_[p])‖ := by
  have hcast : ((n : ℚ_[p]) : ℂ_[p]) = (n : ℂ_[p]) := by
    rw [map_intCast, PadicComplex.coe_eq, map_intCast]
  rw [← hcast, norm_extends', Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hn),
    Padic.valuation_intCast]
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hdvd : (p : ℤ) ^ padicValInt p n ∣ n := padicValInt_dvd n
  have hle : ((p : ℝ) ^ padicValInt p n) ≤ |(n : ℝ)| := by
    have := Int.le_of_dvd (abs_pos.mpr hn) ((dvd_abs _ _).mpr hdvd)
    exact_mod_cast this
  rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
  exact hle

end PadicComplex

namespace NumberField

variable {L : Type*} [NormedField L] [IsUltrametricDist L] [IsAlgClosed L] [CharZero L]
  {K : Type*} [Field K] [NumberField K]

/-- **Liouville's inequality at an ultrametric place.** A nonzero algebraic integer `x` of a
number field of degree `d` satisfies `1 ≤ house x ^ d * ‖σ x‖` at every embedding `σ` of the field
into `L`, provided nonzero integers `n` have `1 ≤ |n| * ‖n‖` in `L`. -/
theorem one_le_house_pow_mul_norm_embedding
    (hL : ∀ n : ℤ, n ≠ 0 → 1 ≤ |(n : ℝ)| * ‖(n : L)‖) {x : K} (hx : IsIntegral ℤ x)
    (hx0 : x ≠ 0) (σ : K →+* L) : 1 ≤ house x ^ Module.finrank ℚ K * ‖σ x‖ := by
  classical
  obtain ⟨a, rfl⟩ : ∃ a : 𝓞 K, (a : K) = x := ⟨⟨x, hx⟩, rfl⟩
  set n : ℤ := Algebra.norm ℤ a with hn
  have hn0 : n ≠ 0 := by
    rw [hn, Ne, Algebra.norm_eq_zero_iff]
    exact fun h => hx0 (by rw [h]; rfl)
  have hnorm : (n : ℚ) = Algebra.norm ℚ (a : K) := by
    rw [hn, ← Algebra.coe_norm_int]
  -- the norm is the product of the conjugates of `(a : K)` in `L`
  have hprod : (n : L) = ∏ τ : K →ₐ[ℚ] L, τ (a : K) := by
    rw [← Algebra.norm_eq_prod_embeddings ℚ L (a : K), ← hnorm, map_intCast]
  -- each conjugate has norm at most one, so the product has norm at most `‖σ (a : K)‖`
  have hconj : ∀ τ : K →ₐ[ℚ] L, ‖τ (a : K)‖ ≤ 1 := fun τ =>
    IsUltrametricDist.norm_le_one_of_isIntegral (hx.map τ)
  have hσ : ‖(n : L)‖ ≤ ‖σ (a : K)‖ := by
    rw [hprod, norm_prod, ← Finset.mul_prod_erase Finset.univ (fun τ => ‖τ (a : K)‖)
      (Finset.mem_univ σ.toRatAlgHom)]
    calc ‖σ.toRatAlgHom (a : K)‖ * ∏ τ ∈ Finset.univ.erase σ.toRatAlgHom, ‖τ (a : K)‖
        ≤ ‖σ.toRatAlgHom (a : K)‖ * 1 := by
          gcongr
          exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun τ _ => hconj τ
      _ = ‖σ (a : K)‖ := by rw [mul_one]; rfl
  -- and the norm, an integer, is at most `house (a : K) ^ d` in absolute value
  have hhouse : |(n : ℝ)| ≤ house (a : K) ^ Module.finrank ℚ K := by
    let φ : K →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := K) (M := ℂ)).toRingHom
    have h1 := norm_norm_le_norm_mul_house_pow (a : K) φ
    have h2 := norm_embedding_le_house (a : K) φ
    have h3 : ‖Algebra.norm ℚ (a : K)‖ = |(n : ℝ)| := by
      rw [← hnorm, ← Rat.norm_cast_real, Rat.cast_intCast, Real.norm_eq_abs]
    rw [← h3]
    calc ‖Algebra.norm ℚ (a : K)‖ ≤ ‖φ (a : K)‖ * house (a : K) ^ (Module.finrank ℚ K - 1) := h1
      _ ≤ house (a : K) * house (a : K) ^ (Module.finrank ℚ K - 1) :=
          mul_le_mul_of_nonneg_right h2 (pow_nonneg (house_nonneg _) _)
      _ = house (a : K) ^ Module.finrank ℚ K := by
          rw [← pow_succ', Nat.sub_add_cancel Module.finrank_pos]
  calc (1 : ℝ) ≤ |(n : ℝ)| * ‖(n : L)‖ := hL n hn0
    _ ≤ house (a : K) ^ Module.finrank ℚ K * ‖σ (a : K)‖ :=
        mul_le_mul hhouse hσ (norm_nonneg _) (pow_nonneg (house_nonneg _) _)

/-- **Liouville's inequality for a number of known size, at an ultrametric place.** If `δ ^ a * x`
is a nonzero algebraic integer of house at most `H`, then `1 ≤ H ^ d * ‖σ x‖`. Unlike the
Archimedean case, the denominator costs nothing: `‖δ‖ ≤ 1`. -/
theorem one_le_pow_mul_norm_embedding
    (hL : ∀ n : ℤ, n ≠ 0 → 1 ≤ |(n : ℝ)| * ‖(n : L)‖) {δ a : ℕ} {x : K} {H : ℝ}
    (hint : IsIntegral ℤ ((δ : K) ^ a * x)) (hH : house ((δ : K) ^ a * x) ≤ H)
    (hδ : δ ≠ 0) (hx0 : x ≠ 0) (σ : K →+* L) : 1 ≤ H ^ Module.finrank ℚ K * ‖σ x‖ := by
  have hy0 : (δ : K) ^ a * x ≠ 0 := mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hδ)) hx0
  have h := one_le_house_pow_mul_norm_embedding hL hint hy0 σ
  have hδ1 : ‖σ ((δ : K) ^ a * x)‖ ≤ ‖σ x‖ := by
    rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow]
    calc ‖(δ : L)‖ ^ a * ‖σ x‖ ≤ 1 ^ a * ‖σ x‖ := by
          gcongr
          exact IsUltrametricDist.norm_natCast_le_one L δ
      _ = ‖σ x‖ := by rw [one_pow, one_mul]
  have hH0 : 0 ≤ H := (house_nonneg _).trans hH
  calc (1 : ℝ) ≤ house ((δ : K) ^ a * x) ^ Module.finrank ℚ K * ‖σ ((δ : K) ^ a * x)‖ := h
    _ ≤ H ^ Module.finrank ℚ K * ‖σ x‖ :=
        mul_le_mul (pow_le_pow_left₀ (house_nonneg _) hH _) hδ1 (norm_nonneg _)
          (pow_nonneg hH0 _)

end NumberField

namespace HasFPowerSeriesOnBall

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]

/-- **Schwarz's lemma in an ultrametric space.** If `f` has the power series `p` on a ball about
`0`, the terms `p n` of degree `< T` vanish, and `‖p n‖ r ^ n ≤ M` for all `n`, then
`‖f z‖ ≤ M (‖z‖ / r) ^ T` whenever `‖z‖ ≤ r` and `z` lies in the ball. -/
theorem norm_le_mul_div_pow_of_isUltrametricDist {f : E → F}
    {p : FormalMultilinearSeries 𝕜 E F} {R : ENNReal} (hf : HasFPowerSeriesOnBall f p 0 R)
    {T : ℕ} (hT : ∀ n < T, p n = 0) {r M : ℝ} (hr : 0 < r) (hM : ∀ n, ‖p n‖ * r ^ n ≤ M)
    {z : E} (hzr : ‖z‖ ≤ r) (hzR : z ∈ Metric.eball (0 : E) R) :
    ‖f z‖ ≤ M * (‖z‖ / r) ^ T := by
  have hM0 : 0 ≤ M := (mul_nonneg (norm_nonneg _) (pow_nonneg hr.le 0)).trans (hM 0)
  have hq0 : 0 ≤ ‖z‖ / r := div_nonneg (norm_nonneg _) hr.le
  have hq1 : ‖z‖ / r ≤ 1 := (div_le_one hr).mpr hzr
  have hsum := hf.hasSum hzR
  simp only [zero_add] at hsum
  rw [← hsum.tsum_eq]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (mul_nonneg hM0 (pow_nonneg hq0 T)) fun n => ?_
  rcases lt_or_ge n T with hn | hn
  · rw [hT n hn]
    simpa using mul_nonneg hM0 (pow_nonneg hq0 T)
  · calc ‖p n (fun _ => z)‖ ≤ ‖p n‖ * ∏ _i : Fin n, ‖z‖ := (p n).le_opNorm _
      _ = ‖p n‖ * r ^ n * (‖z‖ / r) ^ n := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_pow, mul_assoc,
            mul_div_cancel₀ _ (pow_ne_zero n hr.ne')]
      _ ≤ M * (‖z‖ / r) ^ n := by gcongr; exact hM n
      _ ≤ M * (‖z‖ / r) ^ T := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq0 hq1 hn) hM0

end HasFPowerSeriesOnBall
