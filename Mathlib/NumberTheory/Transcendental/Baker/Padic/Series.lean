/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Ring.Ultra
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Power series with many zeros in an ultrametric field

A power series `c` over a complete ultrametric field `K` is recorded by its coefficient sequence
`c : ℕ → K`; its value at `x` is `PadicBaker.seqEval c x = ∑' k, c k * x ^ k` and its formal
derivative is `PadicBaker.seqDeriv c`. The bound `‖c k‖ * r ^ k ≤ M` for some `r > 1` makes the
series converge on the closed unit disc, and so on the integers.

The main result is the ultrametric replacement for the maximum-modulus step of Baker's
extrapolation (Baker–Masser, *Transcendental Number Theory*, Chapter 2, Lemmas 4 and 5): if such a
series vanishes to order `S` at `R` distinct integers, then every coefficient has norm at most
`M * r ^ (-(R * S))`. The proof uses polynomials only. Truncating the series and dividing by the
monic integer polynomial `U = ∏ (X - a) ^ S` gives a quotient with small coefficients (the division
is integral) and a remainder of degree `< R * S` whose Hermite data (derivatives of order `< S` at
the nodes) are small. A polynomial of degree `< R * S` is controlled by its Hermite data through
the inverse of a linear isomorphism of finite-dimensional spaces.

## Main statements

* `PadicBaker.iterate_seqDeriv_apply`: the closed form of the iterated formal derivative.
* `PadicBaker.exists_hermite_bound`: a polynomial of degree `< card A * S` is bounded by its
  Hermite data at the nodes `A`.
* `PadicBaker.norm_le_of_iterate_seqDeriv_eq_zero`: many zeros at integers force small
  coefficients.
-/

@[expose] public section

open Polynomial Filter Topology Function

namespace PadicBaker

variable {K : Type*} [NontriviallyNormedField K]

/-- The value `∑' k, c k * x ^ k` of the power series with coefficients `c`. -/
noncomputable def seqEval (c : ℕ → K) (x : K) : K := ∑' k, c k * x ^ k

/-- The formal derivative `k ↦ (k + 1) * c (k + 1)` of a coefficient sequence. -/
def seqDeriv (c : ℕ → K) : ℕ → K := fun k => ((k + 1 : ℕ) : K) * c (k + 1)

/-- The truncation `∑_{k < τ} c k X ^ k` of a coefficient sequence. -/
noncomputable def seqTrunc (c : ℕ → K) (τ : ℕ) : K[X] := ∑ k ∈ Finset.range τ, monomial k (c k)

theorem iterate_seqDeriv_apply (c : ℕ → K) (j k : ℕ) :
    (seqDeriv^[j] c) k = ((k + j).descFactorial j : K) * c (k + j) := by
  induction j generalizing k with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', seqDeriv, ih, ← mul_assoc]
    have h1 : k + 1 + j = k + (j + 1) := by ring
    rw [h1]
    congr 1
    rw [Nat.descFactorial_succ, show k + (j + 1) - j = k + 1 by omega, Nat.cast_mul]

theorem seqDeriv_add (c d : ℕ → K) : seqDeriv (c + d) = seqDeriv c + seqDeriv d := by
  funext k; simp [seqDeriv, mul_add]

theorem iterate_seqDeriv_add (c d : ℕ → K) (j : ℕ) :
    seqDeriv^[j] (c + d) = seqDeriv^[j] c + seqDeriv^[j] d := by
  funext k; simp [iterate_seqDeriv_apply, mul_add]

theorem iterate_seqDeriv_sum {ι : Type*} (s : Finset ι) (c : ι → ℕ → K) (j : ℕ) :
    seqDeriv^[j] (∑ i ∈ s, c i) = ∑ i ∈ s, seqDeriv^[j] (c i) := by
  funext k; simp [iterate_seqDeriv_apply, Finset.mul_sum]

theorem iterate_seqDeriv_comm (c : ℕ → K) (j : ℕ) :
    seqDeriv^[j] (seqDeriv c) = seqDeriv^[j + 1] c := by
  rw [Function.iterate_succ_apply]

theorem coeff_seqTrunc (c : ℕ → K) (τ k : ℕ) :
    (seqTrunc c τ).coeff k = if k < τ then c k else 0 := by
  simp [seqTrunc, coeff_monomial]

theorem nonneg_of_decay {c : ℕ → K} {r M : ℝ} (hr : 0 ≤ r) (hM : ∀ k, ‖c k‖ * r ^ k ≤ M) :
    0 ≤ M :=
  (mul_nonneg (norm_nonneg _) (pow_nonneg hr 0)).trans (hM 0)

theorem norm_le_of_decay {c : ℕ → K} {r M : ℝ} (hr : 0 < r) (hM : ∀ k, ‖c k‖ * r ^ k ≤ M)
    (k : ℕ) : ‖c k‖ ≤ M * (r ^ k)⁻¹ := by
  rw [le_mul_inv_iff₀ (pow_pos hr k)]; exact hM k

theorem tendsto_norm_of_decay {c : ℕ → K} {r M : ℝ} (hr : 1 < r)
    (hM : ∀ k, ‖c k‖ * r ^ k ≤ M) : Tendsto (fun k => ‖c k‖) atTop (𝓝 0) := by
  have hr0 : 0 < r := by linarith
  have hlim : Tendsto (fun k : ℕ => M * r⁻¹ ^ k) atTop (𝓝 (M * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hr0.le)
      (inv_lt_one_of_one_lt₀ hr)).const_mul M
  rw [mul_zero] at hlim
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hlim
  rw [inv_pow]
  exact norm_le_of_decay hr0 hM k

section Ultra

variable [IsUltrametricDist K]

theorem norm_seqEval_le {c : ℕ → K} {B : ℝ} (hB : 0 ≤ B) {x : K}
    (h : ∀ k, ‖c k * x ^ k‖ ≤ B) : ‖seqEval c x‖ ≤ B :=
  IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hB h

theorem norm_iterate_seqDeriv_apply_le (c : ℕ → K) (j k : ℕ) :
    ‖(seqDeriv^[j] c) k‖ ≤ ‖c (k + j)‖ := by
  rw [iterate_seqDeriv_apply, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one K _)

/-- The iterated derivatives satisfy the same decay bound. -/
theorem iterate_seqDeriv_decay {c : ℕ → K} {r M : ℝ} (hr : 1 ≤ r)
    (hM : ∀ k, ‖c k‖ * r ^ k ≤ M) (j : ℕ) : ∀ k, ‖(seqDeriv^[j] c) k‖ * r ^ k ≤ M := by
  intro k
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  calc ‖(seqDeriv^[j] c) k‖ * r ^ k ≤ ‖c (k + j)‖ * r ^ (k + j) :=
        mul_le_mul (norm_iterate_seqDeriv_apply_le c j k) (pow_le_pow_right₀ hr (by omega))
          (pow_nonneg hr0 _) (norm_nonneg _)
    _ ≤ M := hM _

variable [CompleteSpace K]

theorem summable_of_decay {c : ℕ → K} {r M : ℝ} (hr : 1 < r) (hM : ∀ k, ‖c k‖ * r ^ k ≤ M)
    {x : K} (hx : ‖x‖ ≤ 1) : Summable fun k => c k * x ^ k := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) (tendsto_norm_of_decay hr hM)
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hx)

/-- The iterated derivatives of a truncation are close to those of the series on the unit disc. -/
theorem norm_seqEval_sub_eval_trunc_le {c : ℕ → K} {r M : ℝ} (hr : 1 < r)
    (hM : ∀ k, ‖c k‖ * r ^ k ≤ M) (j τ : ℕ) {x : K} (hx : ‖x‖ ≤ 1) :
    ‖seqEval (seqDeriv^[j] c) x - (derivative^[j] (seqTrunc c τ)).eval x‖ ≤ M * (r ^ τ)⁻¹ := by
  have hr0 : 0 < r := by linarith
  have hM0 : 0 ≤ M := nonneg_of_decay hr0.le hM
  set T := derivative^[j] (seqTrunc c τ) with hT
  have hpoly : HasSum (fun i => T.coeff i * x ^ i) (T.eval x) := by
    rw [eval_eq_sum_range]
    refine hasSum_sum_of_ne_finset_zero fun i hi => ?_
    rw [Finset.mem_range, not_lt] at hi
    rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
  have hser : HasSum (fun i => (seqDeriv^[j] c) i * x ^ i) (seqEval (seqDeriv^[j] c) x) :=
    (summable_of_decay hr (iterate_seqDeriv_decay hr.le hM j) hx).hasSum
  have hdiff := hser.sub hpoly
  rw [← hdiff.tsum_eq]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun i => ?_
  rw [hT, coeff_iterate_derivative, coeff_seqTrunc, iterate_seqDeriv_apply, nsmul_eq_mul]
  by_cases hi : i + j < τ
  · simp only [hi, ↓reduceIte, sub_self, norm_zero]
    positivity
  · simp only [hi, ↓reduceIte, mul_zero, zero_mul, sub_zero, norm_mul, norm_pow]
    calc ‖((i + j).descFactorial j : K)‖ * ‖c (i + j)‖ * ‖x‖ ^ i ≤ 1 * ‖c (i + j)‖ * 1 := by
          gcongr
          · exact IsUltrametricDist.norm_natCast_le_one K _
          · exact pow_le_one₀ (norm_nonneg _) hx
      _ = ‖c (i + j)‖ := by ring
      _ ≤ M * (r ^ (i + j))⁻¹ := norm_le_of_decay hr0 hM _
      _ ≤ M * (r ^ τ)⁻¹ := by
          gcongr
          · exact hr.le
          · omega

end Ultra

section Hermite

/-- The derivatives of order `< S` of a multiple of `(X - a) ^ S` vanish at `a`. -/
theorem iterate_derivative_eval_eq_zero_of_dvd {P : K[X]} {a : K} {S : ℕ}
    (h : (X - C a) ^ S ∣ P) {j : ℕ} (hj : j < S) : (derivative^[j] P).eval a = 0 := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp
  exact isRoot_iterate_derivative_of_lt_rootMultiplicity
    (hj.trans_le ((le_rootMultiplicity_iff hP).mpr h))

variable [CharZero K]

/-- `(X - a) ^ S` divides a polynomial whose derivatives of order `< S` vanish at `a`. -/
theorem pow_X_sub_C_dvd_of_iterate_derivative_eval_eq_zero {P : K[X]} {a : K} {S : ℕ}
    (h : ∀ j < S, (derivative^[j] P).eval a = 0) : (X - C a) ^ S ∣ P := by
  rcases eq_or_ne P 0 with rfl | hP
  · exact dvd_zero _
  rcases S with - | S
  · simp
  rw [← le_rootMultiplicity_iff hP, Nat.succ_le_iff]
  refine (lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors hP
    (mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast S.factorial_ne_zero))).mpr fun m hm => ?_
  exact h m (by omega)

variable [CompleteSpace K]

/-- **A polynomial is controlled by its Hermite data.** For nodes `A` and multiplicity `S`, there is
a constant `C` such that every polynomial of degree `< card A * S` whose derivatives of order `< S`
at the nodes have norm at most `ε` has coefficients of norm at most `C * ε`. -/
theorem exists_hermite_bound (A : Finset K) (S : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : K[X], P.degree < (A.card * S : ℕ) → ∀ ε : ℝ, 0 ≤ ε →
      (∀ a ∈ A, ∀ j < S, ‖(derivative^[j] P).eval a‖ ≤ ε) → ∀ i, ‖P.coeff i‖ ≤ C * ε := by
  classical
  set N := A.card * S with hN
  let V := degreeLT K N
  have : FiniteDimensional K V := (degreeLTEquiv K N).symm.finiteDimensional
  let H : V →ₗ[K] ((↥A × Fin S) → K) := LinearMap.pi fun i : ↥A × Fin S =>
    (leval (i.1 : K)) ∘ₗ ((derivative (R := K)) ^ (i.2 : ℕ)) ∘ₗ V.subtype
  have hH : ∀ (P : V) (i : ↥A × Fin S),
      H P i = (derivative^[(i.2 : ℕ)] (P : K[X])).eval (i.1 : K) := by
    intro P i
    simp [H, Module.End.pow_apply]
  -- the Hermite map is injective
  have hinj : Function.Injective H := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro P hP
    have hdvd : ∀ a ∈ A, (X - C a) ^ S ∣ (P : K[X]) := fun a ha =>
      pow_X_sub_C_dvd_of_iterate_derivative_eval_eq_zero fun j hj => by
        have := congrFun hP (⟨a, ha⟩, ⟨j, hj⟩)
        rwa [hH] at this
    have hcop : (A : Set K).Pairwise (IsCoprime on fun a => (X - C a) ^ S) := by
      intro a _ b _ hab
      exact (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne hab).isUnit).pow
    have hprod := Finset.prod_dvd_of_coprime hcop hdvd
    have hdeg : ((P : K[X])).degree < (∏ a ∈ A, (X - C a) ^ S).degree := by
      rw [degree_eq_natDegree (Monic.ne_zero (monic_prod_of_monic _ _ fun a _ =>
        (monic_X_sub_C a).pow S)), natDegree_prod_of_monic _ _ fun a _ => (monic_X_sub_C a).pow S]
      simp only [natDegree_pow, natDegree_X_sub_C, mul_one, Finset.sum_const, smul_eq_mul]
      have := mem_degreeLT.mp P.2
      rwa [hN] at this
    exact Subtype.ext (eq_zero_of_dvd_of_degree_lt hprod hdeg)
  have hrank : Module.finrank K V = Module.finrank K ((↥A × Fin S) → K) := by
    rw [(degreeLTEquiv K N).finrank_eq, Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card]
    simp [hN]
  have hsurj : Function.Surjective H :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj
  let e : V ≃ₗ[K] ((↥A × Fin S) → K) := LinearEquiv.ofBijective H ⟨hinj, hsurj⟩
  let Φ : ((↥A × Fin S) → K) →ₗ[K] (Fin N → K) :=
    (degreeLTEquiv K N).toLinearMap ∘ₗ e.symm.toLinearMap
  let Φc : ((↥A × Fin S) → K) →L[K] (Fin N → K) := LinearMap.toContinuousLinearMap Φ
  refine ⟨‖Φc‖, norm_nonneg _, fun P hP ε hε hdata i => ?_⟩
  set P' : V := ⟨P, mem_degreeLT.mpr hP⟩ with hP'
  have hΦ : Φc (H P') = fun i : Fin N => P.coeff i := by
    change (degreeLTEquiv K N) (e.symm (e P')) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  have hHle : ‖H P'‖ ≤ ε := by
    refine (pi_norm_le_iff_of_nonneg hε).mpr fun j => ?_
    rw [hH]
    exact hdata _ j.1.2 _ j.2.2
  rcases lt_or_ge i N with hi | hi
  · calc ‖P.coeff i‖ = ‖(Φc (H P')) ⟨i, hi⟩‖ := by rw [hΦ]
      _ ≤ ‖Φc (H P')‖ := norm_le_pi_norm _ _
      _ ≤ ‖Φc‖ * ‖H P'‖ := Φc.le_opNorm _
      _ ≤ ‖Φc‖ * ε := by gcongr
  · rw [coeff_eq_zero_of_degree_lt (hP.trans_le (by exact_mod_cast hi)), norm_zero]
    positivity

end Hermite

section Main

variable [IsUltrametricDist K] [CharZero K] [CompleteSpace K]

/-- **Many zeros at integers force small coefficients.** If `‖c k‖ * r ^ k ≤ M` with `r > 1` and
the power series vanishes to order `S` (its formal derivatives of order `< S` vanish) at each
natural number of `A`, then every coefficient satisfies `‖c k‖ ≤ M * r ^ (-(card A * S))`. -/
theorem norm_le_of_iterate_seqDeriv_eq_zero {c : ℕ → K} {r M : ℝ} (hr : 1 < r)
    (hM : ∀ k, ‖c k‖ * r ^ k ≤ M) (A : Finset ℕ) (S : ℕ)
    (hvan : ∀ a ∈ A, ∀ j < S, seqEval (seqDeriv^[j] c) (a : K) = 0) (k : ℕ) :
    ‖c k‖ ≤ M * (r ^ (A.card * S))⁻¹ := by
  classical
  have hr0 : 0 < r := by linarith
  have hM0 : 0 ≤ M := nonneg_of_decay hr0.le hM
  set N := A.card * S with hN
  -- the nodes in `K`
  set AK : Finset K := A.image (Nat.cast) with hAK
  have hcard : AK.card = A.card := Finset.card_image_of_injective _ Nat.cast_injective
  obtain ⟨C₀, hC₀, hC⟩ := exists_hermite_bound AK S
  -- the monic integer polynomial with the prescribed zeros
  set Uz : ℤ[X] := ∏ a ∈ A, (X - C (a : ℤ)) ^ S with hUz
  have hUzm : Uz.Monic := monic_prod_of_monic _ _ fun a _ => (monic_X_sub_C _).pow S
  set U : K[X] := Uz.map (Int.castRingHom K) with hU
  have hUm : U.Monic := hUzm.map _
  have hUeq : U = ∏ a ∈ A, (X - C (a : K)) ^ S := by
    rw [hU, hUz, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Polynomial.map_pow, Polynomial.map_sub, map_X, map_C, eq_intCast, Int.cast_natCast]
  have hUdeg : U.natDegree = N := by
    rw [hUeq, natDegree_prod_of_monic _ _ fun a _ => (monic_X_sub_C _).pow S]
    simp only [natDegree_pow, natDegree_X_sub_C, mul_one, Finset.sum_const, smul_eq_mul, hN]
  have hUcoeff : ∀ i, ‖U.coeff i‖ ≤ 1 := fun i => by
    rw [hU, coeff_map, eq_intCast]
    exact IsUltrametricDist.norm_intCast_le_one K _
  -- the quotients of monomials by `U` are integral
  have hQcoeff : ∀ i j, ‖(X ^ i /ₘ U).coeff j‖ ≤ 1 := fun i j => by
    have : (X ^ i : K[X]) /ₘ U = ((X ^ i : ℤ[X]) /ₘ Uz).map (Int.castRingHom K) := by
      rw [map_divByMonic _ hUzm, Polynomial.map_pow, map_X]
    rw [this, coeff_map, eq_intCast]
    exact IsUltrametricDist.norm_intCast_le_one K _
  have hQzero : ∀ i < N, (X ^ i : K[X]) /ₘ U = 0 := fun i hi => by
    rw [divByMonic_eq_zero_iff hUm, degree_X_pow, degree_eq_natDegree hUm.ne_zero, hUdeg]
    exact_mod_cast hi
  -- the estimate at a truncation level `τ > k`
  have hstep : ∀ τ, k < τ → ‖c k‖ ≤ max (M * (r ^ N)⁻¹) (C₀ * (M * (r ^ τ)⁻¹)) := by
    intro τ hkτ
    set Q : K[X] := ∑ i ∈ Finset.range τ, c i • (X ^ i /ₘ U) with hQ
    set P : K[X] := ∑ i ∈ Finset.range τ, c i • (X ^ i %ₘ U) with hP
    have hTsplit : seqTrunc c τ = U * Q + P := by
      rw [seqTrunc, hQ, hP, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← C_mul_X_pow_eq_monomial, mul_smul_comm, ← smul_add, add_comm,
        modByMonic_add_div (X ^ i) U, smul_eq_C_mul]
    have hPdeg : P.degree < (AK.card * S : ℕ) := by
      rw [hcard, ← hN, ← mem_degreeLT]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
      rw [mem_degreeLT, ← hUdeg, ← degree_eq_natDegree hUm.ne_zero]
      exact degree_modByMonic_lt _ hUm
    have hQbound : ∀ j, ‖Q.coeff j‖ ≤ M * (r ^ N)⁻¹ := by
      intro j
      rw [hQ, finsetSum_coeff]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i _ => ?_
      rw [coeff_smul, smul_eq_mul, norm_mul]
      rcases lt_or_ge i N with hi | hi
      · rw [hQzero i hi, coeff_zero, norm_zero, mul_zero]; positivity
      · calc ‖c i‖ * ‖(X ^ i /ₘ U).coeff j‖ ≤ ‖c i‖ * 1 := by gcongr; exact hQcoeff i j
          _ = ‖c i‖ := mul_one _
          _ ≤ M * (r ^ i)⁻¹ := norm_le_of_decay hr0 hM i
          _ ≤ M * (r ^ N)⁻¹ := by gcongr; exact hr.le
    have hdata : ∀ a ∈ AK, ∀ j < S, ‖(derivative^[j] P).eval a‖ ≤ M * (r ^ τ)⁻¹ := by
      intro a ha j hj
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
      have hPeq : P = seqTrunc c τ - U * Q := by rw [hTsplit]; ring
      have hUQ : (derivative^[j] (U * Q)).eval (b : K) = 0 := by
        refine iterate_derivative_eval_eq_zero_of_dvd (dvd_mul_of_dvd_left ?_ Q) hj
        rw [hUeq]
        exact Finset.dvd_prod_of_mem (fun a : ℕ => (X - C (a : K)) ^ S) hb
      have hser : seqEval (seqDeriv^[j] c) (b : K) = 0 := hvan b hb j hj
      have hb1 : ‖(b : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K b
      have := norm_seqEval_sub_eval_trunc_le hr hM j τ hb1
      rw [hser, zero_sub, norm_neg] at this
      rw [hPeq, iterate_derivative_sub, eval_sub, hUQ, sub_zero]
      exact this
    have hPbound := hC P hPdeg (M * (r ^ τ)⁻¹) (by positivity) hdata
    have hck : c k = (U * Q).coeff k + P.coeff k := by
      rw [← coeff_add, ← hTsplit, coeff_seqTrunc]
      simp [hkτ]
    have hUQk : ‖(U * Q).coeff k‖ ≤ M * (r ^ N)⁻¹ := by
      rw [coeff_mul]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun x _ => ?_
      rw [norm_mul]
      calc ‖U.coeff x.1‖ * ‖Q.coeff x.2‖ ≤ 1 * (M * (r ^ N)⁻¹) := by
            gcongr
            · exact hUcoeff _
            · exact hQbound _
        _ = M * (r ^ N)⁻¹ := one_mul _
    rw [hck]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max hUQk (hPbound k))
  -- let the truncation level tend to infinity
  by_contra hcon
  push Not at hcon
  have hlim : Tendsto (fun τ : ℕ => C₀ * (M * r⁻¹ ^ τ)) atTop (𝓝 (C₀ * (M * 0))) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hr0.le)
      (inv_lt_one_of_one_lt₀ hr)).const_mul M).const_mul C₀
  rw [mul_zero, mul_zero] at hlim
  have hpos : 0 < ‖c k‖ := (by positivity : 0 ≤ M * (r ^ N)⁻¹).trans_lt hcon
  obtain ⟨τ₀, hτ₀⟩ := (hlim.eventually (gt_mem_nhds hpos)).exists_forall_of_atTop
  have h := hstep (max τ₀ (k + 1)) (by omega)
  have hsmall := hτ₀ (max τ₀ (k + 1)) (le_max_left _ _)
  rw [inv_pow] at hsmall
  rcases le_max_iff.mp h with h' | h'
  · linarith
  · linarith

/-- The value on the closed unit disc is small too. -/
theorem norm_seqEval_le_of_iterate_seqDeriv_eq_zero {c : ℕ → K} {r M : ℝ} (hr : 1 < r)
    (hM : ∀ k, ‖c k‖ * r ^ k ≤ M) (A : Finset ℕ) (S : ℕ)
    (hvan : ∀ a ∈ A, ∀ j < S, seqEval (seqDeriv^[j] c) (a : K) = 0) {x : K} (hx : ‖x‖ ≤ 1) :
    ‖seqEval c x‖ ≤ M * (r ^ (A.card * S))⁻¹ := by
  have hr0 : 0 < r := by linarith
  have hM0 : 0 ≤ M := nonneg_of_decay hr0.le hM
  refine norm_seqEval_le (by positivity) fun k => ?_
  rw [norm_mul, norm_pow]
  calc ‖c k‖ * ‖x‖ ^ k ≤ ‖c k‖ * 1 := by gcongr; exact pow_le_one₀ (norm_nonneg _) hx
    _ = ‖c k‖ := mul_one _
    _ ≤ M * (r ^ (A.card * S))⁻¹ := norm_le_of_iterate_seqDeriv_eq_zero hr hM A S hvan k

end Main

end PadicBaker
