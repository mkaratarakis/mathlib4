/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.NumberTheory.Transcendental.Baker.MultiIndex
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Truncated Taylor interpolation

A function holomorphic and bounded by `M` on the ball of radius `R` is, on the smaller ball of
radius `r`, within `(1 + T) * M * (r / R) ^ T` of its Taylor polynomial of degree `< T`.  This is
the interpolation estimate of Waldschmidt, *Diophantine Approximation on Linear Algebraic
Groups*, Lemma 4.13, which turns smallness of finitely many Taylor coefficients at the origin
into smallness of the function on a disc.

The proof restricts to the complex line through the point, where the difference between the
function and its Taylor polynomial has a zero of order `T` at the origin.  Schwarz's lemma for
such a zero gives the factor `(r / R) ^ T`, and Cauchy's estimate bounds the Taylor polynomial by
`T * M` on the circle.  Waldschmidt bounds the Taylor polynomial by `√T * M` using Parseval's
formula instead; that needs a Hilbert space of values, whereas Cauchy's estimate works for any
Banach space, and the weaker constant is all that the construction of the auxiliary function
uses.

## Main statements

* `Complex.norm_le_mul_div_pow_of_iterate_dslope_eq_zero`: Schwarz's lemma for a zero of
  order `T`.
* `HasFPowerSeriesOnBall.norm_apply_le`: Cauchy's estimate for the homogeneous terms of a
  power series.
* `HasFPowerSeriesOnBall.norm_sub_partialSum_le`: the Taylor remainder estimate, on any
  complex normed space.
* `MultiIndex.norm_coeff_mul_pow_le`: Cauchy's inequality `‖c_α‖ ρ ^ |α| ≤ M` on a polydisc,
  proved by averaging over roots of unity on a torus rather than by a Cauchy integral.
* `MultiIndex.norm_le_of_hasFPowerSeriesOnBall`: Lemma 4.13 in Waldschmidt's form, with the
  Taylor polynomial expanded in multi-index coefficients.
-/

@[expose] public section

open Metric Function Filter Topology
open scoped NNReal ENNReal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

namespace Complex

variable [CompleteSpace V]

/-- Iterated slopes at an interior point of an open set stay holomorphic there. -/
lemma differentiableOn_iterate_dslope {g : ℂ → V} {s : Set ℂ} {c : ℂ} (hc : s ∈ 𝓝 c)
    (hg : DifferentiableOn ℂ g s) (k : ℕ) :
    DifferentiableOn ℂ ((swap dslope c)^[k] g) s := by
  induction k with
  | zero => exact hg
  | succ k ih =>
    rw [iterate_succ_apply']
    exact (differentiableOn_dslope hc).2 ih

/-- **Schwarz's lemma for a zero of order `T`.**

If `g` is holomorphic and bounded by `M` on the disc of radius `ρ` about `0`, and its first `T`
iterated slopes at `0` vanish -- that is, `g` has a zero of order at least `T` there -- then
`‖g w‖ ≤ M * (‖w‖ / ρ) ^ T` on that disc. -/
theorem norm_le_mul_div_pow_of_iterate_dslope_eq_zero {g : ℂ → V} {ρ M : ℝ}
    (hg : DifferentiableOn ℂ g (ball 0 ρ)) {T : ℕ}
    (hT : ∀ k < T, (swap dslope 0)^[k] g 0 = 0) (hM : ∀ w ∈ ball (0 : ℂ) ρ, ‖g w‖ ≤ M)
    {w : ℂ} (hw : ‖w‖ < ρ) : ‖g w‖ ≤ M * (‖w‖ / ρ) ^ T := by
  have hρ : 0 < ρ := (norm_nonneg w).trans_lt hw
  set h := (swap dslope (0 : ℂ))^[T] g with hh
  have hhd : DifferentiableOn ℂ h (ball 0 ρ) :=
    differentiableOn_iterate_dslope (ball_mem_nhds 0 hρ) hg T
  have heq : ∀ v, g v = v ^ T • h v := fun v => by
    simpa using (pow_sub_smul_iterate_dslope_of_zero T hT v).symm
  -- on each smaller circle, `h` is bounded by `M / ρ' ^ T`
  have hsmall : ∀ ρ' ∈ Set.Ioo ‖w‖ ρ, M * (‖w‖ / ρ') ^ T ≥ ‖g w‖ := by
    rintro ρ' ⟨hwρ', hρ'ρ⟩
    have hρ' : 0 < ρ' := (norm_nonneg w).trans_lt hwρ'
    have hcl : DiffContOnCl ℂ h (ball 0 ρ') :=
      hhd.diffContOnCl_ball (closedBall_subset_ball hρ'ρ)
    have hfr : ∀ v ∈ frontier (ball (0 : ℂ) ρ'), ‖h v‖ ≤ M / ρ' ^ T := by
      intro v hv
      rw [frontier_ball _ hρ'.ne'] at hv
      have hvn : ‖v‖ = ρ' := by simpa using hv
      have hgv := hM v (by simpa [hvn] using hρ'ρ)
      rw [heq v, norm_smul, norm_pow, hvn] at hgv
      rw [le_div_iff₀ (by positivity), mul_comm]
      exact hgv
    have hw' : w ∈ closure (ball (0 : ℂ) ρ') := by
      rw [closure_ball _ hρ'.ne']
      simpa using hwρ'.le
    have hhw := norm_le_of_forall_mem_frontier_norm_le isBounded_ball hcl hfr hw'
    calc ‖g w‖ = ‖w‖ ^ T * ‖h w‖ := by rw [heq w, norm_smul, norm_pow]
      _ ≤ ‖w‖ ^ T * (M / ρ' ^ T) := by gcongr
      _ = M * (‖w‖ / ρ') ^ T := by rw [div_pow]; field_simp
  -- let the radius increase to `ρ`
  have hcont : ContinuousAt (fun ρ' : ℝ => M * (‖w‖ / ρ') ^ T) ρ :=
    continuousAt_const.mul ((continuousAt_const.div continuousAt_id hρ.ne').pow T)
  exact ge_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds)
    (eventually_of_mem (Ioo_mem_nhdsLT hw) hsmall)

end Complex

namespace HasFPowerSeriesOnBall

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace V]
  {F : E → V} {p : FormalMultilinearSeries ℂ E V} {R : ℝ≥0}

omit [NormedSpace ℂ E] [CompleteSpace V] in
private lemma mem_eball_coe {y : E} (hy : ‖y‖ < R) : y ∈ eball (0 : E) R := by
  rw [mem_eball_zero_iff, enorm_eq_nnnorm, ENNReal.coe_lt_coe]
  exact_mod_cast hy

/-- **Cauchy's estimate for the homogeneous terms of a power series.**

If `F` has the power series `p` on the ball of radius `R` about `0` and is bounded by `M`
there, then every homogeneous term of `p` is bounded by `M` on that ball. -/
theorem norm_apply_le (hF : HasFPowerSeriesOnBall F p 0 R) {M : ℝ}
    (hM : ∀ y : E, ‖y‖ < R → ‖F y‖ ≤ M) (n : ℕ) {y : E} (hy : ‖y‖ < R) :
    ‖p n (fun _ => y)‖ ≤ M := by
  -- restrict to the line through `y`
  set u : ℂ →L[ℂ] E := (1 : ℂ →L[ℂ] ℂ).smulRight y with hu
  have hu_apply : ∀ w : ℂ, u w = w • y := fun w => by simp [hu]
  have hF0 : HasFPowerSeriesOnBall F p (u 0) R := by simpa [hu_apply] using hF
  obtain ⟨ρ, hρ⟩ := hF0.hasFPowerSeriesAt.compContinuousLinearMap
  -- the `n`-th term is the `n`-th derivative of the restriction, divided by `n !`
  have hfact := hρ.factorial_smul 1 n
  rw [← iteratedDeriv_eq_iteratedFDeriv] at hfact
  simp only [FormalMultilinearSeries.compContinuousLinearMap_apply, comp_def,
    hu_apply, one_smul] at hfact
  -- the restriction is holomorphic on a neighbourhood of the closed unit disc
  have hmaps : ∀ w ∈ closedBall (0 : ℂ) 1, u w ∈ eball (0 : E) R := by
    intro w hw
    refine mem_eball_coe ?_
    rw [hu_apply, norm_smul]
    calc ‖w‖ * ‖y‖ ≤ 1 * ‖y‖ := by gcongr; simpa using hw
      _ < R := by simpa using hy
  have hdiff : DifferentiableOn ℂ (F ∘ u) (closedBall 0 1) :=
    hF.differentiableOn.comp u.differentiableOn hmaps
  have hC : ∀ w ∈ sphere (0 : ℂ) 1, ‖(F ∘ u) w‖ ≤ M := by
    intro w hw
    have hw' := hmaps w (sphere_subset_closedBall hw)
    rw [mem_eball_zero_iff, enorm_eq_nnnorm, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe,
      coe_nnnorm] at hw'
    exact hM _ hw'
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n one_pos
    (hdiff.diffContOnCl_ball subset_rfl) hC
  simp only [comp_def, hu_apply] at hcauchy
  rw [← hfact, RCLike.norm_nsmul (K := ℂ), nsmul_eq_mul, one_pow, div_one] at hcauchy
  exact le_of_mul_le_mul_left hcauchy (by exact_mod_cast n.factorial_pos)

/-- **Truncated Taylor interpolation.**

If `F` has the power series `p` on the ball of radius `R` about `0` and is bounded by `M` there,
then at a point `z` of that ball, `F z` differs from the Taylor polynomial of degree `< T` by at
most `(1 + T) * M * (‖z‖ / R) ^ T`.  This is the analytic content of Waldschmidt's Lemma 4.13,
on any complex normed space and with values in any complex Banach space. -/
theorem norm_sub_partialSum_le (hF : HasFPowerSeriesOnBall F p 0 R) {M : ℝ}
    (hM : ∀ y : E, ‖y‖ < R → ‖F y‖ ≤ M) (T : ℕ) {z : E} (hz : ‖z‖ < R) :
    ‖F z - p.partialSum T z‖ ≤ (1 + T) * M * (‖z‖ / R) ^ T := by
  have hR : (0 : ℝ) < R := (norm_nonneg z).trans_lt hz
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simpa using hR))
  rcases eq_or_ne z 0 with rfl | hz0
  · cases T with
    | zero => simpa [FormalMultilinearSeries.partialSum] using hM 0 (by simpa using hR)
    | succ T =>
      have : p.partialSum (T + 1) 0 = F 0 := by
        rw [FormalMultilinearSeries.partialSum, Finset.sum_range_succ']
        simp only [hF.coeff_zero, add_eq_right]
        exact Finset.sum_eq_zero fun k _ => (p (k + 1)).map_zero
      rw [this, sub_self, norm_zero]
      positivity
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  set ρ : ℝ := R / ‖z‖ with hρ
  have hwz : ∀ w : ℂ, ‖w‖ < ρ → ‖w • z‖ < R := fun w hw => by
    rw [norm_smul]
    rwa [hρ, lt_div_iff₀ hzpos] at hw
  set c : ℕ → V := fun n => p n fun _ => z with hc
  have hcw : ∀ (w : ℂ) (n : ℕ), p n (fun _ => w • z) = w ^ n • c n := fun w n => by
    simpa [hc] using (p n).map_smul_univ (fun _ => w) (fun _ => z)
  -- `g` is `F` on the line through `z`, minus its Taylor polynomial
  set g : ℂ → V := fun w => F (w • z) - ∑ n ∈ Finset.range T, w ^ n • c n with hg
  set c' : ℕ → V := fun n => if n < T then 0 else c n with hc'
  have hsum : ∀ w : ℂ, ‖w‖ < ρ → HasSum (fun n => w ^ n • c' n) (g w) := by
    intro w hw
    have hs : HasSum (fun n => w ^ n • c n) (F (w • z)) := by
      simpa [hcw] using hF.hasSum (mem_eball_coe (hwz w hw))
    have hfin : HasSum (fun n => if n < T then w ^ n • c n else 0)
        (∑ n ∈ Finset.range T, w ^ n • c n) := by
      rw [show ∑ n ∈ Finset.range T, w ^ n • c n
          = ∑ n ∈ Finset.range T, (if n < T then w ^ n • c n else 0) from
        Finset.sum_congr rfl fun n hn => by simp_all]
      exact hasSum_sum_of_ne_finset_zero fun n hn => by simp_all
    convert hs.sub hfin using 1
    funext n
    by_cases hn : n < T <;> simp [hc', hn]
  -- its expansion at `0` has no terms of degree `< T`
  set q : FormalMultilinearSeries ℂ ℂ V :=
    fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (c' n) with hq
  have hqc : ∀ n, q.coeff n = c' n := fun n => by
    simp [hq, FormalMultilinearSeries.coeff]
  have hρpos : 0 < ρ := by positivity
  have hgq : HasFPowerSeriesAt g q 0 := by
    refine hasFPowerSeriesAt_iff.2 ?_
    filter_upwards [ball_mem_nhds (0 : ℂ) hρpos] with w hw
    simpa [hqc] using hsum w (by simpa using hw)
  have hT : ∀ k < T, (swap dslope 0)^[k] g 0 = 0 := by
    intro k hk
    rw [← (hgq.has_fpower_series_iterate_dslope_fslope k).coeff_zero 1, ←
      FormalMultilinearSeries.coeff, FormalMultilinearSeries.coeff_iterate_fslope, zero_add,
      hqc]
    simp [hc', hk]
  -- `g` is holomorphic and bounded by `(1 + T) * M` on the disc of radius `ρ`
  have hmaps : Set.MapsTo (fun w : ℂ => w • z) (ball 0 ρ) (eball (0 : E) R) :=
    fun w hw => mem_eball_coe (hwz w (by simpa using hw))
  have hgd : DifferentiableOn ℂ g (ball 0 ρ) :=
    (hF.differentiableOn.comp (differentiableOn_id.smul_const z) hmaps).sub
      (Differentiable.differentiableOn (by fun_prop))
  have hgM : ∀ w ∈ ball (0 : ℂ) ρ, ‖g w‖ ≤ (1 + T) * M := by
    intro w hw
    have hw' : ‖w‖ < ρ := by simpa using hw
    have hpoly : ‖∑ n ∈ Finset.range T, w ^ n • c n‖ ≤ T * M := by
      refine (norm_sum_le _ _).trans ?_
      have hb : ∀ n ∈ Finset.range T, ‖w ^ n • c n‖ ≤ M := fun n _ => by
        rw [← hcw]
        exact hF.norm_apply_le hM n (hwz w hw')
      simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul _ _ _ hb
    calc ‖g w‖ ≤ ‖F (w • z)‖ + ‖∑ n ∈ Finset.range T, w ^ n • c n‖ := norm_sub_le _ _
      _ ≤ M + T * M := add_le_add (hM _ (hwz w hw')) hpoly
      _ = (1 + T) * M := by ring
  -- Schwarz's lemma at `w = 1`
  have h1 := Complex.norm_le_mul_div_pow_of_iterate_dslope_eq_zero hgd hT hgM
    (w := 1) (by simpa [hρ, one_lt_div hzpos] using hz)
  have hg1 : g 1 = F z - p.partialSum T z := by
    simp [hg, hc, FormalMultilinearSeries.partialSum]
  rw [hg1] at h1
  refine h1.trans_eq ?_
  rw [norm_one, hρ, one_div_div]

end HasFPowerSeriesOnBall

namespace MultiIndex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The degree-`k` term of a power series on `ι → 𝕜`, expanded in the multi-index
coefficients of degree `k`. -/
lemma apply_diag_eq_sum_piAntidiag {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) W) (k : ℕ) (z : ι → 𝕜) :
    p k (fun _ => z) = ∑ α ∈ Finset.univ.piAntidiag k, (∏ i, z i ^ α i) • coeff p α := by
  have hsub : Finset.univ.piAntidiag k ⊆ Fintype.piFinset fun _ : ι => Finset.range (k + 1) := by
    intro α hα
    rw [Finset.mem_piAntidiag] at hα
    simp only [Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff]
    exact fun i => hα.1 ▸ Finset.single_le_sum (fun j _ => Nat.zero_le (α j)) (Finset.mem_univ i)
  rw [(p k).apply_diag_eq_sum_multiIndex z]
  symm
  calc ∑ α ∈ Finset.univ.piAntidiag k, (∏ i, z i ^ α i) • coeff p α
      = ∑ α ∈ Finset.univ.piAntidiag k, (∏ i, z i ^ α i) • coeffAt p k α := by
        refine Finset.sum_congr rfl fun α hα => ?_
        rw [Finset.mem_piAntidiag] at hα
        rw [coeff, hα.1]
    _ = _ := by
        refine Finset.sum_subset hsub fun α _ hα => ?_
        have hk : ∑ i, α i ≠ k := fun h => hα (by simp [Finset.mem_piAntidiag, h])
        rw [coeffAt_eq_zero p hk, smul_zero]

/-- Orthogonality of the characters of `ℤ / N`: for `a, b < N`, the sum over `j < N` of
`ω ^ ((b + (N - a)) * j)` is `N` when `b = a` and `0` otherwise. -/
private lemma sum_pow_mul_eq {N : ℕ} {ω : ℂ} (hω : IsPrimitiveRoot ω N) {a b : ℕ} (ha : a < N)
    (hb : b < N) :
    ∑ j : Fin N, ω ^ ((b + (N - a)) * (j : ℕ)) = if b = a then (N : ℂ) else 0 := by
  split_ifs with hba
  · subst hba
    have h1 : ∀ j : Fin N, ω ^ ((b + (N - b)) * (j : ℕ)) = 1 := fun j => by
      rw [show b + (N - b) = N by omega, pow_mul, hω.pow_eq_one, one_pow]
    simp [h1]
  · set m := b + (N - a) with hm
    have hm1 : ω ^ m ≠ 1 := by
      rw [Ne, hω.pow_eq_one_iff_dvd]
      rintro ⟨q, hq⟩
      rcases q with _ | _ | q
      · omega
      · omega
      · have h2 : 2 * N ≤ N * (q + 1 + 1) := by nlinarith
        omega
    rw [Fin.sum_univ_eq_sum_range (fun j => ω ^ (m * j)) N]
    simp_rw [pow_mul]
    rw [geom_sum_eq hm1, show (ω ^ m) ^ N = 1 by
      rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow], sub_self, zero_div]

/-- **Cauchy's inequality on a polydisc.**

If `F` has the power series `p` on the polydisc of polyradius `R` about `0` and `‖F‖ ≤ M`
there, then each multi-index coefficient satisfies `‖c_α‖ * ρ ^ |α| ≤ M` for `ρ < R`.

The degree-`k` part of `p` is a polynomial of degree at most `k` in each variable, so averaging
it against a character over the points `(ρ ω ^ j i)ᵢ` of the torus of radius `ρ`, with `ω` a
primitive `(k + 1)`-th root of unity, extracts the coefficient exactly; the average is bounded
by `M` through Cauchy's estimate `HasFPowerSeriesOnBall.norm_apply_le`. -/
theorem norm_coeff_mul_pow_le [CompleteSpace V] {F : (ι → ℂ) → V}
    {p : FormalMultilinearSeries ℂ (ι → ℂ) V} {R : ℝ≥0} (hF : HasFPowerSeriesOnBall F p 0 R)
    {M : ℝ} (hM : ∀ y : ι → ℂ, ‖y‖ < R → ‖F y‖ ≤ M) (α : ι → ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ρ < R) : ‖coeff p α‖ * ρ ^ (∑ i, α i) ≤ M := by
  set k := ∑ i, α i with hk
  set N := k + 1 with hN
  have hNpos : 0 < N := Nat.succ_pos k
  have hω : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / N)) N :=
    Complex.isPrimitiveRoot_exp N hNpos.ne'
  set ω := Complex.exp (2 * Real.pi * Complex.I / N) with hωdef
  have hωn : ‖ω‖ = 1 := hω.norm'_eq_one hNpos.ne'
  have hle : ∀ β ∈ (Finset.univ : Finset ι).piAntidiag k, ∀ i, β i < N := by
    intro β hβ i
    rw [Finset.mem_piAntidiag] at hβ
    exact Nat.lt_succ_of_le
      (hβ.1 ▸ Finset.single_le_sum (fun j _ => Nat.zero_le (β j)) (Finset.mem_univ i))
  have hα : α ∈ (Finset.univ : Finset ι).piAntidiag k := by simp [hk]
  -- sample points on the torus of radius `ρ`, and the character picking out `α`
  set z : (ι → Fin N) → ι → ℂ := fun j i => (ρ : ℂ) * ω ^ (j i : ℕ) with hz
  set wt : (ι → Fin N) → ℂ := fun j => ∏ i, ω ^ ((N - α i) * (j i : ℕ)) with hwt
  have hexp : ∀ j, p k (fun _ => z j) = ∑ β ∈ Finset.univ.piAntidiag k,
      ((ρ : ℂ) ^ k * ∏ i, ω ^ ((j i : ℕ) * β i)) • coeff p β := by
    intro j
    rw [apply_diag_eq_sum_piAntidiag]
    refine Finset.sum_congr rfl fun β hβ => ?_
    rw [Finset.mem_piAntidiag] at hβ
    congr 1
    simp only [hz, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hβ.1, ← pow_mul]
  have hinner : ∀ β ∈ (Finset.univ : Finset ι).piAntidiag k,
      ∑ j, wt j * ((ρ : ℂ) ^ k * ∏ i, ω ^ ((j i : ℕ) * β i))
        = if β = α then (N : ℂ) ^ Fintype.card ι * (ρ : ℂ) ^ k else 0 := by
    intro β hβ
    calc ∑ j, wt j * ((ρ : ℂ) ^ k * ∏ i, ω ^ ((j i : ℕ) * β i))
        = (ρ : ℂ) ^ k * ∑ j : ι → Fin N, ∏ i, ω ^ ((β i + (N - α i)) * (j i : ℕ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hwt, mul_left_comm, ← Finset.prod_mul_distrib]
          congr 1
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [← pow_add]
          congr 1
          ring
      _ = (ρ : ℂ) ^ k * ∏ i, ∑ a : Fin N, ω ^ ((β i + (N - α i)) * (a : ℕ)) := by
          rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
      _ = (ρ : ℂ) ^ k * ∏ i, (if β i = α i then (N : ℂ) else 0) := by
          congr 1
          exact Finset.prod_congr rfl fun i _ =>
            sum_pow_mul_eq hω (hle α hα i) (hle β hβ i)
      _ = _ := by
          split_ifs with h
          · subst h
            simp [Finset.prod_const, Finset.card_univ, mul_comm]
          · obtain ⟨i, hi⟩ : ∃ i, β i ≠ α i := by
              by_contra hc
              push Not at hc
              exact h (funext hc)
            rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), mul_zero]
  have hkey : ∑ j, wt j • p k (fun _ => z j)
      = ((N : ℂ) ^ Fintype.card ι * (ρ : ℂ) ^ k) • coeff p α := by
    calc ∑ j, wt j • p k (fun _ => z j)
        = ∑ β ∈ Finset.univ.piAntidiag k,
            (∑ j, wt j * ((ρ : ℂ) ^ k * ∏ i, ω ^ ((j i : ℕ) * β i))) • coeff p β := by
          simp_rw [hexp, Finset.smul_sum, smul_smul]
          rw [Finset.sum_comm]
          simp_rw [Finset.sum_smul]
      _ = ∑ β ∈ Finset.univ.piAntidiag k,
            (if β = α then (N : ℂ) ^ Fintype.card ι * (ρ : ℂ) ^ k else 0) • coeff p β :=
          Finset.sum_congr rfl fun β hβ => by rw [hinner β hβ]
      _ = _ := by
          simp_rw [ite_smul, zero_smul]
          rw [Finset.sum_ite_eq' _ α, ite_eq_left hα]
  -- each sample is bounded by `M`, and the character has modulus one
  have hbound : ‖∑ j, wt j • p k (fun _ => z j)‖ ≤ (N : ℝ) ^ Fintype.card ι * M := by
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ j ∈ (Finset.univ : Finset (ι → Fin N)), ‖wt j • p k (fun _ => z j)‖ ≤ M := by
      intro j _
      have hzj : ‖z j‖ < R := by
        refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg hρ0).2 fun i => ?_) hρ
        simp [hz, norm_pow, hωn, abs_of_nonneg hρ0]
      rw [norm_smul]
      have hw1 : ‖wt j‖ = 1 := by simp [hwt, norm_prod, norm_pow, hωn]
      rw [hw1, one_mul]
      exact hF.norm_apply_le hM k hzj
    simpa [nsmul_eq_mul, Fintype.card_fun, Fintype.card_fin] using
      Finset.sum_le_card_nsmul _ _ _ hb
  rw [hkey, norm_smul, norm_mul, norm_pow, norm_pow, Complex.norm_natCast, Complex.norm_real,
    Real.norm_of_nonneg hρ0, mul_assoc] at hbound
  have hNc : (0 : ℝ) < (N : ℝ) ^ Fintype.card ι := by positivity
  rw [mul_comm]
  exact le_of_mul_le_mul_left hbound hNc

/-- **Truncated Taylor interpolation** (Waldschmidt, Lemma 4.13).

Let `F` have the power series `p` on the polydisc of polyradius `R` about `0`, with `‖F‖ ≤ M`
there.  On the polydisc of polyradius `r < R`,
`‖F z‖ ≤ (1 + T) * M * (r / R) ^ T + ∑_{|α| < T} ‖c_α‖ * r ^ |α|`,
where `c_α = coeff p α` is the Taylor coefficient `D^α F (0) / α!`.  Waldschmidt has `1 + √T`
in place of `1 + T`; see the module docstring. -/
theorem norm_le_of_hasFPowerSeriesOnBall [CompleteSpace V] {F : (ι → ℂ) → V}
    {p : FormalMultilinearSeries ℂ (ι → ℂ) V} {R : ℝ≥0} (hF : HasFPowerSeriesOnBall F p 0 R)
    {M : ℝ} (hM : ∀ y : ι → ℂ, ‖y‖ < R → ‖F y‖ ≤ M) (T : ℕ) {r : ℝ} (hr : r < R)
    {z : ι → ℂ} (hz : ‖z‖ ≤ r) :
    ‖F z‖ ≤ (1 + T) * M * (r / R) ^ T +
      ∑ k ∈ Finset.range T, ∑ α ∈ Finset.univ.piAntidiag k, ‖coeff p α‖ * r ^ k := by
  have hr0 : 0 ≤ r := (norm_nonneg z).trans hz
  have hzR : ‖z‖ < R := hz.trans_lt hr
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z hzR)
  have hrem := hF.norm_sub_partialSum_le hM T hzR
  have hpoly : ‖p.partialSum T z‖ ≤
      ∑ k ∈ Finset.range T, ∑ α ∈ Finset.univ.piAntidiag k, ‖coeff p α‖ * r ^ k := by
    rw [FormalMultilinearSeries.partialSum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [apply_diag_eq_sum_piAntidiag]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α hα => ?_)
    rw [Finset.mem_piAntidiag] at hα
    rw [norm_smul, mul_comm, norm_prod]
    gcongr
    calc ∏ i, ‖z i ^ α i‖ ≤ ∏ i, r ^ α i := by
          gcongr with i
          rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) ((norm_le_pi_norm z i).trans hz) _
      _ = r ^ k := by rw [Finset.prod_pow_eq_pow_sum, hα.1]
  calc ‖F z‖ ≤ ‖F z - p.partialSum T z‖ + ‖p.partialSum T z‖ := norm_le_norm_sub_add _ _
    _ ≤ (1 + T) * M * (‖z‖ / R) ^ T + _ := add_le_add hrem hpoly
    _ ≤ (1 + T) * M * (r / R) ^ T + _ := by gcongr

end MultiIndex
