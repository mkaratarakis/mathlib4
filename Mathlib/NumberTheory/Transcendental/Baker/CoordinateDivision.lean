/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.NumberTheory.Transcendental.Baker.TaylorCoeff

/-!
# Dividing a multi-index power series by a coordinate

If every coefficient of degree `< m` in the `i`-th coordinate vanishes, a multi-index power
series is `z i ^ m` times an analytic function (`MultiIndex.exists_analyticAt_eq_pow_smul`, and
`MultiIndex.exists_analyticAt_eq_sub_pow_smul` about an arbitrary centre).  Dividing by a linear
factor `z i - ζ` is done slice by slice with `dslope`: the divided difference
`(f z - f (update z i ζ)) / (z i - ζ)` is analytic off the hyperplane `z i = ζ`
(`MultiIndex.analyticAt_dslope_slice_of_ne`) and, using the Taylor expansion about a point of
the hyperplane, on it as well (`MultiIndex.analyticAt_dslope_slice_of_eq`).

## Main statements

* `MultiIndex.hasSum_split_coord_pow`: `f = f₀ + z i ^ p • f₁`, with `f₀` of degree `< p` in
  `z i`.
* `MultiIndex.exists_analyticAt_eq_pow_smul`: division by a power of a coordinate.
* `MultiIndex.analyticAt_dslope_slice`: the divided difference in one coordinate is analytic,
  on and off the hyperplane.
-/

@[expose] public section

open scoped NNReal ENNReal

section Coordinate

variable {ι : Type*} [Fintype ι] {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace MultiIndex

variable [DecidableEq ι]

/-- **Division of a multi-index power series by a coordinate.**

If every coefficient supported off the `i`-th coordinate vanishes, then the series is `z i`
times the series with the `i`-th exponent shifted down.  This is the algebraic heart of the
division step in a Schwarz lemma for Cartesian products. -/
theorem hasSum_smul_shift {c : (ι → ℕ) → F} (i : ι) {z : ι → 𝕜} {T : F}
    (hvanish : ∀ α : ι → ℕ, α i = 0 → c α = 0)
    (h : HasSum (fun β : ι → ℕ => (∏ j, z j ^ β j) • c (β + (Pi.single i 1 : ι → ℕ))) T) :
    HasSum (fun α : ι → ℕ => (∏ j, z j ^ α j) • c α) (z i • T) := by
  set e : ι → ℕ := Pi.single i 1 with he
  -- multiplying the shifted series by `z i` restores the exponents
  have hterm : ∀ β : ι → ℕ,
      z i • ((∏ j, z j ^ β j) • c (β + e)) = (∏ j, z j ^ (β + e) j) • c (β + e) := by
    intro β
    rw [smul_smul]
    congr 1
    rw [show ∏ j, z j ^ (β + e) j = ∏ j, (z j ^ β j * z j ^ e j) from
      Finset.prod_congr rfl fun j _ => by rw [Pi.add_apply, pow_add], Finset.prod_mul_distrib]
    have : ∏ j, z j ^ e j = z i := by
      rw [Finset.prod_eq_single i]
      · simp [he]
      · intro j _ hj; simp [he, Pi.single_eq_of_ne hj]
      · simp
    rw [this, mul_comm]
  have hshift : HasSum (fun β : ι → ℕ => (∏ j, z j ^ (β + e) j) • c (β + e)) (z i • T) := by
    simpa [hterm] using h.const_smul (z i)
  -- reindex: the multi-indices missed by the shift have `α i = 0`, where `c` vanishes
  have hinj : Function.Injective fun β : ι → ℕ => β + e := add_left_injective e
  have hzero : ∀ α : ι → ℕ, α ∉ Set.range (fun β : ι → ℕ => β + e) →
      (∏ j, z j ^ α j) • c α = 0 := by
    intro α hα
    have hai : α i = 0 := by
      by_contra hne
      refine hα ⟨fun j => α j - e j, ?_⟩
      funext j
      simp only [Pi.add_apply]
      rcases eq_or_ne j i with rfl | hj
      · simp only [he, Pi.single_eq_same]
        omega
      · simp [he, Pi.single_eq_of_ne hj]
    rw [hvanish α hai, smul_zero]
  exact (hinj.hasSum_iff hzero).1 hshift

/-- The shifted series is again analytic: dividing by a coordinate preserves analyticity. -/
theorem analyticAt_tsum_monomial_shift [CompleteSpace F] (c : (ι → ℕ) → F)
    (i : ι) {r : ℝ≥0} (hr : 0 < r)
    (hsum : Summable fun α : ι → ℕ => ‖c α‖ * (r : ℝ) ^ (∑ j, α j)) :
    AnalyticAt 𝕜
      (fun z : ι → 𝕜 => ∑' β : ι → ℕ, (∏ j, z j ^ β j) • c (β + (Pi.single i 1 : ι → ℕ))) 0 :=
  analyticAt_tsum_monomial _ hr (MultiIndex.summable_shift (by exact_mod_cast hr) i hsum)

/-- **Splitting a multi-index power series along a coordinate.**

Every series decomposes as the part not involving `z i` plus `z i` times the shifted series.
This is the `p = 1` case of the division lemma behind a Schwarz lemma for Cartesian
products: `f = f₀ + z i * f₁` with `f₀` of degree `0` in `z i`. -/
theorem hasSum_split_coord {c : (ι → ℕ) → F} (i : ι) {z : ι → 𝕜} {S T : F}
    (h₀ : HasSum (fun α : ι → ℕ => (∏ j, z j ^ α j) • (if α i = 0 then c α else 0)) S)
    (h₁ : HasSum (fun β : ι → ℕ =>
      (∏ j, z j ^ β j) • c (β + (Pi.single i 1 : ι → ℕ))) T) :
    HasSum (fun α : ι → ℕ => (∏ j, z j ^ α j) • c α) (S + z i • T) := by
  classical
  set d : (ι → ℕ) → F := fun α => if α i = 0 then 0 else c α with hd
  -- `d` is the part of `c` genuinely involving the `i`-th coordinate
  have hdvanish : ∀ α : ι → ℕ, α i = 0 → d α = 0 := fun α hα => by simp [hd, hα]
  have hdshift : ∀ β : ι → ℕ, d (β + (Pi.single i 1 : ι → ℕ)) = c (β + Pi.single i 1) := by
    intro β
    simp [hd]
  have h₁' : HasSum (fun β : ι → ℕ =>
      (∏ j, z j ^ β j) • d (β + (Pi.single i 1 : ι → ℕ))) T := by
    simpa [hdshift] using h₁
  have hsplit := h₀.add (hasSum_smul_shift i hdvanish h₁')
  refine hsplit.congr_fun fun α => ?_
  rw [← smul_add]
  congr 1
  by_cases hα : α i = 0 <;> simp [hd, hα]

/-- The part of a series not involving the `i`-th coordinate really does not: its value is
unchanged by moving `z i`. -/
theorem tsum_ite_coord_eq_update [CompleteSpace F] {c : (ι → ℕ) → F} (i : ι) (z : ι → 𝕜)
    (w : 𝕜) :
    (∑' α : ι → ℕ, (∏ j, z j ^ α j) • (if α i = 0 then c α else 0))
      = ∑' α : ι → ℕ, (∏ j, Function.update z i w j ^ α j) • (if α i = 0 then c α else 0) := by
  refine tsum_congr fun α => ?_
  by_cases hα : α i = 0
  · congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rcases eq_or_ne j i with rfl | hj
    · rw [hα]; simp
    · rw [Function.update_of_ne hj]
  · simp [hα]

/-- **Division by a power of a coordinate.**

If every coefficient with `α i < p` vanishes, the series is `z i ^ p` times the series with
the `i`-th exponent shifted down by `p`.  This is `hasSum_smul_shift` iterated, and is the
induction on the degree in the division lemma behind a Schwarz lemma for Cartesian
products. -/
theorem hasSum_smul_shift_pow {c : (ι → ℕ) → F} (i : ι) {z : ι → 𝕜} :
    ∀ (p : ℕ) {T : F}, (∀ α : ι → ℕ, α i < p → c α = 0) →
      HasSum (fun β : ι → ℕ => (∏ j, z j ^ β j) • c (β + (Pi.single i p : ι → ℕ))) T →
      HasSum (fun α : ι → ℕ => (∏ j, z j ^ α j) • c α) (z i ^ p • T) := by
  intro p
  induction p generalizing c with
  | zero => intro T _ h; simpa using h
  | succ p ih =>
    intro T hvanish h
    -- peel off one factor, then apply the inductive hypothesis to the shifted coefficients
    have hstep : ∀ β : ι → ℕ,
        c (β + (Pi.single i p : ι → ℕ) + (Pi.single i 1 : ι → ℕ))
          = c (β + (Pi.single i (p + 1) : ι → ℕ)) := by
      intro β
      rw [add_assoc, ← Pi.single_add]
    have hshift : HasSum (fun β : ι → ℕ =>
        (∏ j, z j ^ β j) • (fun α => c (α + (Pi.single i 1 : ι → ℕ)))
          (β + (Pi.single i p : ι → ℕ))) T := by
      simpa [hstep] using h
    have hvanish' : ∀ β : ι → ℕ, β i < p → c (β + (Pi.single i 1 : ι → ℕ)) = 0 := by
      intro β hβ
      refine hvanish _ ?_
      simp only [Pi.add_apply, Pi.single_eq_same]
      omega
    have hinner := ih (c := fun α => c (α + (Pi.single i 1 : ι → ℕ))) hvanish' hshift
    have houter := hasSum_smul_shift i (c := c) (fun α hα => hvanish α (by omega)) hinner
    rwa [smul_smul, ← pow_succ'] at houter

/-- Shifting a multi-index down by `p` in one coordinate keeps a series normally
convergent. -/
lemma summable_shift_pow {c : (ι → ℕ) → F} {r : ℝ} (hr : 0 < r) (i : ι) :
    ∀ (p : ℕ), (Summable fun α : ι → ℕ => ‖c α‖ * r ^ (∑ j, α j)) →
      Summable fun β : ι → ℕ => ‖c (β + (Pi.single i p : ι → ℕ))‖ * r ^ (∑ j, β j) := by
  intro p
  induction p generalizing c with
  | zero => intro hsum; simpa using hsum
  | succ p ih =>
    intro hsum
    have hstep : ∀ β : ι → ℕ,
        c (β + (Pi.single i p : ι → ℕ) + (Pi.single i 1 : ι → ℕ))
          = c (β + (Pi.single i (p + 1) : ι → ℕ)) := by
      intro β
      rw [add_assoc, ← Pi.single_add]
    have h1 := ih (c := fun α => c (α + (Pi.single i 1 : ι → ℕ))) (summable_shift hr i hsum)
    simpa [hstep] using h1

/-- The quotient of a normally convergent series by a power of a coordinate is again
analytic. -/
theorem analyticAt_tsum_monomial_shift_pow [CompleteSpace F] (c : (ι → ℕ) → F) (i : ι) (p : ℕ)
    {r : ℝ≥0} (hr : 0 < r)
    (hsum : Summable fun α : ι → ℕ => ‖c α‖ * (r : ℝ) ^ (∑ j, α j)) :
    AnalyticAt 𝕜 (fun z : ι → 𝕜 =>
      ∑' β : ι → ℕ, (∏ j, z j ^ β j) • c (β + (Pi.single i p : ι → ℕ))) 0 :=
  analyticAt_tsum_monomial _ hr (summable_shift_pow (by exact_mod_cast hr) i p hsum)

omit [DecidableEq ι] in
/-- A normally convergent multi-index series converges at every point of the polydisc. -/
lemma summable_monomial_smul [CompleteSpace F] {c : (ι → ℕ) → F} {ρ : ℝ} {z : ι → 𝕜}
    (hz : ‖z‖ ≤ ρ) (hsum : Summable fun α : ι → ℕ => ‖c α‖ * ρ ^ (∑ j, α j)) :
    Summable fun α : ι → ℕ => (∏ j, z j ^ α j) • c α := by
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun α => ?_) hsum)
  rw [norm_smul, norm_prod, mul_comm]
  gcongr
  calc ∏ j, ‖z j ^ α j‖ = ∏ j, ‖z j‖ ^ α j := by
        exact Finset.prod_congr rfl fun j _ => norm_pow _ _
    _ ≤ ∏ j, ρ ^ α j := by
        gcongr with j
        exact (norm_le_pi_norm z j).trans hz
    _ = ρ ^ (∑ j, α j) := by rw [← Finset.prod_pow_eq_pow_sum]

/-- The quotient of a normally convergent series by a power of a coordinate is analytic on
the whole polydisc of convergence. -/
theorem analyticOnNhd_tsum_monomial_shift_pow [CompleteSpace F] (c : (ι → ℕ) → F) (i : ι)
    (p : ℕ) {r : ℝ≥0} (hr : 0 < r)
    (hsum : Summable fun α : ι → ℕ => ‖c α‖ * (r : ℝ) ^ (∑ j, α j)) :
    AnalyticOnNhd 𝕜 (fun z : ι → 𝕜 =>
        ∑' β : ι → ℕ, (∏ j, z j ^ β j) • c (β + (Pi.single i p : ι → ℕ)))
      (Metric.eball (0 : ι → 𝕜) r) :=
  analyticOnNhd_tsum_monomial _ hr (summable_shift_pow (by exact_mod_cast hr) i p hsum)

/-- **Division of an analytic function by a power of a coordinate.**

If the multi-index coefficients of `f` all vanish below degree `m` in the `i`-th coordinate,
then `f = z i ^ m • g` with `g` analytic. -/
theorem exists_analyticAt_eq_pow_smul [CompleteSpace F] {f : (ι → 𝕜) → F}
    {p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F} {r : ℝ≥0} (hf : HasFPowerSeriesOnBall f p 0 r)
    (i : ι) (m : ℕ) (hvanish : ∀ α : ι → ℕ, α i < m → coeff p α = 0)
    {ρ : ℝ≥0} (hρ : 0 < ρ) (hρr : (ρ : ℝ≥0∞) ≤ r)
    (hconv : ∀ z : ι → 𝕜, ‖z‖ ≤ (ρ : ℝ) →
      Summable fun k => (Fintype.card ι : ℝ) ^ k * ‖p k‖ * ‖z‖ ^ k)
    (hsum : Summable fun α : ι → ℕ => ‖coeff p α‖ * (ρ : ℝ) ^ (∑ j, α j)) :
    ∃ g : (ι → 𝕜) → F, AnalyticOnNhd 𝕜 g (Metric.eball (0 : ι → 𝕜) ρ) ∧
      ∀ z : ι → 𝕜, ‖z‖ < (ρ : ℝ) → f z = z i ^ m • g z := by
  refine ⟨fun z => ∑' β : ι → ℕ, (∏ j, z j ^ β j) • coeff p (β + (Pi.single i m : ι → ℕ)),
    analyticOnNhd_tsum_monomial_shift_pow _ i m hρ hsum, fun z hz => ?_⟩
  have hshift : HasSum
      (fun β : ι → ℕ => (∏ j, z j ^ β j) • coeff p (β + (Pi.single i m : ι → ℕ)))
      (∑' β : ι → ℕ, (∏ j, z j ^ β j) • coeff p (β + (Pi.single i m : ι → ℕ))) :=
    (summable_monomial_smul hz.le (summable_shift_pow (by exact_mod_cast hρ) i m hsum)).hasSum
  have hfull := hasSum_smul_shift_pow (c := coeff p) i m hvanish hshift
  have hz' : ‖z‖ < (r : ℝ≥0) := by
    refine lt_of_lt_of_le hz ?_
    exact_mod_cast (ENNReal.coe_le_coe.1 hρr)
  exact (hasSum_coeff hf hz' (hconv z hz.le)).unique hfull

/-- **Division by a power of a coordinate, at a general centre.**

The same as `exists_analyticAt_eq_pow_smul` for a function analytic at `x`: if the
coefficients of the expansion at `x` vanish below degree `m` in the `i`-th coordinate, then
`f` is `(z i - x i) ^ m` times an analytic function.  Iterating this over the roots of a monic
polynomial `P` divides by `P (z i)`. -/
theorem exists_analyticAt_eq_sub_pow_smul [CompleteSpace F] {f : (ι → 𝕜) → F}
    {p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F} {x : ι → 𝕜} {r : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f p x r) (i : ι) (m : ℕ)
    (hvanish : ∀ α : ι → ℕ, α i < m → coeff p α = 0)
    {ρ : ℝ≥0} (hρ : 0 < ρ) (hρr : (ρ : ℝ≥0∞) ≤ r)
    (hconv : ∀ z : ι → 𝕜, ‖z‖ ≤ (ρ : ℝ) →
      Summable fun k => (Fintype.card ι : ℝ) ^ k * ‖p k‖ * ‖z‖ ^ k)
    (hsum : Summable fun α : ι → ℕ => ‖coeff p α‖ * (ρ : ℝ) ^ (∑ j, α j)) :
    ∃ g : (ι → 𝕜) → F, AnalyticOnNhd 𝕜 g (Metric.eball (0 : ι → 𝕜) ρ) ∧
      ∀ z : ι → 𝕜, ‖z‖ < (ρ : ℝ) → f (x + z) = z i ^ m • g z := by
  have hf0 : HasFPowerSeriesOnBall (fun w : ι → 𝕜 => f (x + w)) p 0 r := by
    simpa [sub_neg_eq_add, add_comm] using hf.comp_sub (-x)
  exact exists_analyticAt_eq_pow_smul hf0 i m hvanish hρ hρr hconv hsum

/-!
### Slices along a coordinate

Dividing by a linear factor `z i - ζ` is a one-variable operation performed with the other
coordinates held fixed.  `dslope` supplies the quotient and the identity it satisfies; what
has to be added in several variables is that the quotient is jointly analytic, which comes
from `exists_analyticAt_eq_sub_pow_smul`.
-/

/-- The slice of `f` along the `i`-th coordinate through `z`. -/
def slice (f : (ι → 𝕜) → F) (i : ι) (z : ι → 𝕜) : 𝕜 → F :=
  fun w => f (Function.update z i w)

omit [Fintype ι] [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F] in
@[simp] lemma slice_apply_self (f : (ι → 𝕜) → F) (i : ι) (z : ι → 𝕜) :
    slice f i z (z i) = f z := by simp [slice]

omit [Fintype ι] in
/-- **The slicewise divided difference.**  `dslope` of the slice divides the difference
between `f` and its restriction to the hyperplane `z i = ζ`. -/
theorem sub_smul_dslope_slice (f : (ι → 𝕜) → F) (i : ι) (ζ : 𝕜) (z : ι → 𝕜) :
    (z i - ζ) • dslope (slice f i z) ζ (z i) = f z - f (Function.update z i ζ) := by
  simp [slice]

/-- Off the hyperplane the quotient is the honest one, so it is analytic there. -/
theorem analyticAt_dslope_slice_of_ne {f : (ι → 𝕜) → F} (i : ι) (ζ : 𝕜) {x : ι → 𝕜}
    (hx : x i ≠ ζ) (hf : AnalyticAt 𝕜 f x)
    (hres : AnalyticAt 𝕜 (fun z : ι → 𝕜 => f (Function.update z i ζ)) x) :
    AnalyticAt 𝕜 (fun z : ι → 𝕜 => dslope (slice f i z) ζ (z i)) x := by
  have hcoord : AnalyticAt 𝕜 (fun z : ι → 𝕜 => z i - ζ) x :=
    (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι => 𝕜) i).analyticAt x |>.sub
      analyticAt_const
  have hne : (fun z : ι → 𝕜 => z i - ζ) x ≠ 0 := sub_ne_zero.2 hx
  have hform : ∀ᶠ z in nhds x,
      dslope (slice f i z) ζ (z i) = (z i - ζ)⁻¹ • (f z - f (Function.update z i ζ)) := by
    have hopen : {z : ι → 𝕜 | z i ≠ ζ} ∈ nhds x := by
      refine IsOpen.mem_nhds ?_ hx
      exact isOpen_ne.preimage (by fun_prop)
    filter_upwards [hopen] with z hz
    rw [← sub_smul_dslope_slice f i ζ z, smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hz), one_smul]
  exact ((hcoord.inv hne).smul (hf.sub hres)).congr (hform.mono fun z hz => hz.symm)

/-- If the multi-index coefficients vanish below degree `m` in the `i`-th coordinate, then the
slice of `f` through the centre along that coordinate has a zero of order at least `m`.

This is the bridge to one-variable reasoning: it is what lets a division by one linear factor
be followed by a division by the next, since a nonzero factor at the second root cannot absorb
the vanishing. -/
theorem exists_slice_eq_pow_smul [CompleteSpace F] {f : (ι → 𝕜) → F}
    {p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F} {x : ι → 𝕜} {r : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f p x r) (i : ι) (m : ℕ)
    (hvanish : ∀ α : ι → ℕ, α i < m → coeff p α = 0)
    {ρ : ℝ≥0} (hρ : 0 < ρ) (hρr : (ρ : ℝ≥0∞) ≤ r)
    (hconv : ∀ z : ι → 𝕜, ‖z‖ ≤ (ρ : ℝ) →
      Summable fun k => (Fintype.card ι : ℝ) ^ k * ‖p k‖ * ‖z‖ ^ k)
    (hsum : Summable fun α : ι → ℕ => ‖coeff p α‖ * (ρ : ℝ) ^ (∑ j, α j)) :
    ∃ g : 𝕜 → F, AnalyticAt 𝕜 g 0 ∧
      ∀ w : 𝕜, ‖w - x i‖ < (ρ : ℝ) →
        f (Function.update x i w) = (w - x i) ^ m • g (w - x i) := by
  obtain ⟨G, hG, hGeq⟩ := exists_analyticAt_eq_sub_pow_smul hf i m hvanish hρ hρr hconv hsum
  -- the line through `x` in the `i`-th direction
  set L : 𝕜 →L[𝕜] (ι → 𝕜) :=
    (ContinuousLinearMap.id 𝕜 𝕜).smulRight (Pi.single i 1 : ι → 𝕜) with hL
  have hLapp : ∀ u : 𝕜, L u = u • (Pi.single i 1 : ι → 𝕜) := fun u => rfl
  have hLnorm : ∀ u : 𝕜, ‖L u‖ = ‖u‖ := by
    intro u
    rw [hLapp, norm_smul, Pi.norm_single, norm_one, mul_one]
  have h0 : (0 : ι → 𝕜) ∈ Metric.eball (0 : ι → 𝕜) ρ :=
    Metric.mem_eball_self (by exact_mod_cast hρ)
  have hL0 : L (0 : 𝕜) = (0 : ι → 𝕜) := by simp [hLapp]
  have hcomp : AnalyticAt 𝕜 (fun u : 𝕜 => G (L u)) 0 :=
    (hG (L 0) (by rw [hL0]; exact h0)).comp (L.analyticAt 0)
  refine ⟨fun u => G (L u), hcomp, fun w hw => ?_⟩
  · have hxz : x + L (w - x i) = Function.update x i w := by
      funext j
      rcases eq_or_ne j i with rfl | hj
      · simp [hLapp]
      · simp [hLapp, Pi.single_eq_of_ne hj, Function.update_of_ne hj]
    have hcoord : (L (w - x i)) i = w - x i := by simp [hLapp]
    have := hGeq (L (w - x i)) (by rw [hLnorm]; exact hw)
    rw [hxz, hcoord] at this
    exact this

/-- **Splitting a multi-index power series along a power of a coordinate.**

`f = f₀ + z i ^ p * f₁`, where `f₀` collects the multi-indices of degree `< p` in the `i`-th
coordinate -- Waldschmidt's "polynomial in `z i` of degree `< p`" -- and `f₁` is the series
with that exponent shifted down by `p`.  This is Lemma 4.8 (c) of [waldschmidt2000] for a
single coordinate and a single monic factor `z i ^ p`. -/
theorem hasSum_split_coord_pow {c : (ι → ℕ) → F} (i : ι) (p : ℕ) {z : ι → 𝕜} {S T : F}
    (h₀ : HasSum (fun α : ι → ℕ => (∏ j, z j ^ α j) • (if α i < p then c α else 0)) S)
    (h₁ : HasSum (fun β : ι → ℕ =>
      (∏ j, z j ^ β j) • c (β + (Pi.single i p : ι → ℕ))) T) :
    HasSum (fun α : ι → ℕ => (∏ j, z j ^ α j) • c α) (S + z i ^ p • T) := by
  classical
  set d : (ι → ℕ) → F := fun α => if α i < p then 0 else c α with hd
  have hdvanish : ∀ α : ι → ℕ, α i < p → d α = 0 := fun α hα => by simp [hd, hα]
  have hdshift : ∀ β : ι → ℕ, d (β + (Pi.single i p : ι → ℕ)) = c (β + Pi.single i p) := by
    intro β
    simp [hd]
  have h₁' : HasSum (fun β : ι → ℕ =>
      (∏ j, z j ^ β j) • d (β + (Pi.single i p : ι → ℕ))) T := by
    simpa [hdshift] using h₁
  have hsplit := h₀.add (hasSum_smul_shift_pow i p hdvanish h₁')
  refine hsplit.congr_fun fun α => ?_
  rw [← smul_add]
  congr 1
  by_cases hα : α i < p <;> simp [hd, hα]

omit [DecidableEq ι] in
/-- Truncating the coefficients in one coordinate keeps a series normally convergent. -/
lemma summable_truncate {c : (ι → ℕ) → F} {r : ℝ} (hr : 0 ≤ r) (i : ι) (p : ℕ)
    (hsum : Summable fun α : ι → ℕ => ‖c α‖ * r ^ (∑ j, α j)) :
    Summable fun α : ι → ℕ => ‖if α i < p then c α else 0‖ * r ^ (∑ j, α j) := by
  classical
  refine Summable.of_nonneg_of_le (fun α => by positivity) (fun α => ?_) hsum
  gcongr
  by_cases hα : α i < p <;> simp [hα]

omit [DecidableEq ι] in
/-- The truncated part of the decomposition is analytic on the same polydisc. -/
theorem analyticOnNhd_tsum_monomial_truncate [CompleteSpace F] (c : (ι → ℕ) → F) (i : ι)
    (p : ℕ) {r : ℝ≥0} (hr : 0 < r)
    (hsum : Summable fun α : ι → ℕ => ‖c α‖ * (r : ℝ) ^ (∑ j, α j)) :
    AnalyticOnNhd 𝕜 (fun z : ι → 𝕜 =>
        ∑' α : ι → ℕ, (∏ j, z j ^ α j) • (if α i < p then c α else 0))
      (Metric.eball (0 : ι → 𝕜) r) :=
  analyticOnNhd_tsum_monomial _ hr (MultiIndex.summable_truncate (by positivity) i p hsum)

end MultiIndex

end Coordinate

section LinearFactor

open Metric Function Filter Topology

namespace MultiIndex

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝕜 : Type*} [RCLike 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-!
### Division by a linear factor
-/

omit [DecidableEq ι] [CompleteSpace F] in
/-- The restriction of `f` to the hyperplane `z i = ζ`, as a function on the whole space. -/
lemma analyticAt_comp_update [DecidableEq ι] {f : (ι → 𝕜) → F} (i : ι) (ζ : 𝕜) {x : ι → 𝕜}
    (hf : AnalyticAt 𝕜 f (update x i ζ)) :
    AnalyticAt 𝕜 (fun z : ι → 𝕜 => f (update z i ζ)) x := by
  have hupd : (fun z : ι → 𝕜 => update z i ζ)
      = fun z : ι → 𝕜 => z + (ζ - z i) • (Pi.single i 1 : ι → 𝕜) := by
    funext z j
    rcases eq_or_ne j i with rfl | hj
    · simp
    · simp [update_of_ne hj, Pi.single_eq_of_ne hj]
  have haff : AnalyticAt 𝕜 (fun z : ι → 𝕜 => update z i ζ) x := by
    rw [hupd]
    exact analyticAt_id.add ((analyticAt_const.sub
      ((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι => 𝕜) i).analyticAt x)).smul
        analyticAt_const)
  exact hf.comp_of_eq haff rfl

/-- **Division by a linear factor, across the hyperplane.**

If `f` is analytic at a point `x` of the hyperplane `z i = ζ`, then so is the divided
difference `z ↦ dslope (slice f i z) ζ (z i)`, which is `(f z - f (update z i ζ)) / (z i - ζ)`
off the hyperplane and the partial derivative on it.  In the multi-index expansion about `x` it
is the series with the `i`-th exponent shifted down by one. -/
theorem analyticAt_dslope_slice_of_eq {f : (ι → 𝕜) → F} (i : ι) {ζ : 𝕜} {x : ι → 𝕜}
    (hx : x i = ζ) (hf : AnalyticAt 𝕜 f x) :
    AnalyticAt 𝕜 (fun z : ι → 𝕜 => dslope (slice f i z) ζ (z i)) x := by
  obtain ⟨ρ, hρ, hsum, hhs⟩ := exists_hasSum_of_analyticAt hf
  set c := taylorCoeff f x with hc
  set G : (ι → 𝕜) → F := fun y =>
    ∑' β : ι → ℕ, (∏ j, y j ^ β j) • c (β + (Pi.single i 1 : ι → ℕ)) with hG
  have hGan : AnalyticOnNhd 𝕜 G (eball 0 ρ) := analyticOnNhd_tsum_monomial_shift_pow c i 1 hρ hsum
  have hnorm_upd : ∀ (y : ι → 𝕜) (v : 𝕜), ‖v‖ ≤ ‖y‖ → ‖update y i v‖ ≤ ‖y‖ := by
    intro y v hv
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg y)).2 fun j => ?_
    rcases eq_or_ne j i with rfl | hj
    · simpa using hv
    · rw [update_of_ne hj]; exact norm_le_pi_norm y j
  -- the splitting `f (x + y) = f (x + update y i 0) + y i • G y`
  have hsplit : ∀ y : ι → 𝕜, ‖y‖ < ρ → f (x + y) = f (x + update y i 0) + y i • G y := by
    intro y hy
    have h₁ : HasSum (fun β : ι → ℕ => (∏ j, y j ^ β j) • c (β + (Pi.single i 1 : ι → ℕ)))
        (G y) :=
      (summable_monomial_smul hy.le (summable_shift_pow (by exact_mod_cast hρ) i 1 hsum)).hasSum
    have hite : Summable fun α : ι → ℕ =>
        ‖(if α i = 0 then c α else 0)‖ * (ρ : ℝ) ^ (∑ j, α j) := by
      refine hsum.of_nonneg_of_le (fun _ => by positivity) fun α => ?_
      by_cases hα : α i = 0
      · simp [hα]
      · simp only [hα, ↓reduceIte, norm_zero, zero_mul]
        positivity
    have h₀ := (summable_monomial_smul hy.le hite).hasSum
    have hfull := hasSum_split_coord i h₀ h₁
    rw [(hhs y hy).unique hfull]
    congr 1
    rw [tsum_ite_coord_eq_update i y 0]
    have hy0 : ‖update y i 0‖ < ρ := (hnorm_upd y 0 (by simp)).trans_lt hy
    refine (tsum_congr fun α => ?_).trans (hhs _ hy0).tsum_eq
    by_cases hα : α i = 0
    · simp [hα]
    · rw [ite_eq_right_iff.2 (fun h => absurd h hα), smul_zero,
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hα]), zero_smul]
  have hq : ∀ y : ι → 𝕜, ‖y‖ < ρ → dslope (slice f i (x + y)) ζ ((x + y) i) = G y := by
    intro y hy
    have hxy : (x + y) i = ζ + y i := by simp [hx]
    have hupd : update (x + y) i ζ = x + update y i 0 := by
      funext j
      rcases eq_or_ne j i with rfl | hj
      · simp [hx]
      · simp [update_of_ne hj]
    rcases eq_or_ne (y i) 0 with hyi | hyi
    · -- on the hyperplane the divided difference is a derivative
      rw [hxy, hyi, add_zero, dslope_same]
      have hline : ∀ w : 𝕜,
          update (x + y) i w = x + (y + (w - ζ) • (Pi.single i 1 : ι → 𝕜)) := by
        intro w
        funext j
        rcases eq_or_ne j i with rfl | hj
        · simp [hx, hyi]
        · simp [update_of_ne hj, Pi.single_eq_of_ne hj]
      set φ : 𝕜 → F := fun w => G (y + (w - ζ) • (Pi.single i 1 : ι → 𝕜)) with hφdef
      have hmem : ∀ᶠ w in 𝓝 ζ, ‖y + (w - ζ) • (Pi.single i 1 : ι → 𝕜)‖ < ρ := by
        have hcont : Continuous fun w : 𝕜 => ‖y + (w - ζ) • (Pi.single i 1 : ι → 𝕜)‖ := by
          fun_prop
        have h0 : ‖y + (ζ - ζ) • (Pi.single i 1 : ι → 𝕜)‖ < ρ := by simpa using hy
        exact hcont.continuousAt.eventually_lt continuousAt_const h0
      have hev : slice f i (x + y) =ᶠ[𝓝 ζ] fun w => f (x + y) + (w - ζ) • φ w := by
        filter_upwards [hmem] with w hw
        rw [slice, hline, hsplit _ hw]
        have hback : update (y + (w - ζ) • (Pi.single i 1 : ι → 𝕜)) i 0 = y := by
          funext j
          rcases eq_or_ne j i with rfl | hj
          · simp [hyi]
          · simp [update_of_ne hj, Pi.single_eq_of_ne hj]
        have hcoord : (y + (w - ζ) • (Pi.single i 1 : ι → 𝕜)) i = w - ζ := by simp [hyi]
        rw [hback, hcoord]
      have hφ : DifferentiableAt 𝕜 φ ζ := by
        have hGy : AnalyticAt 𝕜 G (y + (ζ - ζ) • (Pi.single i 1 : ι → 𝕜)) :=
          hGan _ (by rw [Metric.eball_coe, mem_ball_zero_iff]; simpa using hy)
        have hlin : DifferentiableAt 𝕜 (fun w : 𝕜 => y + (w - ζ) • (Pi.single i 1 : ι → 𝕜)) ζ := by
          fun_prop
        exact hGy.differentiableAt.comp ζ hlin
      have hderiv : HasDerivAt (fun w => f (x + y) + (w - ζ) • φ w) (φ ζ) ζ := by
        have h1 : HasDerivAt (fun w : 𝕜 => w - ζ) 1 ζ := (hasDerivAt_id ζ).sub_const ζ
        simpa using (h1.smul hφ.hasDerivAt).const_add (f (x + y))
      rw [(hderiv.congr_of_eventuallyEq hev).deriv]
      simp [hφdef]
    · -- off the hyperplane it is the honest quotient
      have hkey := sub_smul_dslope_slice f i ζ (x + y)
      rw [hupd, hsplit y hy, add_sub_cancel_left, hxy, add_sub_cancel_left] at hkey
      rw [hxy]
      exact smul_right_injective F hyi hkey
  have hev : (fun z : ι → 𝕜 => dslope (slice f i z) ζ (z i)) =ᶠ[𝓝 x]
      fun z => G (z - x) := by
    filter_upwards [ball_mem_nhds x (by exact_mod_cast hρ : (0 : ℝ) < ρ)] with z hz
    have := hq (z - x) (by simpa [dist_eq_norm] using hz)
    simpa using this
  have hGx : AnalyticAt 𝕜 (fun z : ι → 𝕜 => G (z - x)) x :=
    (hGan 0 (by rw [Metric.eball_coe, mem_ball_zero_iff]; simpa using hρ)).comp_of_eq
      (analyticAt_id.sub analyticAt_const) (by simp)
  exact hGx.congr hev.symm

/-- **Division by a linear factor.**  The divided difference of an analytic function in one
coordinate is analytic, both on and off the hyperplane. -/
theorem analyticAt_dslope_slice {f : (ι → 𝕜) → F} (i : ι) (ζ : 𝕜) {x : ι → 𝕜}
    (hf : AnalyticAt 𝕜 f x) (hres : AnalyticAt 𝕜 f (update x i ζ)) :
    AnalyticAt 𝕜 (fun z : ι → 𝕜 => dslope (slice f i z) ζ (z i)) x := by
  rcases eq_or_ne (x i) ζ with h | h
  · exact analyticAt_dslope_slice_of_eq i h hf
  · exact analyticAt_dslope_slice_of_ne i ζ h hf (analyticAt_comp_update i ζ hres)

end MultiIndex

end LinearFactor
