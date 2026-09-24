/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.NumberTheory.Transcendental.Baker.SchwarzProduct

/-!
# Exponential polynomials

The functions `z ↦ z ^ τ * exp (w · z)` on `ℂⁿ` from which the auxiliary function of the
Schneider–Lang criterion is built, and their Taylor coefficients at an arbitrary point.  This
is Lemma 4.9 of Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, in the
form of Taylor coefficients `D^σ φ (ξ) / σ!` rather than derivatives.

A function of the form `∏ᵢ gᵢ (zᵢ)` has as multi-index Taylor coefficients the products of
the one-variable ones (`hasSum_prod_pi`), and `(ξ + h) ^ τ e ^ {w h}` has the one-variable
coefficients `∑_{k ≤ σ} (τ choose k) ξ ^ (τ - k) w ^ (σ - k) / (σ - k)!`.

## Main statements

* `hasSum_prod_pi`: a finite product of absolutely convergent series is the sum, over
  multi-indices, of the products of their terms.
* `MultiIndex.taylorCoeff_expMonomial`: Lemma 4.9.
-/

@[expose] public section

open Finset

universe u

variable {R : Type*} [NormedCommRing R] [CompleteSpace R]

/-- The statement of `hasSum_prod_pi` for the index type `ι`. -/
def ProdPiStmt (R : Type*) [NormedCommRing R] (ι : Type u) [Fintype ι] : Prop :=
  ∀ f : ι → ℕ → R, (∀ i, Summable fun k => ‖f i k‖) →
    HasSum (fun σ : ι → ℕ => ∏ i, f i (σ i)) (∏ i, ∑' k, f i k) ∧
      Summable fun σ : ι → ℕ => ‖∏ i, f i (σ i)‖

omit [CompleteSpace R] in
lemma prodPiStmt_of_equiv {α β : Type u} [Fintype β] (e : α ≃ β)
    (ih : @ProdPiStmt R _ α (Fintype.ofEquiv β e.symm)) : ProdPiStmt R β := by
  intro f hf
  let _ : Fintype α := Fintype.ofEquiv β e.symm
  obtain ⟨h1, h2⟩ := ih (fun a => f (e a)) fun a => hf (e a)
  set E : (α → ℕ) ≃ (β → ℕ) := e.arrowCongr (Equiv.refl ℕ) with hE
  have hcomp : ∀ σ : α → ℕ, ∏ b, f b ((E σ) b) = ∏ a, f (e a) (σ a) := by
    intro σ
    rw [← e.prod_comp]
    simp [hE, Equiv.arrowCongr_apply]
  have hsum : ∏ b, ∑' k, f b k = ∏ a, ∑' k, f (e a) k := (e.prod_comp _).symm
  refine ⟨?_, ?_⟩
  · rw [← E.hasSum_iff, hsum]
    exact h1.congr_fun fun σ => hcomp σ
  · rw [← E.summable_iff]
    refine h2.congr fun σ => ?_
    simp only [Function.comp_apply, hcomp]

omit [CompleteSpace R] in
lemma prodPiStmt_empty : ProdPiStmt R PEmpty := by
  intro f _
  have hprod : ∀ σ : PEmpty → ℕ, ∏ i, f i (σ i) = 1 := fun σ => Finset.prod_of_isEmpty _
  have h1 : HasSum (fun σ : PEmpty → ℕ => ∏ i, f i (σ i)) 1 := by
    have := hasSum_single (f := fun σ : PEmpty → ℕ => ∏ i, f i (σ i)) default
      fun σ' hσ' => absurd (Subsingleton.elim σ' default) hσ'
    rwa [hprod] at this
  refine ⟨by rwa [Finset.prod_of_isEmpty], ?_⟩
  exact (hasSum_single (f := fun σ : PEmpty → ℕ => ‖∏ i, f i (σ i)‖) default
    fun σ' hσ' => absurd (Subsingleton.elim σ' default) hσ').summable

lemma prodPiStmt_option {α : Type u} [Fintype α] (ih : ProdPiStmt R α) :
    ProdPiStmt R (Option α) := by
  intro f hf
  obtain ⟨h1, h2⟩ := ih (fun a => f (some a)) fun a => hf (some a)
  have hs : Summable fun x : ℕ × (α → ℕ) => f none x.1 * ∏ i, f (some i) (x.2 i) :=
    summable_mul_of_summable_norm (f := f none) (g := fun σ : α → ℕ => ∏ i, f (some i) (σ i))
      (hf none) h2
  have hmul := HasSum.mul (hf none).of_norm.hasSum h1 hs
  have hg : ∀ x : ℕ × (α → ℕ),
      ∏ i, f i ((Equiv.piOptionEquivProd.symm x : Option α → ℕ) i) =
        f none x.1 * ∏ i, f (some i) (x.2 i) := fun x => by
    rw [Fintype.prod_option]
    rfl
  refine ⟨(Equiv.piOptionEquivProd.symm.hasSum_iff).1 ?_,
    (Equiv.piOptionEquivProd.symm.summable_iff).1 ?_⟩
  · rw [Fintype.prod_option]
    exact hmul.congr_fun fun x => hg x
  · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => ?_)
      ((hf none).mul_norm h2)
    simp only [Function.comp_apply, hg]
    exact le_rfl

/-- **Products of absolutely convergent series.**  For finitely many absolutely convergent
series `∑ₖ f i k` in a complete normed commutative ring, the family
`σ ↦ ∏ i, f i (σ i)` over multi-indices `σ : ι → ℕ` is absolutely summable with sum
`∏ i, ∑' k, f i k`. -/
theorem hasSum_prod_pi {ι : Type u} [Fintype ι] (f : ι → ℕ → R)
    (hf : ∀ i, Summable fun k => ‖f i k‖) :
    HasSum (fun σ : ι → ℕ => ∏ i, f i (σ i)) (∏ i, ∑' k, f i k) ∧
      Summable fun σ : ι → ℕ => ‖∏ i, f i (σ i)‖ := by
  have key : ProdPiStmt R ι := Fintype.induction_empty_option (P := fun ι _ => ProdPiStmt R ι)
    (fun _ _ _ e ih => prodPiStmt_of_equiv e ih) prodPiStmt_empty
    (fun _ _ ih => prodPiStmt_option ih) ι
  exact key f hf

/-!
### One variable
-/

/-- The coefficient of `h ^ k` in `(ξ + h) ^ τ * exp (w h)`. -/
noncomputable def expCoeff (τ : ℕ) (ξ w : ℂ) (k : ℕ) : ℂ :=
  ∑ j ∈ range (k + 1), (τ.choose j : ℂ) * ξ ^ (τ - j) * (w ^ (k - j) / (k - j).factorial)

lemma hasSum_cexp_series (x : ℂ) : HasSum (fun n => x ^ n / n.factorial) (Complex.exp x) := by
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.expSeries_div_hasSum_exp x

/-- **The Taylor series of `(ξ + h) ^ τ e ^ {w h}`**, absolutely convergent everywhere. -/
theorem hasSum_expCoeff (τ : ℕ) (ξ w y : ℂ) :
    HasSum (fun k => expCoeff τ ξ w k * y ^ k) ((ξ + y) ^ τ * Complex.exp (w * y)) ∧
      Summable fun k => ‖expCoeff τ ξ w k * y ^ k‖ := by
  set f : ℕ → ℂ := fun j => (τ.choose j : ℂ) * ξ ^ (τ - j) * y ^ j with hf
  set g : ℕ → ℂ := fun i => (w * y) ^ i / i.factorial with hg
  have hf0 : ∀ j ∉ range (τ + 1), f j = 0 := fun j hj => by
    rw [Finset.mem_range, not_lt] at hj
    simp [hf, Nat.choose_eq_zero_of_lt (by omega : τ < j)]
  have hfs : Summable fun j => ‖f j‖ :=
    summable_of_ne_finset_zero (s := range (τ + 1)) fun j hj => by simp [hf0 j hj]
  have hgs : Summable fun i => ‖g i‖ := by
    refine (Real.summable_pow_div_factorial ‖w * y‖).congr fun i => ?_
    simp [hg, norm_pow]
  have hfsum : ∑' j, f j = (ξ + y) ^ τ := by
    rw [tsum_eq_sum hf0, add_comm ξ y, add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hf]
    ring
  have hgsum : ∑' i, g i = Complex.exp (w * y) := (hasSum_cexp_series (w * y)).tsum_eq
  have hterm : ∀ k, ∑ j ∈ range (k + 1), f j * g (k - j) = expCoeff τ ξ w k * y ^ k := by
    intro k
    rw [expCoeff, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    simp only [hf, hg, mul_pow]
    rw [show y ^ k = y ^ j * y ^ (k - j) by rw [← pow_add, Nat.add_sub_cancel' hjk]]
    ring
  have h := hasSum_sum_range_mul_of_summable_norm hfs hgs
  rw [hfsum, hgsum] at h
  refine ⟨h.congr_fun fun k => (hterm k).symm, ?_⟩
  exact (summable_norm_sum_mul_range_of_summable_norm hfs hgs).congr fun k => by rw [hterm]

/-!
### Several variables: Lemma 4.9
-/

namespace MultiIndex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The exponential monomial `z ↦ z ^ τ * exp (w · z)` on `ℂⁿ`. -/
noncomputable def expMonomial (τ : ι → ℕ) (w : ι → ℂ) (z : ι → ℂ) : ℂ :=
  (∏ v, z v ^ τ v) * Complex.exp (∑ v, w v * z v)

omit [DecidableEq ι] in
lemma analyticAt_expMonomial (τ : ι → ℕ) (w : ι → ℂ) (y : ι → ℂ) :
    AnalyticAt ℂ (expMonomial τ w) y := by
  have hcoord : ∀ v, AnalyticAt ℂ (fun z : ι → ℂ => z v) y := fun v =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) v).analyticAt y
  refine (Finset.analyticAt_fun_prod _ fun v _ => (hcoord v).pow _).mul ?_
  exact analyticAt_cexp.comp (Finset.analyticAt_fun_sum _ fun v _ =>
    analyticAt_const.mul (hcoord v))

/-- The multi-index Taylor coefficients of `expMonomial τ w` at `ξ`. -/
noncomputable def expMonomialCoeff (τ : ι → ℕ) (w ξ : ι → ℂ) (σ : ι → ℕ) : ℂ :=
  Complex.exp (∑ v, w v * ξ v) * ∏ v, expCoeff (τ v) (ξ v) (w v) (σ v)

omit [DecidableEq ι] in
/-- **The expansion of an exponential monomial at an arbitrary point**, absolutely convergent
on every polydisc. -/
theorem hasSum_expMonomial (τ : ι → ℕ) (w ξ : ι → ℂ) (y : ι → ℂ) :
    HasSum (fun σ : ι → ℕ => (∏ v, y v ^ σ v) • expMonomialCoeff τ w ξ σ)
      (expMonomial τ w (ξ + y)) := by
  obtain ⟨h1, -⟩ := hasSum_prod_pi (fun v k => expCoeff (τ v) (ξ v) (w v) k * y v ^ k)
    fun v => (hasSum_expCoeff (τ v) (ξ v) (w v) (y v)).2
  have hval : ∏ v, ∑' k, expCoeff (τ v) (ξ v) (w v) k * y v ^ k =
      ∏ v, (ξ v + y v) ^ τ v * Complex.exp (w v * y v) :=
    Finset.prod_congr rfl fun v _ => (hasSum_expCoeff (τ v) (ξ v) (w v) (y v)).1.tsum_eq
  rw [hval] at h1
  have h2 := h1.mul_left (Complex.exp (∑ v, w v * ξ v))
  have htot : Complex.exp (∑ v, w v * ξ v) * ∏ v, (ξ v + y v) ^ τ v * Complex.exp (w v * y v)
      = expMonomial τ w (ξ + y) := by
    rw [expMonomial, Finset.prod_mul_distrib, ← Complex.exp_sum]
    simp only [Pi.add_apply]
    rw [show ∑ v, w v * (ξ v + y v) = ∑ v, w v * ξ v + ∑ v, w v * y v by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun v _ => by ring,
      Complex.exp_add]
    ring
  rw [htot] at h2
  refine h2.congr_fun fun σ => ?_
  rw [expMonomialCoeff, smul_eq_mul, Finset.prod_mul_distrib]
  ring

omit [DecidableEq ι] in
theorem summable_expMonomialCoeff (τ : ι → ℕ) (w ξ : ι → ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    Summable fun σ : ι → ℕ => ‖expMonomialCoeff τ w ξ σ‖ * ρ ^ (∑ v, σ v) := by
  obtain ⟨-, h2⟩ := hasSum_prod_pi (fun v k => expCoeff (τ v) (ξ v) (w v) k * (ρ : ℂ) ^ k)
    fun v => (hasSum_expCoeff (τ v) (ξ v) (w v) ρ).2
  refine (h2.mul_left ‖Complex.exp (∑ v, w v * ξ v)‖).congr fun σ => ?_
  rw [expMonomialCoeff, norm_mul, norm_prod, norm_prod, mul_assoc, ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hρ]

/-- **Lemma 4.9 of [waldschmidt2000]**, in Taylor-coefficient form: the coefficient of
`(z - ξ) ^ σ` in `z ^ τ exp (w · z)` is
`exp (w · ξ) ∏_v ∑_{j ≤ σ_v} (τ_v choose j) ξ_v ^ (τ_v - j) w_v ^ (σ_v - j) / (σ_v - j)!`. -/
theorem taylorCoeff_expMonomial (τ : ι → ℕ) (w ξ : ι → ℂ) (σ : ι → ℕ) :
    taylorCoeff (expMonomial τ w) ξ σ = expMonomialCoeff τ w ξ σ :=
  taylorCoeff_eq_of_hasSum (ρ := 1) one_pos
    (by simpa using summable_expMonomialCoeff τ w ξ 1 zero_le_one)
    (fun y _ => hasSum_expMonomial τ w ξ y) σ

end MultiIndex
