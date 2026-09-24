/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Linear independence of exponential polynomials

Polynomials times exponentials with distinct frequencies are linearly independent: if
`∑_c Q_c (ζ) e ^ {c ζ} = 0` for all `ζ ∈ ℂ`, with distinct `c`, then every `Q_c` is zero.  In
several variables the same holds for `∑_w P_w (z) e ^ {w · z}`, by restricting to a line on
which the frequencies stay distinct and the polynomials stay nonzero.

This is what makes the auxiliary function of the Schneider–Lang criterion nonzero.

## Main statements

* `ExpPoly.eq_zero_of_sum_eval_mul_cexp`: one variable.
* `ExpPoly.eq_zero_of_sum_eval_mul_cexp_pi`: several variables.
-/

@[expose] public section

open Polynomial Finset

namespace ExpPoly

/-- The size of a family of polynomials: the sum over its nonzero members of `natDegree + 1`. -/
noncomputable def size (T : Finset ℂ) (Q : ℂ → ℂ[X]) : ℕ :=
  ∑ c ∈ T, if Q c = 0 then 0 else (Q c).natDegree + 1

lemma derivative_add_C_mul {Q : ℂ[X]} (hQ : Q ≠ 0) {a : ℂ} (ha : a ≠ 0) :
    derivative Q + C a * Q ≠ 0 ∧ (derivative Q + C a * Q).natDegree = Q.natDegree := by
  set d := Q.natDegree with hd
  have hcoeff : (derivative Q + C a * Q).coeff d = a * Q.leadingCoeff := by
    rw [coeff_add, coeff_derivative, coeff_C_mul,
      coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree < d + 1), zero_mul, zero_add]
    rfl
  have hne : (derivative Q + C a * Q).coeff d ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero ha (leadingCoeff_ne_zero.2 hQ)
  have hle : (derivative Q + C a * Q).natDegree ≤ d :=
    natDegree_add_le_of_degree_le ((natDegree_derivative_le Q).trans (by omega))
      (natDegree_C_mul_le a Q)
  exact ⟨fun h => hne (by rw [h, coeff_zero]), le_antisymm hle (le_natDegree_of_ne_zero hne)⟩

/-- **Exponential polynomials in one variable.**  If `∑_{c ∈ T} Q_c (ζ) e ^ {c ζ} = 0` for all
`ζ`, then every `Q_c` is zero. -/
theorem eq_zero_of_sum_eval_mul_cexp (T : Finset ℂ) (Q : ℂ → ℂ[X])
    (hQ : ∀ ζ : ℂ, ∑ c ∈ T, (Q c).eval ζ * Complex.exp (c * ζ) = 0) : ∀ c ∈ T, Q c = 0 := by
  suffices key : ∀ (N : ℕ) (Q : ℂ → ℂ[X]), size T Q ≤ N →
      (∀ ζ : ℂ, ∑ c ∈ T, (Q c).eval ζ * Complex.exp (c * ζ) = 0) → ∀ c ∈ T, Q c = 0 from
    key _ Q le_rfl hQ
  intro N
  induction N with
  | zero =>
    intro Q hs _ c hc
    by_contra h
    have := Finset.single_le_sum (f := fun c => if Q c = 0 then 0 else (Q c).natDegree + 1)
      (fun _ _ => Nat.zero_le _) hc
    simp only [h, ↓reduceIte] at this
    unfold size at hs
    omega
  | succ N ih =>
    intro Q hs hQ
    by_contra hall
    push Not at hall
    obtain ⟨c₀, hc₀, hQc₀⟩ := hall
    set Q' : ℂ → ℂ[X] := fun c => derivative (Q c) + C (c - c₀) * Q c with hQ'
    -- the new family is again a vanishing combination
    have hid' : ∀ ζ : ℂ, ∑ c ∈ T, (Q' c).eval ζ * Complex.exp (c * ζ) = 0 := by
      intro ζ
      set G : ℂ → ℂ := fun ζ => ∑ c ∈ T, (Q c).eval ζ * Complex.exp ((c - c₀) * ζ) with hG
      have hG0 : G = fun _ => 0 := by
        funext ζ
        have h := hQ ζ
        have : G ζ = Complex.exp (-c₀ * ζ) * ∑ c ∈ T, (Q c).eval ζ * Complex.exp (c * ζ) := by
          rw [hG, Finset.mul_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [show (c - c₀) * ζ = -c₀ * ζ + c * ζ by ring, Complex.exp_add]
          ring
        rw [this, h, mul_zero]
      have hderiv : HasDerivAt G (∑ c ∈ T, ((derivative (Q c)).eval ζ *
          Complex.exp ((c - c₀) * ζ) + (Q c).eval ζ *
            ((c - c₀) * Complex.exp ((c - c₀) * ζ)))) ζ := by
        refine HasDerivAt.fun_sum fun c _ => ?_
        refine ((Q c).hasDerivAt ζ).mul ?_
        have := ((hasDerivAt_id ζ).const_mul (c - c₀)).cexp
        simpa [mul_comm] using this
      rw [hG0] at hderiv
      have h0 := hderiv.unique (hasDerivAt_const ζ (0 : ℂ))
      have : ∑ c ∈ T, (Q' c).eval ζ * Complex.exp (c * ζ) = Complex.exp (c₀ * ζ) *
          ∑ c ∈ T, ((derivative (Q c)).eval ζ * Complex.exp ((c - c₀) * ζ) +
            (Q c).eval ζ * ((c - c₀) * Complex.exp ((c - c₀) * ζ))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        simp only [hQ', eval_add, eval_mul, eval_C]
        rw [show c * ζ = c₀ * ζ + (c - c₀) * ζ by ring, Complex.exp_add]
        ring
      rw [this, h0, mul_zero]
    -- and it is smaller
    have hsize : size T Q' < size T Q := by
      refine Finset.sum_lt_sum (fun c hc => ?_) ⟨c₀, hc₀, ?_⟩
      · by_cases hcc : c = c₀
        · subst hcc
          simp only [hQ', sub_self, map_zero, zero_mul, add_zero, hQc₀, ↓reduceIte]
          by_cases hd : derivative (Q c) = 0
          · simp [hd]
          · simp only [hd, ↓reduceIte]
            have hdeg : (Q c).natDegree ≠ 0 := fun h0 => hd (derivative_of_natDegree_zero h0)
            have := natDegree_derivative_lt hdeg
            omega
        · by_cases hQc : Q c = 0
          · simp [hQ', hQc]
          · obtain ⟨hne, hdeg⟩ := derivative_add_C_mul hQc (sub_ne_zero.2 hcc)
            simp only [hQ', hne, hQc, ↓reduceIte, hdeg, le_refl]
      · simp only [hQ', sub_self, map_zero, zero_mul, add_zero, hQc₀, ↓reduceIte]
        by_cases hd : derivative (Q c₀) = 0
        · simp [hd]
        · simp only [hd, ↓reduceIte]
          have hdeg : (Q c₀).natDegree ≠ 0 := fun h0 => hd (derivative_of_natDegree_zero h0)
          have := natDegree_derivative_lt hdeg
          omega
    have hQ'0 := ih Q' (by omega) hid'
    -- recover `Q`
    have hne : ∀ c ∈ T, c ≠ c₀ → Q c = 0 := fun c hc hcc => by
      by_contra h
      exact (derivative_add_C_mul h (sub_ne_zero.2 hcc)).1 (hQ'0 c hc)
    have hd0 : derivative (Q c₀) = 0 := by simpa [hQ'] using hQ'0 c₀ hc₀
    have hconst : Q c₀ = C ((Q c₀).coeff 0) :=
      eq_C_of_natDegree_eq_zero (derivative_eq_zero.1 hd0)
    have h0 := hQ 0
    rw [Finset.sum_eq_single c₀ (fun c hc hcc => by rw [hne c hc hcc, eval_zero, zero_mul])
      (fun h => absurd hc₀ h), hconst, eval_C, mul_zero, Complex.exp_zero, mul_one] at h0
    exact hQc₀ (by rw [hconst, h0, map_zero])

/-- One variable, with frequencies `c a` injective on an arbitrary finite index set. -/
theorem eq_zero_of_sum_eval_mul_cexp' {α : Type*} (T : Finset α) (c : α → ℂ)
    (hc : Set.InjOn c T) (Q : α → ℂ[X])
    (hQ : ∀ ζ : ℂ, ∑ a ∈ T, (Q a).eval ζ * Complex.exp (c a * ζ) = 0) : ∀ a ∈ T, Q a = 0 := by
  classical
  set Q' : ℂ → ℂ[X] := fun b => ∑ a ∈ T.filter (fun a => c a = b), Q a with hQ'def
  have hQ' : ∀ a ∈ T, Q' (c a) = Q a := fun a ha => by
    simp only [hQ'def]
    rw [Finset.sum_eq_single_of_mem a (by simp [ha])]
    intro a' ha' hne
    exact absurd (hc (Finset.mem_filter.1 ha').1 ha (Finset.mem_filter.1 ha').2) hne
  have hid : ∀ ζ : ℂ, ∑ b ∈ T.image c, (Q' b).eval ζ * Complex.exp (b * ζ) = 0 := by
    intro ζ
    rw [Finset.sum_image fun a ha a' ha' h => hc ha ha' h, ← hQ ζ]
    exact Finset.sum_congr rfl fun a ha => by rw [hQ' a ha]
  intro a ha
  rw [← hQ' a ha]
  exact eq_zero_of_sum_eval_mul_cexp _ Q' hid _ (Finset.mem_image_of_mem c ha)

variable {ι : Type*} [Fintype ι]

/-- The linear form `z ↦ ∑ v, a v * z v` as a polynomial. -/
noncomputable def linForm (a : ι → ℂ) : MvPolynomial ι ℂ :=
  ∑ v, MvPolynomial.C (a v) * MvPolynomial.X v

lemma eval_linForm (a z : ι → ℂ) : MvPolynomial.eval z (linForm a) = ∑ v, a v * z v := by
  simp [linForm]

lemma linForm_ne_zero {a : ι → ℂ} (ha : a ≠ 0) : linForm a ≠ 0 := by
  classical
  intro h
  obtain ⟨v, hv⟩ : ∃ v, a v ≠ 0 := by
    by_contra hc
    push Not at hc
    exact ha (funext hc)
  have := congrArg (fun p => MvPolynomial.eval (Pi.single v 1) p) h
  simp only [eval_linForm, map_zero] at this
  rw [Finset.sum_eq_single v (fun w _ hw => by simp [Pi.single_eq_of_ne hw])
    (fun h => absurd (Finset.mem_univ v) h)] at this
  simp only [Pi.single_eq_same, mul_one] at this
  exact hv this

omit [Fintype ι] in
lemma eval_aeval_line (u : ι → ℂ) (p : MvPolynomial ι ℂ) (ζ : ℂ) :
    (MvPolynomial.aeval (fun v => C (u v) * X) p).eval ζ =
      MvPolynomial.eval (fun v => u v * ζ) p := by
  rw [← Polynomial.coe_aeval_eq_eval, MvPolynomial.comp_aeval_apply,
    MvPolynomial.aeval_eq_eval₂Hom]
  simp only [Algebra.algebraMap_self, map_mul, aeval_C, aeval_X, RingHom.id_apply]
  rfl

/-- **Exponential polynomials in several variables.**  If
`∑_{w ∈ T} P_w (z) e ^ {w · z} = 0` for all `z ∈ ℂⁿ`, then every `P_w` is zero. -/
theorem eq_zero_of_sum_eval_mul_cexp_pi (T : Finset (ι → ℂ)) (P : (ι → ℂ) → MvPolynomial ι ℂ)
    (hP : ∀ z : ι → ℂ,
      ∑ w ∈ T, MvPolynomial.eval z (P w) * Complex.exp (∑ v, w v * z v) = 0) :
    ∀ w ∈ T, P w = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨w₀, hw₀, hPw₀⟩ := hcon
  -- a line on which the frequencies stay distinct and the polynomials stay nonzero
  set G : MvPolynomial ι ℂ := (∏ p ∈ T.offDiag, linForm (p.1 - p.2)) *
    ∏ w ∈ T.filter (fun w => P w ≠ 0), P w with hGdef
  have hG : G ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun p hp => linForm_ne_zero ?_)
      (Finset.prod_ne_zero_iff.2 fun w hw => (Finset.mem_filter.1 hw).2)
    obtain ⟨-, -, hne⟩ := Finset.mem_offDiag.1 hp
    exact sub_ne_zero.2 hne
  obtain ⟨u, hu⟩ : ∃ u : ι → ℂ, MvPolynomial.eval u G ≠ 0 := by
    by_contra h
    push Not at h
    exact hG (MvPolynomial.funext fun u => by simp [h u])
  rw [hGdef, map_mul, map_prod, map_prod] at hu
  have hu1 := left_ne_zero_of_mul hu
  have hu2 := right_ne_zero_of_mul hu
  set c : (ι → ℂ) → ℂ := fun w => ∑ v, w v * u v with hc
  have hcinj : Set.InjOn c T := by
    intro a ha b hb hab
    by_contra hne
    have := (Finset.prod_ne_zero_iff.1 hu1) (a, b) (Finset.mem_offDiag.2 ⟨ha, hb, hne⟩)
    rw [eval_linForm] at this
    apply this
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    exact sub_eq_zero.2 hab
  set Q : (ι → ℂ) → ℂ[X] := fun w => MvPolynomial.aeval (fun v => C (u v) * X) (P w) with hQ
  have hid : ∀ ζ : ℂ, ∑ w ∈ T, (Q w).eval ζ * Complex.exp (c w * ζ) = 0 := by
    intro ζ
    rw [← hP fun v => u v * ζ]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hQ, eval_aeval_line]
    congr 2
    rw [hc, Finset.sum_mul]
    exact Finset.sum_congr rfl fun v _ => by ring
  have hQ0 := eq_zero_of_sum_eval_mul_cexp' T c hcinj Q hid w₀ hw₀
  have hne := (Finset.prod_ne_zero_iff.1 hu2) w₀ (Finset.mem_filter.2 ⟨hw₀, hPw₀⟩)
  apply hne
  have h1 : (Q w₀).eval 1 = MvPolynomial.eval (fun v => u v * 1) (P w₀) :=
    eval_aeval_line u (P w₀) 1
  rw [hQ0, eval_zero] at h1
  simpa using h1.symm

/-- Several variables, with frequencies `c a` injective on an arbitrary finite index set. -/
theorem eq_zero_of_sum_eval_mul_cexp_pi' {α : Type*} (T : Finset α) (c : α → ι → ℂ)
    (hc : Set.InjOn c T) (P : α → MvPolynomial ι ℂ)
    (hP : ∀ z : ι → ℂ,
      ∑ a ∈ T, MvPolynomial.eval z (P a) * Complex.exp (∑ v, c a v * z v) = 0) :
    ∀ a ∈ T, P a = 0 := by
  classical
  set P' : (ι → ℂ) → MvPolynomial ι ℂ :=
    fun w => ∑ a ∈ T.filter (fun a => c a = w), P a with hP'def
  have hP' : ∀ a ∈ T, P' (c a) = P a := fun a ha => by
    simp only [hP'def]
    rw [Finset.sum_eq_single_of_mem a (by simp [ha])]
    intro a' ha' hne
    exact absurd (hc (Finset.mem_filter.1 ha').1 ha (Finset.mem_filter.1 ha').2) hne
  have hid : ∀ z : ι → ℂ, ∑ w ∈ T.image c,
      MvPolynomial.eval z (P' w) * Complex.exp (∑ v, w v * z v) = 0 := by
    intro z
    rw [Finset.sum_image fun a ha a' ha' h => hc ha ha' h, ← hP z]
    exact Finset.sum_congr rfl fun a ha => by rw [hP' a ha]
  intro a ha
  rw [← hP' a ha]
  exact eq_zero_of_sum_eval_mul_cexp_pi _ P' hid _ (Finset.mem_image_of_mem c ha)

end ExpPoly
