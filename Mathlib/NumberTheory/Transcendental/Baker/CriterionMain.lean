/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.Transcendental.Baker.Criterion

/-!
# The criterion of Schneider–Lang: parameters and conclusion

The choice of parameters for the transcendence argument of
`Mathlib/NumberTheory/Transcendental/Baker/Criterion.lean` (step 6 of §4.6 of Waldschmidt,
*Diophantine Approximation on Linear Algebraic Groups*), and the resulting proof of
Corollary 4.2.

## Main statements

* `Transcendental.SchneiderLangProof.exists_parameters`: admissible parameters exist.
* `Transcendental.SchneiderLangProof.main`: Corollary 4.2.
-/

@[expose] public section

open Finset MultiIndex NumberField

namespace Transcendental.SchneiderLangProof

variable {n d₀ d₁ : ℕ}

/-- The exponent of the Liouville factor. -/
noncomputable def phiE (d₀ d₁ n T S₁ δ D : ℕ) (N Hg : ℝ) (M : ℕ) : ℝ :=
  M * Real.log M + D * (Real.log (((T + 1) ^ d₀ * (T + 1) ^ d₁ : ℕ) : ℝ) +
    ((d₀ * T + M + d₁ * n * T * S₁ : ℕ) : ℝ) * Real.log δ + N +
    ((d₀ * T : ℕ) : ℝ) * Real.log ((δ : ℝ) ^ 2 * M + n * S₁ * Hg + 1) +
    M * Real.log (d₁ * T * Hg + 1) + ((d₁ * n * T * S₁ : ℕ) : ℝ) * Real.log Hg)

lemma natPow_eq_exp (M : ℕ) : (M : ℝ) ^ M = Real.exp (M * Real.log M) := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  · rw [← Real.log_pow, Real.exp_log (by positivity)]

lemma liouvilleFactor_le_exp {d₀ d₁ n T S₁ δ D : ℕ} (hD : 1 ≤ D) (hδ : 1 ≤ δ) {N Hg : ℝ}
    (hN : 0 ≤ N) (hHg : 1 ≤ Hg) (M : ℕ) :
    liouvilleFactor d₀ d₁ n T S₁ δ D N Hg M ≤ Real.exp (phiE d₀ d₁ n T S₁ δ D N Hg M) := by
  unfold liouvilleFactor phiE
  set c : ℝ := (((T + 1) ^ d₀ * (T + 1) ^ d₁ : ℕ) : ℝ) with hc
  set A : ℕ := d₀ * T + M + d₁ * n * T * S₁ with hA
  set Q : ℝ := (δ : ℝ) ^ 2 * M + n * S₁ * Hg + 1 with hQ
  set W : ℝ := d₁ * T * Hg + 1 with hW
  set Y : ℝ := (δ : ℝ) ^ A * Real.exp N * Q ^ (d₀ * T) * W ^ M * Hg ^ (d₁ * n * T * S₁)
    with hY
  have hδ1 : (1 : ℝ) ≤ δ := by exact_mod_cast hδ
  have hc1 : 1 ≤ c := by
    rw [hc]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
  have hQ1 : 1 ≤ Q := by
    have : (0 : ℝ) ≤ (δ : ℝ) ^ 2 * M + n * S₁ * Hg := by positivity
    linarith
  have hW1 : 1 ≤ W := by
    have : (0 : ℝ) ≤ d₁ * T * Hg := by positivity
    linarith
  have hδA : 1 ≤ (δ : ℝ) ^ A := one_le_pow₀ hδ1
  have hY1 : (δ : ℝ) ^ A ≤ Y := by
    rw [hY]
    have h1 : 1 ≤ Real.exp N := Real.one_le_exp hN
    have h2 : 1 ≤ Q ^ (d₀ * T) := one_le_pow₀ hQ1
    have h3 : 1 ≤ W ^ M := one_le_pow₀ hW1
    have h4 : 1 ≤ Hg ^ (d₁ * n * T * S₁) := one_le_pow₀ hHg
    calc (δ : ℝ) ^ A = (δ : ℝ) ^ A * 1 * 1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  have hX : (δ : ℝ) ^ A ≤ c * Y := hY1.trans (le_mul_of_one_le_left (by linarith) hc1)
  have hX0 : 0 < c * Y := lt_of_lt_of_le (by positivity) hX
  have hlogX : Real.log (c * Y) = Real.log c + (A : ℝ) * Real.log δ + N +
      ((d₀ * T : ℕ) : ℝ) * Real.log Q + M * Real.log W +
        ((d₁ * n * T * S₁ : ℕ) : ℝ) * Real.log Hg := by
    have hδ0 : (δ : ℝ) ≠ 0 := by positivity
    rw [hY, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity), Real.log_pow, Real.log_exp, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  calc (M : ℝ) ^ M * (δ : ℝ) ^ A * (c * Y) ^ (D - 1)
      ≤ (M : ℝ) ^ M * (c * Y) * (c * Y) ^ (D - 1) := by gcongr
    _ = (M : ℝ) ^ M * (c * Y) ^ D := by
        rw [mul_assoc, ← pow_succ']
        congr 2
        omega
    _ = Real.exp (M * Real.log M) * Real.exp (D * Real.log (c * Y)) := by
        have h2 : (c * Y) ^ D = Real.exp (D * Real.log (c * Y)) := by
          rw [← Real.log_pow, Real.exp_log (pow_pos hX0 D)]
        rw [natPow_eq_exp, h2]
    _ = _ := by
        rw [← Real.exp_add, hlogX]

lemma growth_eq {d₀ d₁ T : ℕ} {N Ax ρ : ℝ} (hρ : 0 ≤ ρ) :
    growth d₀ d₁ T N Ax ρ = Real.exp (Real.log (((T + 1) ^ d₀ * (T + 1) ^ d₁ : ℕ) : ℝ) + N +
      ((d₀ * T : ℕ) : ℝ) * Real.log (1 + ρ) + T * Ax * ρ) := by
  unfold growth
  have hc : (0 : ℝ) < (((T + 1) ^ d₀ * (T + 1) ^ d₁ : ℕ) : ℝ) := by positivity
  rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hc, ← Real.log_pow,
    Real.exp_log (by positivity)]
  push_cast
  ring

/-- **The choice of parameters** (step 6 of §4.6 of [waldschmidt2000]).  For fixed data there
are parameters satisfying all the inequalities used in `core`. -/
theorem exists_parameters (hn1 : 1 ≤ n) (hd : n < d₀ + d₁) {D δ : ℕ} (hD : 1 ≤ D)
    (hδ : 1 ≤ δ) {Hg Ax Ay B : ℝ} (hHg : 1 ≤ Hg) (hAx : 0 ≤ Ax) (hAy : 0 ≤ Ay) (hB : 0 ≤ B) :
    ∃ (T S₁ S₀ : ℕ) (U N r : ℝ) (R : NNReal) (Ep : ℕ → ℝ),
      1 ≤ S₁ ∧ 0 < N ∧ 0 < r ∧ S₁ * Ay + 2 ≤ r ∧ 12 * (n : ℝ) ^ 2 ≤ N + U + U ∧
      Real.exp 1 ≤ R / r ∧ R / r ≤ Real.exp ((N + U + U) / 6) ∧
      (2 * (N + U + U)) ^ (n + 1) ≤
        ((T + 1) ^ d₀ * (T + 1) ^ d₁ : ℕ) * N * Real.log (R / r) ^ n ∧
      ((T + 1) ^ d₀ * (T + 1) ^ d₁ : ℕ) * ((1 + (R : ℝ)) ^ (d₀ * T) *
        Real.exp (T * Ax * R)) ≤ Real.exp U ∧
      (∀ M : ℕ, M ≤ n * S₀ → liouvilleFactor d₀ d₁ n T S₁ δ D N Hg M * Real.exp (-U) < 1) ∧
      (∀ M, 1 ≤ Ep M) ∧
      (∀ M : ℕ, S₀ ≤ M → liouvilleFactor d₀ d₁ n T S₁ δ D N Hg M *
        (n * (1 / Ep M) ^ (M / n * S₁) * growth d₀ d₁ T N Ax
          (Ay * (5 * 3 ^ n * Ep M * (S₁ + 2 * B)))) < 1) := by
  sorry

/-- **Corollary 4.2 of [waldschmidt2000]**, proved. -/
theorem main (hd₀ : d₀ ≤ n) (hn : n < d₀ + d₁)
    (x : Fin d₁ → Fin n → ℂ) (hx : ∀ i v, IsAlgebraic ℚ (x i v))
    (hxli : LinearIndependent ℚ x)
    (y : Fin n → Fin n → ℂ) (hyli : LinearIndependent ℂ y) :
    (∃ (h : Fin d₀) (j : Fin n), Transcendental ℚ (y j (Fin.castLE hd₀ h))) ∨
      ∃ (i : Fin d₁) (j : Fin n), Transcendental ℚ (Complex.exp (∑ v, x i v * y j v)) := by
  classical
  by_contra hcon
  simp only [not_or, not_exists, Transcendental, not_not] at hcon
  obtain ⟨hyalg, hexpalg⟩ := hcon
  -- `n ≥ 1`
  have hn1 : 1 ≤ n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    subst hn0
    exact hxli.ne_zero ⟨0, by omega⟩ (funext fun v => v.elim0)
  -- the change of variables `z ↦ ∑ⱼ zⱼ yⱼ`
  set Lm : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) := Fintype.linearCombination ℂ y with hLm
  have hinj : Function.Injective Lm := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    funext j
    exact Fintype.linearIndependent_iff.1 hyli z
      (by simpa [hLm, Fintype.linearCombination_apply] using hz) j
  set Yl := (LinearEquiv.ofInjectiveEndo Lm hinj).toContinuousLinearEquiv with hYldef
  have hYl : ∀ z, Yl z = fun v => ∑ j, z j * y j v := fun z => by
    funext v
    simp [hYldef, hLm, Fintype.linearCombination_apply, Finset.sum_apply]
  -- the number field generated by the data
  set S : Set ℂ := Set.range (fun p : Fin d₁ × Fin n => x p.1 p.2) ∪
    Set.range (fun p : Fin n × Fin d₀ => y p.1 (Fin.castLE hd₀ p.2)) ∪
    Set.range (fun p : Fin d₁ × Fin n => Complex.exp (∑ v, x p.1 v * y p.2 v)) with hS
  have hSfin : S.Finite :=
    ((Set.finite_range _).union (Set.finite_range _)).union (Set.finite_range _)
  have : Finite S := hSfin.to_subtype
  have hSalg : ∀ z ∈ S, IsAlgebraic ℚ z := by
    intro z hz
    rcases hz with (⟨p, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩
    · exact hx _ _
    · exact hyalg _ _
    · exact hexpalg _ _
  set K := IntermediateField.adjoin ℚ S with hK
  have : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin fun z hz => (hSalg z hz).isIntegral
  have : NumberField K := ⟨⟩
  have hmem : ∀ z ∈ S, z ∈ K := fun z hz => IntermediateField.subset_adjoin ℚ S hz
  set X : Fin d₁ → Fin n → K := fun i v => ⟨x i v, hmem _ (by simp [hS])⟩ with hXdef
  set Yg : Fin n → Fin d₀ → K := fun j h => ⟨y j (Fin.castLE hd₀ h), hmem _ (by
    refine Or.inl (Or.inr ⟨(j, h), rfl⟩))⟩ with hYgdef
  set Eg : Fin d₁ → Fin n → K := fun i j => ⟨Complex.exp (∑ v, x i v * y j v), hmem _ (by
    exact Or.inr ⟨(i, j), rfl⟩)⟩ with hEgdef
  set ι₀ : K →+* ℂ := (IntermediateField.val K).toRingHom with hι₀
  have hX : ∀ i v, ι₀ (X i v) = x i v := fun i v => rfl
  have hY : ∀ j (v : Fin n) (h : (v : ℕ) < d₀), ι₀ (Yg j ⟨v, h⟩) = y j v := fun j v h => rfl
  have hE : ∀ i j, ι₀ (Eg i j) = Complex.exp (∑ v, x i v * y j v) := fun i j => rfl
  -- a common denominator and a bound for the houses
  set gens : Finset K := (Finset.univ.image fun p : Fin d₁ × Fin n => X p.1 p.2) ∪
    (Finset.univ.image fun p : Fin n × Fin d₀ => Yg p.1 p.2) ∪
    (Finset.univ.image fun p : Fin d₁ × Fin n => Eg p.1 p.2) with hgens
  obtain ⟨c, hc0, hc⟩ := exists_integral_multiples ℤ ℚ (L := K) gens
  set δ : ℕ := c.natAbs with hδdef
  have hδ : 1 ≤ δ := Nat.one_le_iff_ne_zero.2 (Int.natAbs_ne_zero.2 hc0)
  have hint : ∀ g ∈ gens, IsIntegral ℤ ((δ : K) ^ 1 * g) := by
    intro g hg
    have h1 := hc g hg
    rw [pow_one]
    rcases Int.natAbs_eq c with h | h
    · have : (δ : K) * g = c • g := by
        rw [zsmul_eq_mul, hδdef,
          show ((c.natAbs : ℕ) : K) = (((c.natAbs : ℕ) : ℤ) : K) from (Int.cast_natCast _).symm,
          ← h]
      rw [this]
      exact h1
    · have : (δ : K) * g = -(c • g) := by
        rw [zsmul_eq_mul, hδdef, ← neg_mul,
          show ((c.natAbs : ℕ) : K) = (((c.natAbs : ℕ) : ℤ) : K) from (Int.cast_natCast _).symm,
          show ((c.natAbs : ℕ) : ℤ) = -c by omega, Int.cast_neg]
      rw [this]
      exact h1.neg
  set Hg : ℝ := 1 + ∑ g ∈ gens, house ((δ : K) ^ 1 * g) with hHgdef
  have hHg : 1 ≤ Hg := by
    have : 0 ≤ ∑ g ∈ gens, house ((δ : K) ^ 1 * g) := Finset.sum_nonneg fun g _ => house_nonneg _
    linarith
  have hsize : ∀ g ∈ gens, AlgSize δ g 1 Hg := fun g hg => ⟨hint g hg, by
    rw [hHgdef]
    have := Finset.single_le_sum (fun g _ => house_nonneg ((δ : K) ^ 1 * g)) hg
    linarith⟩
  have hXs : ∀ i v, AlgSize δ (X i v) 1 Hg := fun i v =>
    hsize _ (by simp [hgens])
  have hYs : ∀ j h, AlgSize δ (Yg j h) 1 Hg := fun j h =>
    hsize _ (by simp [hgens])
  have hEs : ∀ i j, AlgSize δ (Eg i j) 1 Hg := fun i j =>
    hsize _ (by simp [hgens])
  have hD : 1 ≤ Module.finrank ℚ K := Module.finrank_pos
  -- the parameters, and the contradiction
  obtain ⟨T, S₁, S₀, U, N, r, R, Ep, hS₁, hN, hr0, hr, hW, hRr, hRr', hL, hMU, hvan, hEp,
    hbig⟩ := exists_parameters hn1 hn hD hδ hHg (Ax := ∑ i, ∑ v, ‖x i v‖)
      (Ay := ∑ j, ∑ v, ‖y j v‖)
      (B := ‖(Yl.symm : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))‖) (by positivity) (by positivity)
      (norm_nonneg _)
  exact core hn1 hd₀ hxli Yl hYl ι₀ hX hY hE hδ hHg hXs hYs hEs T S₁ S₀ hS₁ hN hr0 hr hW hRr
    hRr' hL hMU hvan Ep hEp hbig

end Transcendental.SchneiderLangProof
