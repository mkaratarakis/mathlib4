/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.GaussSum
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# The Pólya–Vinogradov inequality

For a non-principal Dirichlet character `χ` modulo a prime `p`, the sum of `χ` over any `N`
consecutive residues is `O(√p log p)`; we prove the explicit form

`‖∑_{n < N} χ (c + n)‖ ≤ √p (1 + log p)`.

The proof is the classical one, by completing the character sum:

* the Gauss sum `τ = ∑_x χ x ψ x` attached to a primitive additive character has absolute value
  `√(#R)` (`norm_gaussSum`), because `τ * conj τ = τ * gaussSum χ⁻¹ ψ⁻¹ = #R`;
* since `χ` is primitive (the modulus is prime), its discrete Fourier transform is
  `k ↦ χ⁻¹ (-k) τ`, so Fourier inversion expresses `χ` as a combination of the additive
  characters with coefficients of absolute value `√p / p`;
* the additive character sums are geometric series, bounded by `1 / sin (π k / p)`
  (`ZMod.norm_sum_stdAddChar_le`), using `‖e(k/p) - 1‖ = 2 |sin (π k / p)|`;
* those bounds sum to at most `p (1 + log p)` (`sum_one_div_sin_le`), by the rescaled Jordan
  inequality `Real.one_div_sin_pi_mul_div_le` and the harmonic bound `harmonic_le_one_add_log`.

## Main results

* `norm_gaussSum`: the absolute value of a Gauss sum over a finite field is `√(#R)`.
* `ZMod.norm_sum_stdAddChar_le`: the bound for an incomplete exponential sum.
* `sum_one_div_sin_le`: the completed sine sum.
* `DirichletCharacter.norm_sum_le_sqrt_mul_one_add_log`: the Pólya–Vinogradov inequality.

## References

The inequality is due to [Pólya, *Über die Verteilung der quadratischen Reste und
Nichtreste*][polya1918] and [Vinogradov, *Sur la distribution des résidus et des non-résidus des
puissances*][vinogradov1918].
-/

public section

open Finset ZMod

open scoped Real

/-! ### The absolute value of a Gauss sum -/

/-- **The absolute value of a Gauss sum.**  For a non-principal multiplicative character and a
primitive additive character on a finite field, both with values in `ℂ`, the Gauss sum has
absolute value `√(#R)`:  the conjugate of `gaussSum χ ψ` is `gaussSum χ⁻¹ ψ⁻¹`, and the product
of the two is `#R`. -/
theorem norm_gaussSum {R : Type*} [Field R] [Fintype R] {χ : MulChar R ℂ} (hχ : χ ≠ 1)
    {ψ : AddChar R ℂ} (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card R) := by
  have h1 : gaussSum χ ψ * star (gaussSum χ ψ) = (Fintype.card R : ℂ) := by
    rw [star_gaussSum_eq]
    exact gaussSum_mul_gaussSum_eq_card hχ hψ
  have h2 : ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card R : ℝ) := by
    have h3 := congrArg norm h1
    rw [norm_mul, norm_star] at h3
    rw [pow_two]
    simpa using h3
  rw [← h2, Real.sqrt_sq (norm_nonneg _)]

/-! ### Geometric sums -/

/-- A geometric sum of ratio of modulus one is bounded by `2 / ‖z - 1‖`, uniformly in the number
of terms. -/
theorem norm_geom_sum_le {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, z ^ n‖ ≤ 2 / ‖z - 1‖ := by
  have h2 : 0 < ‖z - 1‖ := by rw [norm_pos_iff, sub_ne_zero]; exact hz1
  rw [geom_sum_eq hz1, norm_div]
  have h1 : ‖z ^ N - 1‖ ≤ 2 := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_pow, hz, one_pow, norm_one]
    norm_num
  gcongr

namespace ZMod

/-! ### The standard additive character -/

/-- The standard additive character on `ZMod p`, written out as a complex exponential. -/
theorem stdAddChar_eq_exp {p : ℕ} [NeZero p] (x : ZMod p) :
    stdAddChar x = Complex.exp (((2 * π * x.val / p : ℝ) : ℂ) * Complex.I) := by
  have hval : ((x.val : ℤ) : ZMod p) = x := by
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]
  calc stdAddChar x = stdAddChar (((x.val : ℤ)) : ZMod p) := by rw [hval]
    _ = Complex.exp (2 * π * Complex.I * (x.val : ℤ) / p) := ZMod.stdAddChar_coe _
    _ = Complex.exp (((2 * π * x.val / p : ℝ) : ℂ) * Complex.I) := by
        congr 1
        push_cast
        ring

/-- The values of the standard additive character lie on the unit circle. -/
@[simp]
theorem norm_stdAddChar {p : ℕ} [NeZero p] (x : ZMod p) : ‖stdAddChar x‖ = 1 := by
  rw [stdAddChar_eq_exp, Complex.norm_exp_ofReal_mul_I]

/-- The standard additive character is nontrivial away from `0`. -/
theorem stdAddChar_ne_one {p : ℕ} [NeZero p] {k : ZMod p} (hk : k ≠ 0) :
    stdAddChar k ≠ 1 := by
  intro h
  refine hk (ZMod.injective_stdAddChar ?_)
  rw [h, (stdAddChar (N := p)).map_zero_eq_one]

/-- For `k ≠ 0` the sine `sin (π k / p)` is positive. -/
theorem sin_pi_mul_val_div_pos {p : ℕ} [NeZero p] {k : ZMod p} (hk : k ≠ 0) :
    0 < Real.sin (π * (k.val : ℝ) / p) := by
  have hp : (0 : ℝ) < p := by
    have := NeZero.pos p
    exact_mod_cast this
  have hkv : 0 < k.val := Nat.pos_of_ne_zero fun h => hk ((ZMod.val_eq_zero k).1 h)
  have hkvp : k.val < p := ZMod.val_lt k
  refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
  · refine div_pos (mul_pos Real.pi_pos ?_) hp
    exact_mod_cast hkv
  · rw [div_lt_iff₀ hp]
    have hlt : (k.val : ℝ) < p := by exact_mod_cast hkvp
    nlinarith [Real.pi_pos]

/-- **An incomplete exponential sum.**  For `k ≠ 0` in `ZMod p`, the sum of `e(k x / p)` over `N`
consecutive `x` is at most `1 / sin (π k / p)` in absolute value:  it is a geometric series of
ratio `e(k / p)`, and `‖e(k / p) - 1‖ = 2 |sin (π k / p)|`. -/
theorem norm_sum_stdAddChar_le {p : ℕ} [NeZero p] {k : ZMod p} (hk : k ≠ 0) (c : ZMod p)
    (N : ℕ) :
    ‖∑ n ∈ Finset.range N, stdAddChar (k * (c + ((n : ℕ) : ZMod p)))‖
      ≤ 1 / Real.sin (π * (k.val : ℝ) / p) := by
  have hsin := sin_pi_mul_val_div_pos hk
  have hsplit : ∑ n ∈ Finset.range N, stdAddChar (k * (c + ((n : ℕ) : ZMod p)))
      = stdAddChar (k * c) * ∑ n ∈ Finset.range N, (stdAddChar k) ^ n := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_add, (stdAddChar (N := p)).map_add_eq_mul]
    congr 1
    rw [mul_comm k, ← nsmul_eq_mul, (stdAddChar (N := p)).map_nsmul_eq_pow]
  have harg : (2 * π * (k.val : ℝ) / p) / 2 = π * (k.val : ℝ) / p := by ring
  have he : ‖stdAddChar k - 1‖ = 2 * Real.sin (π * (k.val : ℝ) / p) := by
    rw [stdAddChar_eq_exp, Complex.norm_exp_ofReal_mul_I_sub_one, harg, abs_of_pos hsin]
  have h2 : (2 : ℝ) / (2 * Real.sin (π * (k.val : ℝ) / p))
      = 1 / Real.sin (π * (k.val : ℝ) / p) := by
    have hne : Real.sin (π * (k.val : ℝ) / p) ≠ 0 := ne_of_gt hsin
    field_simp
  rw [hsplit, norm_mul, norm_stdAddChar, one_mul, ← h2, ← he]
  exact norm_geom_sum_le (norm_stdAddChar k) (stdAddChar_ne_one hk) N

end ZMod

/-! ### The completed sine sum -/

/-- **The completed sine sum.**  `∑_{a=1}^{p-1} 1 / sin (π a / p) ≤ p (1 + log p)`:  each term is
at most `(p / 2) (1 / a + 1 / (p - a))` by the rescaled Jordan inequality, and the two halves of
the resulting sum are both the harmonic number `H_{p-1}`. -/
theorem sum_one_div_sin_le {p : ℕ} (hp : 1 < p) :
    ∑ a ∈ Finset.Icc 1 (p - 1), 1 / Real.sin (π * (a : ℝ) / p) ≤ (p : ℝ) * (1 + Real.log p) := by
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hIco : Finset.Icc 1 (p - 1) = Finset.Ico 1 p := by
    rw [show p = (p - 1) + 1 by omega]
    exact (Finset.val_inj.mp rfl).symm
  have h1 : ∑ a ∈ Finset.Icc 1 (p - 1), 1 / Real.sin (π * (a : ℝ) / p)
      ≤ ∑ a ∈ Finset.Icc 1 (p - 1), ((p : ℝ) / 2) * (1 / a + 1 / ((p : ℝ) - a)) := by
    refine Finset.sum_le_sum fun a ha => ?_
    rw [Finset.mem_Icc] at ha
    refine Real.one_div_sin_pi_mul_div_le ?_ ?_
    · have : 1 ≤ a := ha.1
      exact_mod_cast this
    · have : a < p := by omega
      exact_mod_cast this
  refine le_trans h1 ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, hIco,
    Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  have e1 : ∑ i ∈ Finset.range (p - 1), 1 / ((1 + i : ℕ) : ℝ) = (harmonic (p - 1) : ℝ) := by
    rw [harmonic_eq_sum_range_one_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    rw [add_comm]
  have e2 : ∑ i ∈ Finset.range (p - 1), 1 / ((p : ℝ) - ((1 + i : ℕ) : ℝ))
      = (harmonic (p - 1) : ℝ) := by
    rw [harmonic_eq_sum_range_one_div_sub]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hc : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ p)]
      push_cast
      ring
    rw [hc]
    push_cast
    ring_nf
  rw [e1, e2]
  have hH := harmonic_le_one_add_log (p - 1)
  have hlog : Real.log ((p - 1 : ℕ) : ℝ) ≤ Real.log p := by
    have hpos : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
      have : 0 < p - 1 := by omega
      exact_mod_cast this
    have hle : ((p - 1 : ℕ) : ℝ) ≤ (p : ℝ) := by
      have : p - 1 ≤ p := by omega
      exact_mod_cast this
    exact Real.log_le_log hpos hle
  have hHle : (harmonic (p - 1) : ℝ) ≤ 1 + Real.log p := by linarith
  have hnn : (0 : ℝ) ≤ (harmonic (p - 1) : ℝ) := by
    rw [harmonic_eq_sum_range_one_div]
    exact Finset.sum_nonneg fun j _ => by positivity
  nlinarith [hHle, hnn, hpR]

/-! ### The Pólya–Vinogradov inequality -/

/-- **The Pólya–Vinogradov inequality** for a prime modulus:  for a non-principal Dirichlet
character `χ` modulo a prime `p`, the sum of `χ` over any `N` consecutive residues starting at `c`
is at most `√p (1 + log p)` in absolute value. -/
theorem DirichletCharacter.norm_sum_le_sqrt_mul_one_add_log {p : ℕ} (hp : p.Prime)
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) (c : ZMod p) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, χ (c + (n : ℕ))‖ ≤ Real.sqrt p * (1 + Real.log p) := by
  classical
  have hp1 : 1 < p := hp.one_lt
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (1 < p) := ⟨hp1⟩
  have : NeZero p := ⟨hp.pos.ne'⟩
  have hpR : (0 : ℝ) < p := by positivity
  set ψ : AddChar (ZMod p) ℂ := ZMod.stdAddChar with hψdef
  set τ : ℂ := gaussSum χ ψ with hτdef
  have hτ : ‖τ‖ = Real.sqrt p := by
    rw [hτdef, norm_gaussSum hχ (ZMod.isPrimitive_stdAddChar p), ZMod.card]
  -- `χ` is primitive, so its Fourier transform is `χ⁻¹(-k) τ`
  have hprim : χ.IsPrimitive := by
    rcases hp.eq_one_or_self_of_dvd _ (DirichletCharacter.conductor_dvd_level χ) with h | h
    · exact absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.2 h) hχ
    · exact h
  have hF : ∀ k : ZMod p, 𝓕 (χ : ZMod p → ℂ) k = χ⁻¹ (-k) * τ :=
    fun k => hprim.fourierTransform_eq_inv_mul_gaussSum k
  -- Fourier inversion
  have hinv : ∀ x : ZMod p, χ x = (p : ℂ)⁻¹ * ∑ k : ZMod p, ψ (k * x) * (χ⁻¹ (-k) * τ) := by
    intro x
    have h : (𝓕⁻ (𝓕 (χ : ZMod p → ℂ))) x = χ x :=
      congrFun (ZMod.dft.symm_apply_apply (χ : ZMod p → ℂ)) x
    rw [ZMod.invDFT_apply] at h
    rw [← h, smul_eq_mul]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [smul_eq_mul, hF k]
  -- the sum, expanded
  have hsum : ∑ n ∈ Finset.range N, χ (c + (n : ℕ))
      = (p : ℂ)⁻¹ * ∑ k : ZMod p,
          (χ⁻¹ (-k) * τ) * ∑ n ∈ Finset.range N, ψ (k * (c + (n : ℕ))) := by
    calc ∑ n ∈ Finset.range N, χ (c + (n : ℕ))
        = ∑ n ∈ Finset.range N, (p : ℂ)⁻¹ *
            ∑ k : ZMod p, ψ (k * (c + (n : ℕ))) * (χ⁻¹ (-k) * τ) :=
          Finset.sum_congr rfl fun n _ => hinv _
      _ = (p : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
            ∑ k : ZMod p, ψ (k * (c + (n : ℕ))) * (χ⁻¹ (-k) * τ) := by rw [Finset.mul_sum]
      _ = (p : ℂ)⁻¹ * ∑ k : ZMod p,
            ∑ n ∈ Finset.range N, ψ (k * (c + (n : ℕ))) * (χ⁻¹ (-k) * τ) := by
          rw [Finset.sum_comm]
      _ = (p : ℂ)⁻¹ * ∑ k : ZMod p,
            (χ⁻¹ (-k) * τ) * ∑ n ∈ Finset.range N, ψ (k * (c + (n : ℕ))) := by
          refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun n _ => by ring
  -- bound each term; the term `k = 0` vanishes because `χ⁻¹ 0 = 0`
  have hterm : ∀ k : ZMod p, ‖(χ⁻¹ (-k) * τ) * ∑ n ∈ Finset.range N, ψ (k * (c + (n : ℕ)))‖
      ≤ Real.sqrt p * (1 / Real.sin (π * (k.val : ℝ) / p)) := by
    intro k
    by_cases hk : k = 0
    · subst hk
      rw [neg_zero, MulChar.map_nonunit _ not_isUnit_zero, zero_mul, zero_mul, norm_zero]
      simp
    · rw [norm_mul, norm_mul, hτ]
      calc ‖χ⁻¹ (-k)‖ * Real.sqrt p * ‖∑ n ∈ Finset.range N, ψ (k * (c + (n : ℕ)))‖
          ≤ 1 * Real.sqrt p * (1 / Real.sin (π * (k.val : ℝ) / p)) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right
              (DirichletCharacter.norm_le_one _ _) (Real.sqrt_nonneg _))
              (ZMod.norm_sum_stdAddChar_le hk c N) (norm_nonneg _) (by positivity)
        _ = Real.sqrt p * (1 / Real.sin (π * (k.val : ℝ) / p)) := by rw [one_mul]
  -- sum the bounds over `k`, and reindex by `k.val`
  have hZ : ∑ k : ZMod p, (1 / Real.sin (π * (k.val : ℝ) / p))
      ≤ ∑ a ∈ Finset.Icc 1 (p - 1), 1 / Real.sin (π * (a : ℝ) / p) := by
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (0 : ZMod p))]
    have h0 : (1 / Real.sin (π * ((0 : ZMod p)).val / p) : ℝ) = 0 := by simp
    rw [h0, add_zero, ← Finset.sum_image
      (f := fun a : ℕ => 1 / Real.sin (π * (a : ℝ) / p)) (ZMod.val_injective p).injOn]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun a ha _ => ?_)
    · intro a ha
      rw [Finset.mem_image] at ha
      obtain ⟨k, hk, rfl⟩ := ha
      rw [Finset.mem_Icc]
      have hk0 : k ≠ 0 := Finset.ne_of_mem_erase hk
      exact ⟨Nat.pos_of_ne_zero (fun h => hk0 ((ZMod.val_eq_zero k).1 h)),
        by have := ZMod.val_lt k; omega⟩
    · rw [Finset.mem_Icc] at ha
      have hpos : 0 < Real.sin (π * (a : ℝ) / p) := by
        refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
        · refine div_pos (mul_pos Real.pi_pos ?_) hpR
          have : 1 ≤ a := ha.1
          exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
        · rw [div_lt_iff₀ hpR]
          have hlt : (a : ℝ) < p := by
            have : a < p := by omega
            exact_mod_cast this
          nlinarith [Real.pi_pos]
      positivity
  -- assemble
  rw [hsum, norm_mul, norm_inv, Complex.norm_natCast]
  have hb1 : ‖∑ k : ZMod p, (χ⁻¹ (-k) * τ) * ∑ n ∈ Finset.range N, ψ (k * (c + (n : ℕ)))‖
      ≤ Real.sqrt p * ((p : ℝ) * (1 + Real.log p)) := by
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum fun k _ => hterm k) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (le_trans hZ (sum_one_div_sin_le hp1)) (Real.sqrt_nonneg _)
  have hfinal : (p : ℝ)⁻¹ * (Real.sqrt p * ((p : ℝ) * (1 + Real.log p)))
      = Real.sqrt p * (1 + Real.log p) := by field_simp
  calc (p : ℝ)⁻¹ * ‖∑ k : ZMod p, (χ⁻¹ (-k) * τ) *
        ∑ n ∈ Finset.range N, ψ (k * (c + (n : ℕ)))‖
      ≤ (p : ℝ)⁻¹ * (Real.sqrt p * ((p : ℝ) * (1 + Real.log p))) :=
        mul_le_mul_of_nonneg_left hb1 (by positivity)
    _ = Real.sqrt p * (1 + Real.log p) := hfinal
