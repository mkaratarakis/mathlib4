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

* the Gauss sum `τ = ∑_x χ x e(x / p)` has absolute value `√p`
  (`norm_gaussSum_stdAddChar`), because `τ * conj τ = τ * gaussSum χ⁻¹ ψ⁻¹ = p`;
* since `χ` is primitive (the modulus is prime), its discrete Fourier transform is
  `k ↦ χ⁻¹ (-k) τ`, so Fourier inversion expresses `χ` as a combination of the additive
  characters with coefficients of absolute value `√p / p`;
* the additive character sums are geometric series, bounded by `2 / ‖e(k/p) - 1‖`, and
  `‖e(k/p) - 1‖ = 2 |sin (π k / p)|` (`norm_exp_mul_I_sub_one`);
* finally `1 / |sin (π a / p)| ≤ (p / 2)(1 / a + 1 / (p - a))` by concavity of the sine
  (`one_div_abs_sin_le`), and summing over `1 ≤ a ≤ p - 1` gives `p H_{p-1} ≤ p (1 + log p)`
  (`sum_one_div_abs_sin_le`).

## Main results

* `DirichletCharacter.norm_sum_le_sqrt_mul_one_add_log`: the Pólya–Vinogradov inequality.
* `norm_gaussSum_stdAddChar`: the absolute value of a Gauss sum.
* `sum_one_div_abs_sin_le`: the completed sine sum.
-/

public section

open Finset ZMod

open scoped Real

set_option linter.style.haveILetI false

theorem norm_gaussSum_stdAddChar {p : ℕ} [NeZero p] (hp : p.Prime) (χ : DirichletCharacter ℂ p)
    (hχ : χ ≠ 1) : ‖gaussSum χ (ZMod.stdAddChar (N := p))‖ = Real.sqrt p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ (ZMod.stdAddChar (N := p))⁻¹
      = Fintype.card (ZMod p) :=
    gaussSum_mul_gaussSum_eq_card hχ (ZMod.isPrimitive_stdAddChar p)
  rw [← star_gaussSum_eq] at h1
  have h2 : ‖gaussSum χ (ZMod.stdAddChar (N := p))‖ ^ 2 = (p : ℝ) := by
    have h3 := congrArg norm h1
    rw [norm_mul, norm_star, ZMod.card] at h3
    rw [pow_two]
    simpa using h3
  rw [← h2, Real.sqrt_sq (norm_nonneg _)]

theorem norm_geom_sum_le {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, z ^ n‖ ≤ 2 / ‖z - 1‖ := by
  have h2 : 0 < ‖z - 1‖ := by rw [norm_pos_iff, sub_ne_zero]; exact hz1
  rw [geom_sum_eq hz1, norm_div]
  have h1 : ‖z ^ N - 1‖ ≤ 2 := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_pow, hz, one_pow, norm_one]
    norm_num
  gcongr

theorem norm_exp_mul_I_sub_one (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ = 2 * |Real.sin (θ / 2)| := by
  have h1 : ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ^ 2 = 2 - 2 * Real.cos θ := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, sub_zero]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have h2 : 2 - 2 * Real.cos θ = (2 * |Real.sin (θ / 2)|) ^ 2 := by
    have hc := Real.cos_two_mul (θ / 2)
    have hhalf : 2 * (θ / 2) = θ := by ring
    rw [hhalf] at hc
    have hs := Real.sin_sq_add_cos_sq (θ / 2)
    rw [mul_pow, sq_abs]
    nlinarith
  calc ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖
      = Real.sqrt (‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt ((2 * |Real.sin (θ / 2)|) ^ 2) := by rw [h1, h2]
    _ = 2 * |Real.sin (θ / 2)| := Real.sqrt_sq (by positivity)

/-- The standard additive character, explicitly. -/
theorem stdAddChar_eq_exp {p : ℕ} [NeZero p] (x : ZMod p) :
    ZMod.stdAddChar x = Complex.exp (((2 * π * x.val / p : ℝ) : ℂ) * Complex.I) := by
  have hval : ((x.val : ℤ) : ZMod p) = x := by
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]
  calc ZMod.stdAddChar x = ZMod.stdAddChar (((x.val : ℤ)) : ZMod p) := by rw [hval]
    _ = Complex.exp (2 * π * Complex.I * (x.val : ℤ) / p) := ZMod.stdAddChar_coe _
    _ = Complex.exp (((2 * π * x.val / p : ℝ) : ℂ) * Complex.I) := by
        congr 1
        push_cast
        ring

theorem norm_stdAddChar {p : ℕ} [NeZero p] (x : ZMod p) : ‖ZMod.stdAddChar x‖ = 1 := by
  rw [stdAddChar_eq_exp, Complex.norm_exp_ofReal_mul_I]

theorem stdAddChar_ne_one {p : ℕ} [NeZero p] {k : ZMod p} (hk : k ≠ 0) :
    ZMod.stdAddChar k ≠ 1 := by
  intro h
  refine hk (ZMod.injective_stdAddChar ?_)
  rw [h, (ZMod.stdAddChar (N := p)).map_zero_eq_one]

/-! ### Harmonic sums -/

theorem sum_one_div_reflect (n : ℕ) :
    ∑ j ∈ Finset.range n, 1 / ((n : ℝ) - j) = ∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1) := by
  rw [← Finset.sum_range_reflect (fun i : ℕ => 1 / ((i : ℝ) + 1)) n]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have hcast : ((n - 1 - j : ℕ) : ℝ) + 1 = (n : ℝ) - j := by
    rw [Nat.cast_sub (by omega : j ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast
    ring
  simp only [hcast]

theorem sum_one_div_succ_le_one_add_log (n : ℕ) :
    ∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1) ≤ 1 + Real.log n := by
  have h : ∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1) = ((harmonic n : ℚ) : ℝ) := by
    rw [harmonic]
    push_cast
    exact Finset.sum_congr rfl fun j _ => by rw [one_div]
  rw [h]
  exact harmonic_le_one_add_log n

/-! ### The sum of `1 / sin (π a / p)` -/

theorem one_div_min_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    1 / min x y ≤ 1 / x + 1 / y := by
  rcases le_total x y with h | h
  · rw [min_eq_left h]
    have : 0 < 1 / y := by positivity
    linarith
  · rw [min_eq_right h]
    have : 0 < 1 / x := by positivity
    linarith

/-- For `0 < a < p` one has `1 / sin (π a / p) ≤ (p / 2) (1 / a + 1 / (p - a))`:  the sine is at
least `2 min (a, p - a) / p` by concavity of the sine on `[0, π]`. -/
theorem one_div_abs_sin_le {p a : ℕ} (ha : 0 < a) (hap : a < p) :
    1 / |Real.sin (π * a / p)| ≤ ((p : ℝ) / 2) * (1 / a + 1 / ((p : ℝ) - a)) := by
  have hpN : 0 < p := lt_trans ha hap
  have hp : (0 : ℝ) < p := by exact_mod_cast hpN
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hapR : (a : ℝ) < p := by exact_mod_cast hap
  set θ := π * a / p with hθ
  have hθ0 : 0 < θ := div_pos (mul_pos Real.pi_pos haR) hp
  have hθπ : θ < π := by
    rw [hθ, div_lt_iff₀ hp]
    nlinarith [Real.pi_pos]
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  rw [abs_of_pos hsin]
  have hminpos : 0 < min (a : ℝ) ((p : ℝ) - a) := lt_min haR (by linarith)
  have key : 2 * min (a : ℝ) ((p : ℝ) - a) / p ≤ Real.sin θ := by
    rcases le_or_gt (2 * (a : ℝ)) p with h | h
    · have hmin : min (a : ℝ) ((p : ℝ) - a) = a := min_eq_left (by linarith)
      rw [hmin]
      have hle : θ ≤ π / 2 := by
        rw [hθ, div_le_iff₀ hp]
        nlinarith [Real.pi_pos]
      have hms := Real.mul_le_sin hθ0.le hle
      have heq : 2 / π * θ = 2 * (a : ℝ) / p := by
        rw [hθ]
        field_simp
      rw [heq] at hms
      exact hms
    · have hmin : min (a : ℝ) ((p : ℝ) - a) = (p : ℝ) - a := min_eq_right (by linarith)
      rw [hmin]
      have hle : π - θ ≤ π / 2 := by
        have hhalf : π / 2 ≤ π * (a : ℝ) / p := by
          rw [le_div_iff₀ hp]
          nlinarith [Real.pi_pos]
        rw [hθ]
        linarith
      have h0 : 0 ≤ π - θ := by linarith
      have hms := Real.mul_le_sin h0 hle
      have heq : 2 / π * (π - θ) = 2 * ((p : ℝ) - a) / p := by
        rw [hθ]
        field_simp
      rw [heq, Real.sin_pi_sub] at hms
      exact hms
  have h1 : 1 / Real.sin θ ≤ (p : ℝ) / (2 * min (a : ℝ) ((p : ℝ) - a)) := by
    have h2 := one_div_le_one_div_of_le (by positivity) key
    rwa [one_div_div] at h2
  refine le_trans h1 ?_
  have h3 : (p : ℝ) / (2 * min (a : ℝ) ((p : ℝ) - a))
      = ((p : ℝ) / 2) * (1 / min (a : ℝ) ((p : ℝ) - a)) := by field_simp
  rw [h3]
  exact mul_le_mul_of_nonneg_left (one_div_min_le haR (by linarith)) (by positivity)

/-- **The completed sine sum.**  `∑_{a=1}^{p-1} 1 / sin (π a / p) ≤ p (1 + log p)`. -/
theorem sum_one_div_abs_sin_le {p : ℕ} (hp : 1 < p) :
    ∑ a ∈ Finset.Icc 1 (p - 1), 1 / |Real.sin (π * a / p)| ≤ (p : ℝ) * (1 + Real.log p) := by
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hIco : Finset.Icc 1 (p - 1) = Finset.Ico 1 p := by
    rw [show p = (p - 1) + 1 by omega]
    exact (Finset.val_inj.mp rfl).symm
  have h1 : ∑ a ∈ Finset.Icc 1 (p - 1), 1 / |Real.sin (π * a / p)|
      ≤ ∑ a ∈ Finset.Icc 1 (p - 1), ((p : ℝ) / 2) * (1 / a + 1 / ((p : ℝ) - a)) := by
    refine Finset.sum_le_sum fun a ha => ?_
    rw [Finset.mem_Icc] at ha
    exact one_div_abs_sin_le (by omega) (by omega)
  refine le_trans h1 ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, hIco,
    Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  have e1 : ∑ i ∈ Finset.range (p - 1), 1 / ((1 + i : ℕ) : ℝ)
      = ∑ j ∈ Finset.range (p - 1), 1 / ((j : ℝ) + 1) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    rw [add_comm]
  have e2 : ∑ i ∈ Finset.range (p - 1), 1 / ((p : ℝ) - ((1 + i : ℕ) : ℝ))
      = ∑ j ∈ Finset.range (p - 1), 1 / ((j : ℝ) + 1) := by
    rw [← sum_one_div_reflect (p - 1)]
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
  have hH := sum_one_div_succ_le_one_add_log (p - 1)
  have hlog : Real.log ((p - 1 : ℕ) : ℝ) ≤ Real.log p := by
    have hpos : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
      have : 0 < p - 1 := by omega
      exact_mod_cast this
    have hle : ((p - 1 : ℕ) : ℝ) ≤ (p : ℝ) := by
      have : p - 1 ≤ p := by omega
      exact_mod_cast this
    exact Real.log_le_log hpos hle
  have hHle : ∑ j ∈ Finset.range (p - 1), 1 / ((j : ℝ) + 1) ≤ 1 + Real.log p := by linarith
  have hnn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (p - 1), 1 / ((j : ℝ) + 1) :=
    Finset.sum_nonneg fun j _ => by positivity
  nlinarith [hHle, hnn, hpR]

/-! ### The Pólya–Vinogradov inequality -/

/-- **The Pólya–Vinogradov inequality** for a prime modulus:  for a non-principal Dirichlet
character `χ` modulo a prime `p`, the sum of `χ` over any `N` consecutive residues starting at `c`
is at most `√p (1 + log p)` in absolute value.

The proof is the classical one.  Fourier inversion on `ZMod p` writes `χ` as a combination of the
additive characters with coefficients `χ⁻¹(-k) τ`, where `τ` is the Gauss sum, of absolute
value `√p`; the additive character sums are geometric series, bounded by `1 / |sin (π k / p)|`;
and those bounds sum to at most `p (1 + log p)`. -/
theorem DirichletCharacter.norm_sum_le_sqrt_mul_one_add_log {p : ℕ} [NeZero p] (hp : p.Prime)
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) (c : ZMod p) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, χ (c + (n : ℕ))‖ ≤ Real.sqrt p * (1 + Real.log p) := by
  classical
  have hp1 : 1 < p := hp.one_lt
  haveI : Fact (1 < p) := ⟨hp1⟩
  have hpR : (0 : ℝ) < p := by positivity
  set ψ : AddChar (ZMod p) ℂ := ZMod.stdAddChar with hψdef
  set τ : ℂ := gaussSum χ ψ with hτdef
  have hτ : ‖τ‖ = Real.sqrt p := norm_gaussSum_stdAddChar hp χ hχ
  have hnormψ : ∀ x : ZMod p, ‖ψ x‖ = 1 := fun x => norm_stdAddChar x
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
  -- bound each term
  have hterm : ∀ k : ZMod p, ‖(χ⁻¹ (-k) * τ) * ∑ n ∈ Finset.range N, ψ (k * (c + (n : ℕ)))‖
      ≤ Real.sqrt p * (1 / |Real.sin (π * k.val / p)|) := by
    intro k
    by_cases hk : k = 0
    · subst hk
      rw [neg_zero, MulChar.map_nonunit _ not_isUnit_zero, zero_mul, zero_mul, norm_zero]
      positivity
    · have hkv : 0 < k.val := Nat.pos_of_ne_zero (fun h => hk ((ZMod.val_eq_zero k).1 h))
      have hkvp : k.val < p := ZMod.val_lt k
      have hz1 : ‖ψ k‖ = 1 := hnormψ k
      have hzne : ψ k ≠ 1 := stdAddChar_ne_one hk
      have hsplit : ∑ n ∈ Finset.range N, ψ (k * (c + (n : ℕ)))
          = ψ (k * c) * ∑ n ∈ Finset.range N, (ψ k) ^ n := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [mul_add, ψ.map_add_eq_mul]
        congr 1
        rw [mul_comm k, ← nsmul_eq_mul, ψ.map_nsmul_eq_pow]
      have hsinpos : 0 < |Real.sin (π * (k.val : ℝ) / p)| := by
        have h0 : 0 < π * (k.val : ℝ) / p := by
          refine div_pos (mul_pos Real.pi_pos ?_) hpR
          exact_mod_cast hkv
        have h1 : π * (k.val : ℝ) / p < π := by
          rw [div_lt_iff₀ hpR]
          have hlt : (k.val : ℝ) < p := by exact_mod_cast hkvp
          nlinarith [Real.pi_pos]
        exact abs_pos.2 (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h0 h1))
      have hne : |Real.sin (π * (k.val : ℝ) / p)| ≠ 0 := ne_of_gt hsinpos
      have hgeom : ‖∑ n ∈ Finset.range N, (ψ k) ^ n‖ ≤ 1 / |Real.sin (π * (k.val : ℝ) / p)| := by
        have harg : (2 * π * (k.val : ℝ) / p) / 2 = π * (k.val : ℝ) / p := by ring
        have he : ‖ψ k - 1‖ = 2 * |Real.sin (π * (k.val : ℝ) / p)| := by
          rw [stdAddChar_eq_exp, norm_exp_mul_I_sub_one, harg]
        have h2 : (2 : ℝ) / (2 * |Real.sin (π * (k.val : ℝ) / p)|)
            = 1 / |Real.sin (π * (k.val : ℝ) / p)| := by
          field_simp
        rw [← h2, ← he]
        exact norm_geom_sum_le hz1 hzne N
      have hsq : (0 : ℝ) ≤ Real.sqrt p := Real.sqrt_nonneg _
      calc ‖(χ⁻¹ (-k) * τ) * ∑ n ∈ Finset.range N, ψ (k * (c + (n : ℕ)))‖
          = ‖χ⁻¹ (-k)‖ * ‖τ‖ * (‖ψ (k * c)‖ * ‖∑ n ∈ Finset.range N, (ψ k) ^ n‖) := by
            rw [hsplit, norm_mul, norm_mul, norm_mul]
        _ ≤ 1 * Real.sqrt p * (1 * (1 / |Real.sin (π * (k.val : ℝ) / p)|)) := by
            rw [hτ, hnormψ]
            refine mul_le_mul (mul_le_mul_of_nonneg_right
              (DirichletCharacter.norm_le_one _ _) hsq) ?_ (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_left hgeom zero_le_one
        _ = Real.sqrt p * (1 / |Real.sin (π * (k.val : ℝ) / p)|) := by ring
  -- sum the bounds
  have hZ : ∑ k : ZMod p, (1 / |Real.sin (π * (k.val : ℝ) / p)|)
      ≤ ∑ a ∈ Finset.Icc 1 (p - 1), 1 / |Real.sin (π * a / p)| := by
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (0 : ZMod p))]
    have h0 : (1 / |Real.sin (π * ((0 : ZMod p)).val / p)| : ℝ) = 0 := by
      simp
    rw [h0, add_zero]
    rw [← Finset.sum_image (f := fun a : ℕ => 1 / |Real.sin (π * (a : ℝ) / p)|)
      (ZMod.val_injective p).injOn]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun a _ _ => by positivity)
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨k, hk, rfl⟩ := ha
    rw [Finset.mem_Icc]
    have hk0 : k ≠ 0 := Finset.ne_of_mem_erase hk
    exact ⟨Nat.pos_of_ne_zero (fun h => hk0 ((ZMod.val_eq_zero k).1 h)),
      by have := ZMod.val_lt k; omega⟩
  -- assemble
  rw [hsum, norm_mul, norm_inv, Complex.norm_natCast]
  have hb1 : ‖∑ k : ZMod p, (χ⁻¹ (-k) * τ) * ∑ n ∈ Finset.range N, ψ (k * (c + (n : ℕ)))‖
      ≤ Real.sqrt p * ((p : ℝ) * (1 + Real.log p)) := by
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum fun k _ => hterm k) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (le_trans hZ (sum_one_div_abs_sin_le hp1))
      (Real.sqrt_nonneg _)
  have hfinal : (p : ℝ)⁻¹ * (Real.sqrt p * ((p : ℝ) * (1 + Real.log p)))
      = Real.sqrt p * (1 + Real.log p) := by
    field_simp
  calc (p : ℝ)⁻¹ * ‖∑ k : ZMod p, (χ⁻¹ (-k) * τ) *
        ∑ n ∈ Finset.range N, ψ (k * (c + (n : ℕ)))‖
      ≤ (p : ℝ)⁻¹ * (Real.sqrt p * ((p : ℝ) * (1 + Real.log p))) :=
        mul_le_mul_of_nonneg_left hb1 (by positivity)
    _ = Real.sqrt p * (1 + Real.log p) := hfinal
