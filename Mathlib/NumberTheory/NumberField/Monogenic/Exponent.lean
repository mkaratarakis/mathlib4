/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
public import Mathlib.RingTheory.Adjoin.PowerBasis
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral

/-!
# Criteria for a prime not to divide the exponent of an algebraic integer

Let `K` be a number field and `θ : 𝓞 K` an algebraic integer generating `K` over `ℚ`.
The subring `ℤ[θ]` is the full ring of integers of `K` if and only if no rational prime
divides `RingOfIntegers.exponent θ`.  This file provides tools to check the latter
condition at a given prime `p`.

## Main results

* `RingOfIntegers.aeval_derivative_minpoly_mem_conductor`: the different of `θ`, that is
  `f'(θ)` where `f` is the minimal polynomial of `θ`, belongs to the conductor of `θ`.

* `RingOfIntegers.adjoin_eq_top_iff_forall_prime_not_dvd_exponent`: `ℤ[θ] = 𝓞 K` if and
  only if no prime divides `exponent θ`.

* `RingOfIntegers.not_dvd_exponent_iff_conductor_sup_span_eq_top`: `p` does not divide
  `exponent θ` if and only if the conductor of `θ` is comaximal with `p • 𝓞 K`.

* `RingOfIntegers.not_dvd_exponent_of_minpoly_isEisensteinAt`: if the minimal polynomial
  of `θ` is Eisenstein at `p`, then `p` does not divide `exponent θ`.
-/

@[expose] public section

noncomputable section

open Polynomial NumberField Ideal

namespace RingOfIntegers

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}

/-- The derivative of the minimal polynomial of `θ : 𝓞 K`, evaluated at `θ`, is nonzero. -/
theorem aeval_derivative_minpoly_ne_zero (θ : 𝓞 K) :
    aeval θ (derivative (minpoly ℤ θ)) ≠ 0 := by
  intro h
  have h₀ : aeval ((θ : K)) (derivative (minpoly ℚ ((θ : K)))) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable ℚ ((θ : K))).aeval_derivative_ne_zero
      (minpoly.aeval ℚ ((θ : K)))
  apply h₀
  rw [minpoly.isIntegrallyClosed_eq_field_fractions ℚ K θ.isIntegral, derivative_map,
    aeval_map_algebraMap, aeval_algebraMap_apply, h, map_zero]

variable (hθ : Algebra.adjoin ℚ {(θ : K)} = ⊤)

include hθ in
/-- If `θ` generates `K` over `ℚ` and `f` is its minimal polynomial over `ℤ`, then `f'(θ)`
belongs to the conductor of `θ`. -/
theorem aeval_derivative_minpoly_mem_conductor :
    aeval θ (derivative (minpoly ℤ θ)) ∈ conductor ℤ θ := by
  have h : Ideal.span {aeval θ (derivative (minpoly ℤ θ))} ≤ conductor ℤ θ := by
    rw [← conductor_mul_differentIdeal ℤ ℚ K θ hθ]
    exact Ideal.mul_le_right
  exact h (Ideal.mem_span_singleton_self _)

include hθ in
theorem conductor_ne_bot : conductor ℤ θ ≠ ⊥ := fun h ↦
  aeval_derivative_minpoly_ne_zero θ <| by
    simpa [h] using aeval_derivative_minpoly_mem_conductor hθ

include hθ in
theorem under_conductor_ne_bot : (conductor ℤ θ).under ℤ ≠ ⊥ := by
  intro h
  have h₁ : Ideal.absNorm (conductor ℤ θ) ≠ 0 := by
    rw [Ideal.absNorm_ne_zero_iff]
    exact Ideal.finiteQuotientOfFreeOfNeBot _ (conductor_ne_bot hθ)
  have h₂ : ((Ideal.absNorm (conductor ℤ θ) : ℤ)) ∈ (conductor ℤ θ).under ℤ := by
    rw [Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact Ideal.absNorm_mem (conductor ℤ θ)
  rw [h, Ideal.mem_bot] at h₂
  exact h₁ (by exact_mod_cast h₂)

include hθ in
theorem exponent_ne_zero : exponent θ ≠ 0 := fun h ↦ by
  have := Int.ideal_span_absNorm_eq_self ((conductor ℤ θ).under ℤ)
  rw [show Ideal.absNorm ((conductor ℤ θ).under ℤ) = exponent θ from rfl, h] at this
  exact under_conductor_ne_bot hθ (by simpa using this.symm)

omit [NumberField K] in
/-- `ℤ[θ] = 𝓞 K` if and only if no rational prime divides the exponent of `θ`. -/
theorem adjoin_eq_top_iff_forall_prime_not_dvd_exponent :
    Algebra.adjoin ℤ {θ} = ⊤ ↔ ∀ p : ℕ, p.Prime → ¬p ∣ exponent θ := by
  rw [← exponent_eq_one_iff, Nat.eq_one_iff_not_exists_prime_dvd]

variable {p : ℕ} [hp : Fact p.Prime]

private theorem intCast_dvd_norm_sub_one {c u : 𝓞 K} (h : c + (p : 𝓞 K) * u = 1) :
    (p : ℤ) ∣ Algebra.norm ℤ c - 1 := by
  classical
  let b := RingOfIntegers.basis K
  have hc : c = 1 - (p : ℤ) • u := by
    rw [zsmul_eq_mul]
    push_cast
    linear_combination h
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_one, sub_eq_zero,
    Algebra.norm_eq_matrix_det b,
    show (((Algebra.leftMulMatrix b c).det : ℤ) : ZMod p) =
      (Int.castRingHom (ZMod p)) (Algebra.leftMulMatrix b c).det from rfl,
    RingHom.map_det]
  have hX : (Algebra.leftMulMatrix b c).map (Int.castRingHom (ZMod p)) = 1 := by
    rw [hc, map_sub, map_one, map_smul]
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub,
      map_mul, map_natCast, ZMod.natCast_self, zero_mul, sub_zero]
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  rw [RingHom.mapMatrix_apply, hX, Matrix.det_one]

/-- A rational prime `p` does not divide the exponent of `θ` if and only if the conductor
of `θ` and `p • 𝓞 K` are comaximal. -/
theorem not_dvd_exponent_iff_conductor_sup_span_eq_top :
    ¬p ∣ exponent θ ↔ conductor ℤ θ ⊔ Ideal.span {(p : 𝓞 K)} = ⊤ := by
  rw [not_dvd_exponent_iff]
  constructor
  · intro h
    rw [codisjoint_iff, Ideal.eq_top_iff_one] at h
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h
    rw [Ideal.eq_top_iff_one, show (1 : 𝓞 K) = algebraMap ℤ (𝓞 K) (a + b) by
      rw [hab, map_one], map_add]
    refine add_mem (Ideal.mem_sup_left (Ideal.mem_comap.mp ha)) (Ideal.mem_sup_right ?_)
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hb
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ (by simp)
  · intro h
    rw [Ideal.eq_top_iff_one] at h
    obtain ⟨c, hc, v, hv, hcv⟩ := Submodule.mem_sup.mp h
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp hv
    rw [codisjoint_iff, Ideal.eq_top_iff_one]
    -- The absolute norm `N` of `c` lies in `conductor ∩ ℤ` and is `1 mod p`.
    set N : ℕ := Ideal.absNorm (Ideal.span {c}) with hN
    have hNmem : ((N : ℤ)) ∈ (conductor ℤ θ).under ℤ := by
      rw [Ideal.under_def, Ideal.mem_comap, map_natCast]
      exact (Ideal.span_singleton_le_iff_mem _).mpr hc (Ideal.absNorm_mem (Ideal.span {c}))
    have hpN : ¬(p : ℤ) ∣ (N : ℤ) := by
      rw [hN, Ideal.absNorm_span_singleton]
      intro hdvd
      rw [Int.dvd_natAbs] at hdvd
      have h₁ : (p : ℤ) ∣ Algebra.norm ℤ c - 1 :=
        intCast_dvd_norm_sub_one (u := u) (by rwa [mul_comm] at hcv)
      have h₂ : (p : ℤ) ∣ 1 := by
        simpa [sub_sub_cancel] using dvd_sub hdvd h₁
      exact hp.out.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h₂)
    obtain ⟨x, y, hxy⟩ : IsCoprime ((N : ℤ)) ((p : ℤ)) :=
      ((Nat.prime_iff_prime_int.mp hp.out).coprime_iff_not_dvd.mpr hpN).symm
    rw [← hxy]
    exact add_mem (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ hNmem))
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))

include hθ in
/-- If the minimal polynomial of `θ` is Eisenstein at the rational prime `p`, then `p`
does not divide the exponent of `θ`.  Consequently `ℤ[θ]` is maximal at `p`. -/
theorem not_dvd_exponent_of_minpoly_isEisensteinAt
    (hei : (minpoly ℤ θ).IsEisensteinAt (Submodule.span ℤ {(p : ℤ)})) :
    ¬p ∣ exponent θ := by
  have hE : exponent θ ≠ 0 := exponent_ne_zero hθ
  -- Write `exponent θ = p ^ k * d` with `p ∤ d`; it suffices to show `(d : 𝓞 K)` lies in
  -- the conductor of `θ`, since then `exponent θ ∣ d`.
  obtain ⟨k, d, hpd, hdE⟩ := Nat.exists_eq_pow_mul_and_not_dvd hE p hp.out.ne_one
  -- the power basis of `K` generated by `θ`
  have hint : IsIntegral ℚ ((θ : K)) := (θ.isIntegral.map
    (IsScalarTower.toAlgHom ℤ (𝓞 K) K)).tower_top
  let pb : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop hint hθ
  have hpbgen : pb.gen = (θ : K) := rfl
  -- `(exponent θ : 𝓞 K)` is in the conductor
  have hEmem : ((exponent θ : 𝓞 K)) ∈ conductor ℤ θ :=
    Int.absNorm_under_mem (conductor ℤ θ)
  have hdmem : ((d : 𝓞 K)) ∈ conductor ℤ θ := by
    rw [mem_conductor_iff]
    intro b
    have hb : ((exponent θ : 𝓞 K)) * b ∈ Algebra.adjoin ℤ {θ} := mem_conductor_iff.mp hEmem b
    -- push to `K` and apply the Eisenstein descent lemma
    have hmap : ∀ w : 𝓞 K, w ∈ Algebra.adjoin ℤ {θ} ↔
        (w : K) ∈ Algebra.adjoin ℤ {((θ : K))} := by
      intro w
      rw [show ({((θ : K))} : Set K) = (IsScalarTower.toAlgHom ℤ (𝓞 K) K) '' {θ} by simp,
        Algebra.adjoin_image, Subalgebra.mem_map]
      exact ⟨fun hw ↦ ⟨w, hw, rfl⟩, fun ⟨w', hw', h⟩ ↦ by
        rwa [(FaithfulSMul.algebraMap_injective (𝓞 K) K).eq_iff.mp h] at hw'⟩
    rw [hmap]
    have heq : (p : ℤ) ^ k • ((d : 𝓞 K) * b) = ((exponent θ : 𝓞 K)) * b := by
      rw [zsmul_eq_mul, ← mul_assoc]
      norm_cast
      rw [← hdE]
    have hz : (p : ℤ) ^ k • (((d : 𝓞 K) * b : 𝓞 K) : K) ∈ Algebra.adjoin ℤ {((θ : K))} := by
      rw [show (p : ℤ) ^ k • (((d : 𝓞 K) * b : 𝓞 K) : K) =
          (((p : ℤ) ^ k • ((d : 𝓞 K) * b) : 𝓞 K) : K) by push_cast [zsmul_eq_mul]; ring,
        heq, ← hmap]
      exact hb
    have := mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt
      (B := pb) (Nat.prime_iff_prime_int.mp hp.out) (hpbgen ▸ θ.isIntegral.map
        (IsScalarTower.toAlgHom ℤ (𝓞 K) K))
      (((d : 𝓞 K) * b).isIntegral.map (IsScalarTower.toAlgHom ℤ (𝓞 K) K))
      (hpbgen ▸ hz) (by rw [hpbgen, NumberField.RingOfIntegers.minpoly_coe]; exact hei)
    rwa [hpbgen] at this
  -- conclude: `exponent θ ∣ d`, hence `p ∤ exponent θ`
  have hdvd : exponent θ ∣ d :=
    Int.natCast_dvd_natCast.mp (Int.cast_mem_ideal_iff.mp (by push_cast; exact hdmem))
  exact fun hpE ↦ hpd (hpE.trans hdvd)

end RingOfIntegers
