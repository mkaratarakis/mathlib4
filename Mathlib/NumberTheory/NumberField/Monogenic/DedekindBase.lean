/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.Conductor

/-!
# Monogenity over an integrally closed base

The local theory of monogenity on this branch — the obstruction lemma, Uchida's criterion,
and the ideal calculus of Kaur–Kumar–Remete's Section 2 — is developed over the ring of
integers of a number field with a prime *element* `π`.  That restricts the resulting criteria
to principal primes, i.e. to base fields of class number one, which is the one gap left in
Problem 2 of

* S. Kaur, S. Kumar, L. Remete, *On the index of power compositional polynomials*,
  Finite Fields Appl. **107** (2025), 102642.

This file begins the removal of that restriction, by redoing the theory over an arbitrary
integrally closed base `A`, with `B` the integral closure of `A` in a finite extension `L` of
its fraction field `K`.  Localising such an `A` at a maximal ideal gives a discrete valuation
ring, where every ideal *is* principal, so a criterion available over an arbitrary base
specialises to one at an arbitrary maximal ideal of `𝓞 K`.

Nothing here is number-theoretic: the ring of integers of a number field is one instance of
this setup, and `(𝓞 K)_𝔭` is another.

## Main results

* `Monogenic.exists_mul_mem_adjoin_notMem_adjoin_of_factor`: **the obstruction lemma over an
  integrally closed base.**  Given a decomposition
  `minpoly A θ = h ^ 2 g + π (k h) + π ^ 2 t` with `h * g` monic of degree `< deg (minpoly)`,
  the element `h(θ) g(θ) / π` lies in `B` but not in `A[θ]`, while `π` times it does.

* `Monogenic.adjoin_ne_top_of_sq_factor`: consequently `A[θ] ≠ B`.

## Implementation notes

The proof is the one already used over `𝓞 K`, and the point of this file is that it needs no
property of the base beyond integral closedness: the quadratic-integrality trick produces an
element of `L` integral over `B`, hence over `A`, hence in `B`; and the degree comparison that
rules out `h(θ) g(θ) ∈ π A[θ]` uses only that the minimal polynomial over `A` and over `K`
have the same degree, which is `minpoly.isIntegrallyClosed_eq_field_fractions`.
-/

@[expose] public section

noncomputable section

open Polynomial

namespace Monogenic

variable {A K B L : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [CommRing B] [IsDomain B] [Algebra A B]
  [Field L] [Algebra A L] [Algebra K L] [Algebra B L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsIntegralClosure B A L] [IsFractionRing B L]
  {θ : B}

include K L in
/-- **The obstruction lemma over an integrally closed base.**  Let `π` be a prime element of
`A` and suppose the minimal polynomial of `θ` over `A` decomposes as
`h ^ 2 g + π (k h) + π ^ 2 t` with `h * g` monic of degree below that of the minimal
polynomial.  Then `z = h(θ) g(θ) / π` lies in `B`, satisfies `π z ∈ A[θ]`, and does not lie in
`A[θ]`.

The first two assertions come from the quadratic integrality of `z`: it satisfies
`z ^ 2 + k(θ) z + t(θ) g(θ) = 0`, so it is integral over `B`, hence over `A`, hence lies in
`B` because `B` is the integral closure.  The third is a degree count: were `z ∈ A[θ]`, one
could write `h(θ) g(θ) = π c(θ)` with `deg c < deg (minpoly A θ)`, and then `h * g = π c` as
polynomials, whose leading coefficients make `π` a unit. -/
theorem exists_mul_mem_adjoin_notMem_adjoin_of_factor {π : A} (hπ : Prime π)
    {h g k t : A[X]} (hW : (h * g).Monic)
    (hdeg : (h * g).natDegree < (minpoly A θ).natDegree)
    (hfeq : minpoly A θ = h ^ 2 * g + C π * (k * h) + C π ^ 2 * t) :
    ∃ z : B, algebraMap A B π * z ∈ Algebra.adjoin A {θ} ∧ z ∉ Algebra.adjoin A {θ} := by
  have hint : IsIntegral A θ := IsIntegralClosure.isIntegral A L θ
  set f : A[X] := minpoly A θ with hf
  set πι : B := algebraMap A B π with hπι
  set πK : L := algebraMap B L πι with hπK
  have hπKeq : πK = algebraMap A L π := by
    rw [hπK, hπι]
    exact (IsScalarTower.algebraMap_apply A B L π).symm
  have hπK0 : πK ≠ 0 := by
    rw [hπKeq, IsScalarTower.algebraMap_apply A K L]
    simp only [ne_eq, map_eq_zero]
    exact fun h0 => hπ.ne_zero (IsFractionRing.injective A K (by simpa using h0))
  -- the fundamental relation in `B`
  set πS : B := aeval θ h with hπSdef
  set S : B := aeval θ g with hS
  set kθ : B := aeval θ k with hk
  set tθ : B := aeval θ t with ht
  have hrel : πS ^ 2 * S + πι * (kθ * πS) + πι ^ 2 * tθ = 0 := by
    have h1 : aeval θ f = 0 := hf ▸ minpoly.aeval A θ
    rw [hfeq] at h1
    simp only [map_add, map_mul, map_pow, aeval_C] at h1
    rw [hπSdef, hS, hk, ht, hπι]
    linear_combination h1
  set y : B := πS * S with hydef
  have hy : y ^ 2 + (πι * kθ) * y + (πι ^ 2 * tθ) * S = 0 := by
    rw [hydef]
    linear_combination S * hrel
  -- `z = y / π` is integral over `B`, hence lies in `B`
  set z : L := algebraMap B L y / πK with hz
  have hzy : πK * z = algebraMap B L y := by
    rw [hz]; field_simp
  have hzint : IsIntegral B z := by
    refine ⟨X ^ 2 + (C kθ * X + C (tθ * S)), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_add
        (lt_of_le_of_lt Polynomial.degree_linear_le (by norm_num))
    · simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]
      have hyK := congrArg (algebraMap B L) hy
      simp only [map_add, map_mul, map_pow, map_zero] at hyK
      rw [← hzy, ← hπK] at hyK
      have hp2 : πK ^ 2 ≠ 0 := pow_ne_zero _ hπK0
      have hgoal : πK ^ 2 * (z ^ 2 + (algebraMap B L kθ * z +
          algebraMap B L tθ * algebraMap B L S)) = 0 := by
        linear_combination hyK
      have h2 := (mul_eq_zero.mp hgoal).resolve_left hp2
      rw [map_mul]
      linear_combination h2
  haveI : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
  have hzintA : IsIntegral A z := isIntegral_trans z hzint
  obtain ⟨z', hz'⟩ := IsIntegralClosure.isIntegral_iff (A := B) |>.mp hzintA
  have hpz' : πι * z' = y := by
    apply IsFractionRing.injective B L
    rw [map_mul, hz', ← hπK, hzy]
  refine ⟨z', ?_, ?_⟩
  · rw [hpz', hydef, hπSdef, hS]
    exact mul_mem (Polynomial.aeval_mem_adjoin_singleton _ θ)
      (Polynomial.aeval_mem_adjoin_singleton _ θ)
  -- if `z'` were in `A[θ]`, comparing degrees would make `π` a unit
  intro hz'mem
  have hfmonic : f.Monic := hf ▸ minpoly.monic hint
  have haevf : aeval θ f = 0 := hf ▸ minpoly.aeval A θ
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hz'mem
  obtain ⟨c, hc⟩ := hz'mem
  replace hc : aeval θ c = z' := hc
  set c' : A[X] := c %ₘ f with hc'
  have haevalc' : aeval θ c' = z' := by
    rw [hc', Polynomial.modByMonic_eq_sub_mul_div c f, map_sub, map_mul, haevf, zero_mul,
      sub_zero, hc]
  have hdegc' : c'.degree < f.degree := Polynomial.degree_modByMonic_lt c hfmonic
  set W : A[X] := h * g with hWdef
  have haevalW : aeval θ W = y := by rw [hWdef, map_mul, hydef, hπSdef, hS]
  have hann : aeval θ (W - C π * c') = 0 := by
    rw [map_sub, haevalW, map_mul, aeval_C, haevalc', ← hpz', hπι]
    ring
  have hfne : f ≠ 0 := minpoly.ne_zero hint
  have hdegW : W.degree < f.degree := by
    rw [Polynomial.degree_eq_natDegree hW.ne_zero, Polynomial.degree_eq_natDegree hfne]
    exact_mod_cast hdeg
  have hdeglt : (W - C π * c').degree < f.degree := by
    apply lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
    rw [max_lt_iff]
    refine ⟨hdegW, lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_⟩
    rw [Polynomial.degree_C hπ.ne_zero, zero_add]
    exact hdegc'
  have hWeq : W = C π * c' := by
    by_contra hne
    have hsubne : W - C π * c' ≠ 0 := sub_ne_zero_of_ne hne
    have hmapne : (W - C π * c').map (algebraMap A K) ≠ 0 := by
      rwa [Ne, Polynomial.map_eq_zero_iff (IsFractionRing.injective A K)]
    have haev : Polynomial.aeval (algebraMap B L θ)
        ((W - C π * c').map (algebraMap A K)) = 0 := by
      rw [aeval_map_algebraMap, aeval_algebraMap_apply, hann, map_zero]
    have hge := minpoly.degree_le_of_ne_zero K (algebraMap B L θ) hmapne haev
    rw [minpoly.isIntegrallyClosed_eq_field_fractions K L hint,
      Polynomial.degree_map_eq_of_injective (IsFractionRing.injective A K),
      Polynomial.degree_map_eq_of_injective (IsFractionRing.injective A K)] at hge
    exact absurd (hge.trans_lt hdeglt) (lt_irrefl _)
  have hlead : (1 : A) = π * c'.leadingCoeff := by
    have h1 := congrArg Polynomial.leadingCoeff hWeq
    rwa [hW.leadingCoeff, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C] at h1
  exact hπ.not_unit (isUnit_of_dvd_one ⟨c'.leadingCoeff, hlead⟩)

include K L in
/-- **Non-maximality from a repeated-factor decomposition, over an integrally closed base.**
Under the hypotheses of the obstruction lemma, `A[θ]` is not all of `B`. -/
theorem adjoin_ne_top_of_sq_factor {π : A} (hπ : Prime π)
    {h g k t : A[X]} (hW : (h * g).Monic)
    (hdeg : (h * g).natDegree < (minpoly A θ).natDegree)
    (hfeq : minpoly A θ = h ^ 2 * g + C π * (k * h) + C π ^ 2 * t) :
    Algebra.adjoin A {θ} ≠ ⊤ := by
  obtain ⟨z, -, hz⟩ :=
    exists_mul_mem_adjoin_notMem_adjoin_of_factor (K := K) (L := L) hπ hW hdeg hfeq
  intro htop
  rw [htop] at hz
  exact hz trivial

end Monogenic
