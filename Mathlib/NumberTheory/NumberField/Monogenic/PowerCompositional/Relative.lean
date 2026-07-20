/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.Monogenic.PowerCompositional.Main
public import Mathlib.NumberTheory.NumberField.Monogenic.Relative

/-!
# Power compositional polynomials over a number field base

Problem 2 of S. Kaur, S. Kumar and L. Remete,
*On the index of power compositional polynomials*, Finite Fields Appl. **107** (2025), 102642,
asks for necessary and sufficient conditions for `f(X ^ k)` to be monogenic over an arbitrary
number field base, rather than over `ℚ`.  This file proves the *necessity* half of the
relative analogue of their Theorem 1.1.

The organising notion is `NumberField.Relative.IsIndexDivisor π f`: a decomposition
`f = h ^ 2 g + π (k h) + π ^ 2 t` with `h * g` monic of degree `< deg f`.  Both directions of
Uchida's criterion are available relatively
(`NumberField.Relative.isIndexDivisor_iff_exists_notMem`): `π` is an index divisor of the
minimal polynomial of `θ` exactly when `𝓞 K[θ]` fails to be `π`-saturated in `𝓞 K₁`.

## Main results

* `NumberField.Relative.IsIndexDivisor.expand`: **Lemma 2.6, relative version** --- an index
  divisor of `f` is an index divisor of `f(X ^ ℓ)`.  Unlike the absolute proof, which goes
  through Uchida's criterion, this one is immediate: applying `X ↦ X ^ ℓ` to a decomposition
  gives a decomposition, and `expand` multiplies all degrees by `ℓ`.

* `NumberField.Relative.isIndexDivisor_expand_of_sq_dvd_coeff_zero`: **Proposition 2.3,
  relative version** --- if `π ^ 2` divides `f(0)` and `ℓ ≥ 2` then `π` is an index divisor
  of `f(X ^ ℓ)`.

* `NumberField.Relative.adjoin_ne_top_of_sq_dvd_coeff_zero`: consequently, if `f(X ^ ℓ)` is
  monogenic over `𝓞 K` with `ℓ ≥ 2`, then no square of a prime of `𝓞 K` divides `f(0)`.
  This is condition (3) of Theorem 1.1, and it is necessary over any number field base.

* `NumberField.Relative.adjoin_ne_top_of_isIndexDivisor_expand`: likewise condition (1) is
  necessary: an index divisor of `f` obstructs monogenity of `f(X ^ k)`.

## Main results, continued

* `NumberField.Relative.isIndexDivisor_iff_exists_notMem`: **Uchida's criterion over a
  number field base**.  The forward direction is the obstruction lemma; the backward
  direction combines `NumberField.Relative.exists_splitting_of_not_saturated` --- the
  existence half, extracted from the proof of relative Dedekind sufficiency, where it was
  already present --- with `NumberField.Relative.isIndexDivisor_of_splitting`, which
  normalises a splitting into the required shape.

## What is missing for Problem 2

Uchida's criterion is now available relatively, and the Frobenius twist is settled by
`NumberField.Relative.dvd_expand_iff_map_frobenius_dvd`: it is real — the absolute identity
`f(X ^ p) = f ^ p` mod `π` fails as soon as the residue field is not prime — but harmless,
because `g ↦ g ^ σ` is a *bijection* on the irreducibles.  Consequently every statement of
Section 2 that quantifies existentially over the witnessing prime survives verbatim, and only
those stated for a fixed `g`, such as Theorem 2.4, need the twist inserted.

That leaves one genuine obstacle:

* the base need not be principal, so a prime *element* `π` need not exist at all; the global
  packaging `NumberField.Relative.adjoin_eq_top_of_forall_prime_saturated` currently assumes
  `IsPrincipalIdealRing (𝓞 K)`.  Over a general Dedekind base the whole development would
  have to be redone with prime *ideals* and localisation.

## References

* [S. Kaur, S. Kumar, L. Remete, *On the index of power compositional polynomials*][KKR2025]
-/

@[expose] public section

noncomputable section

open Polynomial NumberField

namespace NumberField.Relative

variable {K K₁ : Type*} [Field K] [NumberField K] [Field K₁] [NumberField K₁]
  [Algebra K K₁] {θ : 𝓞 K₁}

/-- `π` **is an index divisor of** `f`: a decomposition `f = h ^ 2 g + π (k h) + π ^ 2 t`
with `h * g` monic of degree below that of `f`.

Over `ℤ` this is equivalent, by Uchida's criterion, to `p` dividing the index
`[𝓞 K : ℤ[θ]]` --- compare `Polynomial.IsIndexDivisor`.  Over a general base the
implication `IsIndexDivisor → not monogenic` is
`NumberField.Relative.adjoin_ne_top_of_isIndexDivisor`; the converse is open. -/
def IsIndexDivisor {K : Type*} [Field K] [NumberField K] (π : 𝓞 K) (f : (𝓞 K)[X]) : Prop :=
  ∃ h g k t : (𝓞 K)[X], (h * g).Monic ∧ (h * g).natDegree < f.natDegree ∧
    f = h ^ 2 * g + C π * (k * h) + C π ^ 2 * t

/-- An index divisor of the minimal polynomial obstructs monogenity. -/
theorem adjoin_ne_top_of_isIndexDivisor {π : 𝓞 K} (hπ : Prime π)
    (h : IsIndexDivisor π (minpoly (𝓞 K) θ)) :
    Algebra.adjoin (𝓞 K) {θ} ≠ ⊤ := by
  obtain ⟨a, b, c, d, hm, hdeg, heq⟩ := h
  exact adjoin_ne_top_of_sq_factor hπ hm hdeg heq

/-- **Lemma 2.6, relative version.**  An index divisor of `f` is an index divisor of
`f(X ^ ℓ)`.

Substituting `X ^ ℓ` in a decomposition `f = h ^ 2 g + π (k h) + π ^ 2 t` gives one for
`f(X ^ ℓ)`, since `expand` is a ring homomorphism fixing the constants; it multiplies all
degrees by `ℓ`, so the degree condition is preserved.  No form of Uchida's criterion is
needed. -/
theorem IsIndexDivisor.expand {π : 𝓞 K} {f : (𝓞 K)[X]} {ℓ : ℕ} (hℓ : 0 < ℓ)
    (h : IsIndexDivisor π f) : IsIndexDivisor π (Polynomial.expand (𝓞 K) ℓ f) := by
  obtain ⟨a, b, c, d, hm, hdeg, heq⟩ := h
  refine ⟨Polynomial.expand (𝓞 K) ℓ a, Polynomial.expand (𝓞 K) ℓ b,
    Polynomial.expand (𝓞 K) ℓ c, Polynomial.expand (𝓞 K) ℓ d, ?_, ?_, ?_⟩
  · rw [← map_mul]
    exact hm.expand hℓ
  · rw [← map_mul, natDegree_expand, natDegree_expand]
    exact (Nat.mul_lt_mul_right hℓ).mpr hdeg
  · rw [heq]
    simp only [map_add, map_mul, map_pow, expand_C]

/-- **Proposition 2.3, relative version.**  If `π ^ 2` divides `f(0)` and `ℓ ≥ 2`, then `π`
is an index divisor of `f(X ^ ℓ)`.

The witness is the same as in the absolute case: `f(X ^ ℓ)` has no terms in degrees `1` to
`ℓ - 1`, so `f(X ^ ℓ) - f(0)` is divisible by `X ^ 2`, and `f(0)` is divisible by `π ^ 2`. -/
theorem isIndexDivisor_expand_of_sq_dvd_coeff_zero {π : 𝓞 K} (hπ : Prime π) {f : (𝓞 K)[X]}
    (hf : f.Monic) {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (hπ2 : π ^ 2 ∣ f.coeff 0) :
    IsIndexDivisor π (Polynomial.expand (𝓞 K) ℓ f) := by
  have hℓ0 : 0 < ℓ := by omega
  set F := Polynomial.expand (𝓞 K) ℓ f with hFdef
  have hFm : F.Monic := hf.expand hℓ0
  -- `f` is nonconstant: otherwise `f = 1` and `π ^ 2 ∣ 1`.
  have hfd : 0 < f.natDegree := by
    rcases Nat.eq_zero_or_pos f.natDegree with h0 | h
    · exfalso
      rw [hf.natDegree_eq_zero.mp h0] at hπ2
      simp only [coeff_one_zero] at hπ2
      exact hπ.not_unit (isUnit_of_dvd_one ((dvd_pow_self π two_ne_zero).trans hπ2))
    · exact h
  have hFd : 0 < F.natDegree := by
    rw [hFdef, natDegree_expand]
    positivity
  have hF0 : F.coeff 0 = f.coeff 0 := by
    rw [hFdef, coeff_expand hℓ0]
    simp
  -- `X ^ 2` divides `F - F(0)`.
  obtain ⟨G, hG⟩ : (X : (𝓞 K)[X]) ^ 2 ∣ F - C (F.coeff 0) := by
    rw [X_pow_dvd_iff]
    intro d hd
    interval_cases d
    · simp
    · rw [coeff_sub, coeff_C, hFdef, coeff_expand hℓ0]
      simp [Nat.dvd_one.not.mpr (by omega : ℓ ≠ 1)]
  have hdegC : (C (F.coeff 0)).degree < F.degree :=
    lt_of_le_of_lt degree_C_le (natDegree_pos_iff_degree_pos.mp hFd)
  have hXG2 : ((X : (𝓞 K)[X]) ^ 2 * G).Monic := hG ▸ hFm.sub_of_left hdegC
  have hXG : ((X : (𝓞 K)[X]) * G).Monic := by
    refine monic_X.of_mul_monic_left ?_
    rw [show (X : (𝓞 K)[X]) * ((X : (𝓞 K)[X]) * G) = X ^ 2 * G by ring]
    exact hXG2
  have hG0 : G ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hXG2
    exact not_monic_zero hXG2
  have hnd : ((X : (𝓞 K)[X]) * G).natDegree < F.natDegree := by
    have h2 : ((X : (𝓞 K)[X]) ^ 2 * G).natDegree = F.natDegree := by
      rw [← hG, natDegree_sub_C]
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hG0, natDegree_X_pow] at h2
    rw [natDegree_mul X_ne_zero hG0, natDegree_X]
    omega
  obtain ⟨c, hc⟩ := hπ2
  refine ⟨X, G, 0, C c, hXG, hnd, ?_⟩
  have hCF0 : C (F.coeff 0) = C π ^ 2 * C c := by
    rw [hF0, hc, map_mul, map_pow]
  rw [← hCF0]
  linear_combination hG

/-! ### Uchida's criterion over a number field base -/

section Uchida

attribute [local instance] Ideal.Quotient.field

variable {π : 𝓞 K}

omit [NumberField K] in
/-- Membership in `⟨π, P⟩` is divisibility of the reductions modulo `π`. -/
theorem mem_span_pair_iff_map_dvd {P x : (𝓞 K)[X]} :
    x ∈ (Ideal.span {C π, P} : Ideal ((𝓞 K)[X])) ↔
      P.map (Ideal.Quotient.mk (Ideal.span {π})) ∣
        x.map (Ideal.Quotient.mk (Ideal.span {π})) := by
  constructor
  · rintro hx
    obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hx
    refine ⟨b.map (Ideal.Quotient.mk (Ideal.span {π})), ?_⟩
    simp only [Polynomial.map_add, Polynomial.map_mul, map_C,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self π), C_0]
    ring
  · rintro ⟨y₁, hy₁⟩
    obtain ⟨y, hy⟩ := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective y₁
    have hzero : (x - P * y).map (Ideal.Quotient.mk (Ideal.span {π})) = 0 := by
      rw [Polynomial.map_sub, Polynomial.map_mul, hy, ← hy₁, sub_self]
    obtain ⟨z, hz⟩ := map_quotient_span_eq_zero_iff.mp hzero
    exact Ideal.mem_span_pair.mpr ⟨z, y, by linear_combination -hz⟩

/-- If `π * s` lies in `⟨π, P⟩ ^ 2` then `s` lies in `⟨π, P⟩`. -/
theorem mem_span_pair_of_C_mul_mem_sq (hπ : Prime π) {P s : (𝓞 K)[X]}
    (hP0 : P.map (Ideal.Quotient.mk (Ideal.span {π})) ≠ 0)
    (hs : C π * s ∈ (Ideal.span {C π, P} : Ideal ((𝓞 K)[X])) ^ 2) :
    s ∈ (Ideal.span {C π, P} : Ideal ((𝓞 K)[X])) := by
  haveI hmax : (Ideal.span {π} : Ideal (𝓞 K)).IsMaximal :=
    ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ).isMaximal
      (by simpa [Ideal.span_singleton_eq_bot] using hπ.ne_zero)
  have hCπ0 : (C π : (𝓞 K)[X]) ≠ 0 := fun h => hπ.ne_zero (by simpa using congrArg (·.coeff 0) h)
  obtain ⟨u, v, w, huvw⟩ := Ideal.mem_span_pair_sq_iff.mp hs
  have hwdvd : (C π : (𝓞 K)[X]) ∣ w := by
    rw [← map_quotient_span_eq_zero_iff]
    have hPw : (P ^ 2 * w).map (Ideal.Quotient.mk (Ideal.span {π})) = 0 := by
      have h2 : P ^ 2 * w = C π * s - C π ^ 2 * u - C π * P * v := by linear_combination -huvw
      rw [h2]
      simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_C,
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self π), C_0, zero_mul,
        zero_pow two_ne_zero, sub_self]
    rw [Polynomial.map_mul, Polynomial.map_pow] at hPw
    exact (mul_eq_zero.mp hPw).resolve_left (pow_ne_zero _ hP0)
  obtain ⟨w', rfl⟩ := hwdvd
  have hcancel : s = C π * u + P * v + P ^ 2 * w' :=
    mul_left_cancel₀ hCπ0 (by linear_combination huvw)
  exact Ideal.mem_span_pair.mpr ⟨u, v + P * w', by rw [hcancel]; ring⟩

/-- An element of `⟨π, P⟩ ^ 2` of degree below `2 deg P` is divisible by `π`. -/
theorem C_dvd_of_mem_sq_of_natDegree_lt (hπ : Prime π) {P r : (𝓞 K)[X]} (hPm : P.Monic)
    (hr : r ∈ (Ideal.span {C π, P} : Ideal ((𝓞 K)[X])) ^ 2)
    (hdeg : r.natDegree < 2 * P.natDegree) : (C π : (𝓞 K)[X]) ∣ r := by
  haveI hmax : (Ideal.span {π} : Ideal (𝓞 K)).IsMaximal :=
    ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ).isMaximal
      (by simpa [Ideal.span_singleton_eq_bot] using hπ.ne_zero)
  rw [← map_quotient_span_eq_zero_iff]
  by_contra hne
  obtain ⟨u, v, w, huvw⟩ := Ideal.mem_span_pair_sq_iff.mp hr
  have hdvd : (P.map (Ideal.Quotient.mk (Ideal.span {π}))) ^ 2 ∣
      r.map (Ideal.Quotient.mk (Ideal.span {π})) := by
    refine ⟨w.map (Ideal.Quotient.mk (Ideal.span {π})), ?_⟩
    rw [huvw]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_C,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self π), C_0, zero_mul,
      zero_pow two_ne_zero, zero_add]
  have hle := Polynomial.natDegree_le_of_dvd hdvd hne
  rw [(hPm.map _).natDegree_pow, hPm.natDegree_map] at hle
  exact absurd (hle.trans natDegree_map_le) (by omega)

/-- **Normalisation of a splitting.**  A splitting `f = A B + π N` whose three factors are
divisible, modulo `π`, by a common monic irreducible `Pi` can be rewritten in the shape
required by the obstruction lemma, so `π` is an index divisor of `f`.

Dividing `f` by the monic `P ^ 2`, where `P` lifts `Pi`, the remainder has degree below
`2 deg P` and is therefore divisible by `π`; dividing it by `π` lands in `⟨π, P⟩`, and the
quotient is monic because `P ^ 2 q = f - r` is. -/
theorem isIndexDivisor_of_splitting (hπ : Prime π) {f : (𝓞 K)[X]} (hfm : f.Monic)
    {Pi : (𝓞 K ⧸ Ideal.span {π})[X]} (hPim : Pi.Monic) (hPid : 0 < Pi.natDegree)
    {A B N : (𝓞 K)[X]} (hsplit : f = A * B + C π * N)
    (hA : Pi ∣ A.map (Ideal.Quotient.mk (Ideal.span {π})))
    (hB : Pi ∣ B.map (Ideal.Quotient.mk (Ideal.span {π})))
    (hN : Pi ∣ N.map (Ideal.Quotient.mk (Ideal.span {π}))) :
    IsIndexDivisor π f := by
  haveI hmax : (Ideal.span {π} : Ideal (𝓞 K)).IsMaximal :=
    ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ).isMaximal
      (by simpa [Ideal.span_singleton_eq_bot] using hπ.ne_zero)
  obtain ⟨P, hPmap, -, hPm⟩ := lifts_and_degree_eq_and_monic
    ((mem_lifts Pi).mpr (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective Pi)) hPim
  have hPdeg : P.natDegree = Pi.natDegree := by rw [← hPmap, hPm.natDegree_map]
  have hP0 : P.map (Ideal.Quotient.mk (Ideal.span {π})) ≠ 0 := by
    rw [hPmap]; exact hPim.ne_zero
  -- `f` lies in the square of `⟨π, P⟩`
  have hmemP : (C π : (𝓞 K)[X]) ∈ (Ideal.span {C π, P} : Ideal ((𝓞 K)[X])) :=
    Ideal.subset_span (by simp)
  have hfmem : f ∈ (Ideal.span {C π, P} : Ideal ((𝓞 K)[X])) ^ 2 := by
    rw [hsplit, sq]
    exact Ideal.add_mem _
      (Ideal.mul_mem_mul (mem_span_pair_iff_map_dvd.mpr (hPmap ▸ hA))
        (mem_span_pair_iff_map_dvd.mpr (hPmap ▸ hB)))
      (Ideal.mul_mem_mul hmemP (mem_span_pair_iff_map_dvd.mpr (hPmap ▸ hN)))
  -- divide by `P ^ 2`
  have hP2m : (P ^ 2).Monic := hPm.pow 2
  set q := f /ₘ P ^ 2 with hqdef
  set r := f %ₘ P ^ 2 with hrdef
  have hdiv : r + P ^ 2 * q = f := modByMonic_add_div f (P ^ 2)
  have hdvdmap : (P.map (Ideal.Quotient.mk (Ideal.span {π}))) ^ 2 ∣
      f.map (Ideal.Quotient.mk (Ideal.span {π})) := by
    obtain ⟨u, v, w, huvw⟩ := Ideal.mem_span_pair_sq_iff.mp hfmem
    refine ⟨w.map (Ideal.Quotient.mk (Ideal.span {π})), ?_⟩
    rw [huvw]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_C,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self π), C_0, zero_mul,
      zero_pow two_ne_zero, zero_add]
  have hle : 2 * P.natDegree ≤ f.natDegree := by
    have h := Polynomial.natDegree_le_of_dvd hdvdmap (hfm.map _).ne_zero
    rwa [(hPm.map _).natDegree_pow, hPm.natDegree_map, hfm.natDegree_map] at h
  have hrdegPi : r.degree < (P ^ 2).degree := degree_modByMonic_lt _ hP2m
  have hrdegf : r.degree < f.degree := by
    refine hrdegPi.trans_le ?_
    rw [degree_eq_natDegree hP2m.ne_zero, degree_eq_natDegree hfm.ne_zero, hPm.natDegree_pow]
    exact_mod_cast hle
  have hrmem : r ∈ (Ideal.span {C π, P} : Ideal ((𝓞 K)[X])) ^ 2 := by
    have hsub : r = f - P ^ 2 * q := by linear_combination hdiv
    rw [hsub]
    refine Ideal.sub_mem _ hfmem (Ideal.mul_mem_right _ _ ?_)
    rw [sq, sq]
    exact Ideal.mul_mem_mul (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
  have hrsmall : r.natDegree < 2 * P.natDegree := by
    have hne1 : P ^ 2 ≠ 1 := fun h => by
      have h0 : (P ^ 2).natDegree = 0 := by rw [h]; simp
      rw [hPm.natDegree_pow, hPdeg] at h0; omega
    have h := natDegree_modByMonic_lt f hP2m hne1
    rwa [hPm.natDegree_pow] at h
  obtain ⟨s, hs⟩ := C_dvd_of_mem_sq_of_natDegree_lt hπ hPm hrmem hrsmall
  obtain ⟨c, k, hck⟩ := Ideal.mem_span_pair.mp
    (mem_span_pair_of_C_mul_mem_sq hπ hP0 (hs ▸ hrmem))
  -- the quotient is monic of the right degree
  have hP2q : (P ^ 2 * q).Monic := by
    have heq : P ^ 2 * q = f - r := by linear_combination hdiv
    rw [heq]; exact hfm.sub_of_left hrdegf
  have hqm : q.Monic := hP2m.of_mul_monic_left hP2q
  have hdegeq : (P ^ 2 * q).natDegree = f.natDegree := by
    have heq : P ^ 2 * q = f - r := by linear_combination hdiv
    rw [heq]
    exact natDegree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt hrdegf)
  refine ⟨P, q, k, c, hPm.mul hqm, ?_, ?_⟩
  · rw [hPm.natDegree_mul hqm]
    rw [hP2m.natDegree_mul hqm, hPm.natDegree_pow] at hdegeq
    omega
  · linear_combination -hdiv + hs - C π * hck


omit [NumberField K] in
/-- If the reduction of `h` divides that of `G`, then `⟨π, G⟩ ⊆ ⟨π, h⟩`. -/
theorem span_pair_le_of_map_dvd {G h : (𝓞 K)[X]}
    (hdvd : h.map (Ideal.Quotient.mk (Ideal.span {π}))
      ∣ G.map (Ideal.Quotient.mk (Ideal.span {π}))) :
    (Ideal.span {C π, G} : Ideal ((𝓞 K)[X])) ≤ Ideal.span {C π, h} := by
  intro x hx
  rw [mem_span_pair_iff_map_dvd] at hx ⊢
  exact hdvd.trans hx

omit [NumberField K] in
/-- `⟨π, g⟩ ^ 2 ⊆ ⟨π, g ^ 2⟩`. -/
theorem sq_span_pair_le_span_pair_sq {g : (𝓞 K)[X]} :
    (Ideal.span {C π, g} : Ideal ((𝓞 K)[X])) ^ 2 ≤ Ideal.span {C π, g ^ 2} := by
  intro z hz
  obtain ⟨a, b, c, habc⟩ := Ideal.mem_span_pair_sq_iff.mp hz
  rw [mem_span_pair_iff_map_dvd]
  refine ⟨c.map (Ideal.Quotient.mk (Ideal.span {π})), ?_⟩
  rw [habc]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_C,
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self π), C_0, zero_mul,
    zero_pow two_ne_zero, zero_add]

/-- **Lemma 2.1 relatively**: `⟨π, g⟩ ^ 2 = ⟨π ^ 2, g⟩ ⊓ ⟨π, g ^ 2⟩`. -/
theorem span_pair_sq_eq_inf (hπ : Prime π) {g : (𝓞 K)[X]}
    (hg0 : g.map (Ideal.Quotient.mk (Ideal.span {π})) ≠ 0) :
    (Ideal.span {C π, g} : Ideal ((𝓞 K)[X])) ^ 2 =
      Ideal.span {C π ^ 2, g} ⊓ Ideal.span {C π, g ^ 2} := by
  haveI hmax : (Ideal.span {π} : Ideal (𝓞 K)).IsMaximal :=
    ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ).isMaximal
      (by simpa [Ideal.span_singleton_eq_bot] using hπ.ne_zero)
  refine le_antisymm (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨a, b, c, habc⟩ := Ideal.mem_span_pair_sq_iff.mp hz
    exact ⟨Ideal.mem_span_pair.mpr ⟨a, C π * b + g * c, by rw [habc]; ring⟩,
      Ideal.mem_span_pair.mpr ⟨C π * a + g * b, c, by rw [habc]; ring⟩⟩
  · obtain ⟨hz1, hz2⟩ := hz
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hz1
    obtain ⟨c, d, hcd⟩ := Ideal.mem_span_pair.mp hz2
    have hb : b ∈ (Ideal.span {C π, g} : Ideal ((𝓞 K)[X])) := by
      rw [mem_span_pair_iff_map_dvd]
      have h := congrArg (Polynomial.map (Ideal.Quotient.mk (Ideal.span {π})))
        (hab.trans hcd.symm)
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_C,
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self π), C_0,
        zero_pow two_ne_zero] at h
      refine Dvd.intro (d.map (Ideal.Quotient.mk (Ideal.span {π}))) ?_
      have hcancel : b.map (Ideal.Quotient.mk (Ideal.span {π})) =
          d.map (Ideal.Quotient.mk (Ideal.span {π})) *
            g.map (Ideal.Quotient.mk (Ideal.span {π})) :=
        mul_right_cancel₀ hg0 (by linear_combination h)
      linear_combination -hcancel
    obtain ⟨e', e, he⟩ := Ideal.mem_span_pair.mp hb
    exact Ideal.mem_span_pair_sq_iff.mpr ⟨a, e', e, by rw [← hab, ← he]; ring⟩

omit [NumberField K] in
/-- Membership in `⟨π ^ 2, X⟩` is divisibility of the constant term by `π ^ 2`. -/
theorem mem_span_pair_C_sq_X_iff {f : (𝓞 K)[X]} :
    f ∈ (Ideal.span {C π ^ 2, X} : Ideal ((𝓞 K)[X])) ↔ π ^ 2 ∣ f.coeff 0 := by
  constructor
  · rintro hf
    obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hf
    simp [coeff_zero_eq_eval_zero]
  · rintro ⟨c, hc⟩
    obtain ⟨q, hq⟩ : (X : (𝓞 K)[X]) ∣ f - C (f.coeff 0) := by
      rw [X_dvd_iff]; simp
    refine Ideal.mem_span_pair.mpr ⟨C c, q, ?_⟩
    have hCf : C (f.coeff 0) = C π ^ 2 * C c := by rw [hc, map_mul, map_pow]
    linear_combination -hq - hCf

/-- If `π ^ 2` does not divide the constant term, then `f` avoids `⟨π, X⟩ ^ 2`. -/
theorem notMem_sq_span_pair_X_of_sq_not_dvd_coeff_zero (hπ : Prime π) {f : (𝓞 K)[X]}
    (h : ¬ π ^ 2 ∣ f.coeff 0) :
    f ∉ (Ideal.span {C π, X} : Ideal ((𝓞 K)[X])) ^ 2 := by
  haveI hmax : (Ideal.span {π} : Ideal (𝓞 K)).IsMaximal :=
    ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ).isMaximal
      (by simpa [Ideal.span_singleton_eq_bot] using hπ.ne_zero)
  have hX0 : (X : (𝓞 K)[X]).map (Ideal.Quotient.mk (Ideal.span {π})) ≠ 0 := by
    rw [Polynomial.map_X]; exact X_ne_zero
  rw [span_pair_sq_eq_inf hπ hX0]
  exact fun hm => h (mem_span_pair_C_sq_X_iff.mp hm.1)



end Uchida



/-- **Uchida's criterion over a number field base, in the saturation form.**  `𝓞 K[θ]` fails
to be `π`-saturated in `𝓞 K₁` exactly when `π` is an index divisor of the minimal polynomial
of `θ`.

The forward direction is `NumberField.Relative.exists_splitting_of_not_saturated` followed by
the normalisation of the splitting into the shape of `IsIndexDivisor`; the backward direction
is the obstruction lemma. -/
theorem isIndexDivisor_iff_exists_notMem {π : 𝓞 K} (hπ : Prime π) :
    IsIndexDivisor π (minpoly (𝓞 K) θ) ↔
      ∃ β : 𝓞 K₁, algebraMap (𝓞 K) (𝓞 K₁) π * β ∈ Algebra.adjoin (𝓞 K) {θ} ∧
        β ∉ Algebra.adjoin (𝓞 K) {θ} := by
  constructor
  · rintro ⟨a, b, c, d, hm, hdeg, heq⟩
    obtain ⟨z, hz, hznot⟩ := exists_mul_mem_adjoin_notMem_adjoin_of_factor hπ hm hdeg heq
    exact ⟨z, hz, hznot⟩
  · rintro ⟨β, hβ, hβnot⟩
    obtain ⟨Pi, A, B, N, hPim, hPiirr, hsplit, hPiA, hPiB, hPiN⟩ :=
      exists_splitting_of_not_saturated hπ hβnot hβ
    have hPid : 0 < Pi.natDegree := by
      rcases Nat.eq_zero_or_pos Pi.natDegree with h0 | h
      · rw [eq_one_of_monic_natDegree_zero hPim h0] at hPiirr
        exact absurd hPiirr not_irreducible_one
      · exact h
    exact isIndexDivisor_of_splitting hπ (minpoly.monic (IsIntegral.tower_top θ.isIntegral))
      hPim hPid hsplit hPiA hPiB hPiN


/-! ### The Frobenius twist at a residue field that is not prime

Over `𝔽ₚ` one has `F(X ^ p) = F ^ p`, and Section 2 of Kaur–Kumar–Remete uses this
throughout.  Over a residue field `𝔽_q` with `q = p ^ s`, `s > 1`, it fails: the correct
identity is `F(X ^ p) = (F ^ σ⁻¹) ^ p`, where `σ` is the Frobenius `x ↦ x ^ p` acting on
coefficients (`Polynomial.map_frobenius_expand`).  Concretely, for `a ∈ 𝔽_{p ^ 2} ∖ 𝔽ₚ` the
polynomial `X - a` divides neither `X ^ p - a = (X - a)(X ^ p)`'s reduction nor, more to the
point, does the absolute lemma `Polynomial.expand_mem_span_pair` survive.

What does survive is the following exact statement, which shows the twist is a *bijection*
on the irreducible factors: `g` divides `F(X ^ p)` exactly when `g ^ σ` divides `F`.  Since
`σ` is an automorphism of a perfect field, `g ↦ g ^ σ` permutes the monic irreducibles, so
every statement that quantifies existentially over the witnessing prime — Lemma 2.6,
Corollary 2.5, and Theorem 1.1 itself — is unaffected; only results stated for a *fixed* `g`,
such as Theorem 2.4, acquire an explicit twist. -/

section FrobeniusTwist

variable {k : Type*} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] [PerfectRing k p]

/-- **The Frobenius twist.**  Over a perfect field of characteristic `p`, an irreducible `g`
divides `F(X ^ p)` if and only if its Frobenius twist `g ^ σ` divides `F`.

Over `𝔽ₚ` the twist is the identity and this is the familiar statement; over a larger
residue field it is not, and this is the precise correction needed in the relative case. -/
theorem dvd_expand_iff_map_frobenius_dvd {g F : k[X]} (hg : Irreducible g) :
    g ∣ Polynomial.expand k p F ↔ g.map (frobenius k p) ∣ F := by
  have hmapeq : ∀ q : k[X], (Polynomial.mapEquiv (frobeniusEquiv k p)) q
      = q.map (frobenius k p) := fun q => rfl
  have hexp : (Polynomial.mapEquiv (frobeniusEquiv k p)) (Polynomial.expand k p F) = F ^ p := by
    rw [hmapeq]
    exact Polynomial.map_frobenius_expand p F
  constructor
  · intro hdvd
    have h1 : (Polynomial.mapEquiv (frobeniusEquiv k p)) g ∣ F ^ p := by
      rw [← hexp]
      exact _root_.map_dvd (Polynomial.mapEquiv (frobeniusEquiv k p)) hdvd
    rw [hmapeq] at h1
    have hirr : Irreducible (g.map (frobenius k p)) := by
      rw [← hmapeq]
      exact (MulEquiv.irreducible_iff (Polynomial.mapEquiv (frobeniusEquiv k p)).toMulEquiv).mpr hg
    exact (irreducible_iff_prime.mp hirr).dvd_of_dvd_pow h1
  · intro hdvd
    have h1 : (Polynomial.mapEquiv (frobeniusEquiv k p)) (g ^ p) ∣
        (Polynomial.mapEquiv (frobeniusEquiv k p)) (Polynomial.expand k p F) := by
      rw [hexp, map_pow, hmapeq]
      exact pow_dvd_pow_of_dvd hdvd p
    have h2 : g ^ p ∣ Polynomial.expand k p F := by
      obtain ⟨c, hc⟩ := h1
      obtain ⟨c', rfl⟩ : ∃ c', (Polynomial.mapEquiv (frobeniusEquiv k p)) c' = c :=
        ⟨(Polynomial.mapEquiv (frobeniusEquiv k p)).symm c,
          (Polynomial.mapEquiv (frobeniusEquiv k p)).apply_symm_apply c⟩
      refine ⟨c', (Polynomial.mapEquiv (frobeniusEquiv k p)).injective ?_⟩
      rw [map_mul]
      exact hc
    exact (dvd_pow_self g (Fact.out : p.Prime).ne_zero).trans h2

/-- The Frobenius twist is a bijection on polynomials, so it permutes the monic irreducibles
of `k[X]`.  This is why every existentially quantified index-divisor statement survives
unchanged at a residue field that is not prime. -/
theorem map_frobenius_bijective : Function.Bijective (fun q : k[X] => q.map (frobenius k p)) :=
  (Polynomial.mapEquiv (frobeniusEquiv k p)).bijective

end FrobeniusTwist


/-! ### Necessity of the conditions of Theorem 1.1 over a number field base -/

/-- **Condition (3) of Theorem 1.1 is necessary over any number field base.**  If `θ` is a
root of `f(X ^ ℓ)` with `ℓ ≥ 2` and `𝓞 K[θ]` is the full ring of integers, then no square of
a prime of `𝓞 K` divides `f(0)`. -/
theorem adjoin_ne_top_of_sq_dvd_coeff_zero {π : 𝓞 K} (hπ : Prime π) {f : (𝓞 K)[X]}
    (hf : f.Monic) {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (hπ2 : π ^ 2 ∣ f.coeff 0)
    (hmin : minpoly (𝓞 K) θ = Polynomial.expand (𝓞 K) ℓ f) :
    Algebra.adjoin (𝓞 K) {θ} ≠ ⊤ :=
  adjoin_ne_top_of_isIndexDivisor hπ
    (hmin ▸ isIndexDivisor_expand_of_sq_dvd_coeff_zero hπ hf hℓ hπ2)

/-- **Condition (1) of Theorem 1.1 is necessary over any number field base.**  If `π` is an
index divisor of `f` and `θ` is a root of `f(X ^ ℓ)`, then `𝓞 K[θ]` is not the full ring of
integers. -/
theorem adjoin_ne_top_of_isIndexDivisor_expand {π : 𝓞 K} (hπ : Prime π) {f : (𝓞 K)[X]}
    {ℓ : ℕ} (hℓ : 0 < ℓ) (h : IsIndexDivisor π f)
    (hmin : minpoly (𝓞 K) θ = Polynomial.expand (𝓞 K) ℓ f) :
    Algebra.adjoin (𝓞 K) {θ} ≠ ⊤ :=
  adjoin_ne_top_of_isIndexDivisor hπ (hmin ▸ h.expand hℓ)

end NumberField.Relative
