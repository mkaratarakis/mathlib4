/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.Ideal.Basic
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

The global packaging no longer needs a hypothesis on the class number:
`NumberField.Relative.adjoin_eq_top_of_forall_maximal_saturated` factors the
denominator-clearing discriminant as an *ideal* rather than as an element, so the peeling is
carried out on maximal ideals, which always exist.  Assembling it with Uchida's criterion
gives `adjoin_eq_top_of_forall_maximal_exists_prime_not_isIndexDivisor` below.

That leaves one genuine obstacle:

* the notion `IsIndexDivisor` is attached to a prime *element* `π`, because both the
  obstruction and the certificate divide by it; at a maximal ideal `𝔭` that is not principal
  there is no such `π`, since a prime element of `𝔭` would generate it.  Verifying the
  hypothesis of the theorem below at a non-principal `𝔭` therefore means localising at `𝔭`,
  where the maximal ideal becomes principal, and that requires the local half of the
  development to be restated over an abstract Dedekind base.

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
def IsIndexDivisor {K : Type*} [Field K] (π : 𝓞 K) (f : (𝓞 K)[X]) : Prop :=
  ∃ h g k t : (𝓞 K)[X], (h * g).Monic ∧ (h * g).natDegree < f.natDegree ∧
    f = h ^ 2 * g + C π * (k * h) + C π ^ 2 * t

/-- An index divisor of the minimal polynomial obstructs monogenity. -/
theorem adjoin_ne_top_of_isIndexDivisor {π : 𝓞 K} (hπ : Prime π)
    (h : IsIndexDivisor π (minpoly (𝓞 K) θ)) :
    Algebra.adjoin (𝓞 K) {θ} ≠ ⊤ := by
  obtain ⟨a, b, c, d, hm, hdeg, heq⟩ := h
  exact adjoin_ne_top_of_sq_factor hπ hm hdeg heq

omit [NumberField K] in
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

omit [NumberField K] in
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

/-- Over a perfect field of characteristic `p`, the substitution `X ↦ X ^ (p ^ u)` lands in
`p ^ u`-th powers: `F(X ^ (p ^ u)) = A ^ (p ^ u)` for some `A`.

Over `𝔽ₚ` one may take `A = F`; in general `A` is the inverse iterated Frobenius twist. -/
theorem exists_pow_of_expand_pow (u : ℕ) (F : k[X]) :
    ∃ A : k[X], Polynomial.expand k (p ^ u) F = A ^ (p ^ u) := by
  refine ⟨(Polynomial.mapEquiv (iterateFrobeniusEquiv k p u)).symm F, ?_⟩
  refine (Polynomial.mapEquiv (iterateFrobeniusEquiv k p u)).injective ?_
  have h1 : (Polynomial.mapEquiv (iterateFrobeniusEquiv k p u))
      (Polynomial.expand k (p ^ u) F) = F ^ p ^ u :=
    Polynomial.map_iterateFrobenius_expand p F u
  rw [h1, map_pow, (Polynomial.mapEquiv (iterateFrobeniusEquiv k p u)).apply_symm_apply]


end FrobeniusTwist

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



/-- A monic nonconstant `G : (𝓞 K)[X]` admits a monic `h` whose reduction is an irreducible
factor of the reduction of `G`. -/
theorem exists_monic_map_irreducible_dvd (hπ : Prime π) {G : (𝓞 K)[X]} (hG : G.Monic)
    (hGd : 0 < G.natDegree) :
    ∃ h : (𝓞 K)[X], h.Monic ∧ Irreducible (h.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
      h.map (Ideal.Quotient.mk (Ideal.span {π})) ∣ G.map (Ideal.Quotient.mk (Ideal.span {π})) := by
  classical
  haveI hmax : (Ideal.span {π} : Ideal (𝓞 K)).IsMaximal :=
    ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ).isMaximal
      (by simpa [Ideal.span_singleton_eq_bot] using hπ.ne_zero)
  have hsurj : Function.Surjective (Ideal.Quotient.mk (Ideal.span {π} : Ideal (𝓞 K))) :=
    Ideal.Quotient.mk_surjective
  have hGm : (G.map (Ideal.Quotient.mk (Ideal.span {π}))).Monic := hG.map _
  have hGd' : 0 < (G.map (Ideal.Quotient.mk (Ideal.span {π}))).natDegree := by
    rwa [hG.natDegree_map]
  obtain ⟨π₀, hπ₀irr, hπ₀dvd⟩ := WfDvdMonoid.exists_irreducible_factor
    (not_isUnit_of_natDegree_pos _ hGd') hGm.ne_zero
  have hirr : Irreducible (normalize π₀) := (associated_normalize π₀).irreducible hπ₀irr
  obtain ⟨h, hhmap, -, hhmonic⟩ := lifts_and_degree_eq_and_monic
    ((mem_lifts (normalize π₀)).mpr (Polynomial.map_surjective _ hsurj _))
    (monic_normalize hπ₀irr.ne_zero)
  exact ⟨h, hhmonic, by rw [hhmap]; exact hirr,
    by rw [hhmap, normalize_dvd_iff]; exact hπ₀dvd⟩

/-- **Lemma 2.6 relatively, in ideal form.** -/
theorem exists_expand_mem_sq (hπ : Prime π) {f g : (𝓞 K)[X]} (hgm : g.Monic)
    (hgd : 0 < g.natDegree) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (hmem : f ∈ (Ideal.span {C π, g} : Ideal ((𝓞 K)[X])) ^ 2) :
    ∃ h : (𝓞 K)[X], h.Monic ∧ Irreducible (h.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
      Polynomial.expand (𝓞 K) ℓ f ∈ (Ideal.span {C π, h} : Ideal ((𝓞 K)[X])) ^ 2 := by
  have hEm : (Polynomial.expand (𝓞 K) ℓ g).Monic := hgm.expand hℓ
  have hEd : 0 < (Polynomial.expand (𝓞 K) ℓ g).natDegree := by
    rw [natDegree_expand]; positivity
  obtain ⟨h, hhm, hhirr, hhdvd⟩ := exists_monic_map_irreducible_dvd hπ hEm hEd
  refine ⟨h, hhm, hhirr, Ideal.pow_right_mono (span_pair_le_of_map_dvd hhdvd) 2 ?_⟩
  obtain ⟨u, v, w, huvw⟩ := Ideal.mem_span_pair_sq_iff.mp hmem
  refine Ideal.mem_span_pair_sq_iff.mpr ⟨Polynomial.expand (𝓞 K) ℓ u,
    Polynomial.expand (𝓞 K) ℓ v, Polynomial.expand (𝓞 K) ℓ w, ?_⟩
  rw [huvw]
  simp only [map_add, map_mul, map_pow, expand_C]

/-- **Proposition 2.3 relatively, in ideal form.** -/
theorem expand_mem_sq_of_sq_dvd_coeff_zero (hπ : Prime π) {f : (𝓞 K)[X]} {ℓ : ℕ} (hℓ : 2 ≤ ℓ)
    (hπ2 : π ^ 2 ∣ f.coeff 0) :
    Polynomial.expand (𝓞 K) ℓ f ∈ (Ideal.span {C π, X} : Ideal ((𝓞 K)[X])) ^ 2 := by
  have hℓ0 : 0 < ℓ := by omega
  haveI hmax : (Ideal.span {π} : Ideal (𝓞 K)).IsMaximal :=
    ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ).isMaximal
      (by simpa [Ideal.span_singleton_eq_bot] using hπ.ne_zero)
  have hX0 : (X : (𝓞 K)[X]).map (Ideal.Quotient.mk (Ideal.span {π})) ≠ 0 := by
    rw [Polynomial.map_X]; exact X_ne_zero
  rw [span_pair_sq_eq_inf hπ hX0, Ideal.mem_inf]
  constructor
  · refine mem_span_pair_C_sq_X_iff.mpr ?_
    rwa [coeff_expand hℓ0, if_pos (dvd_zero ℓ), Nat.zero_div]
  · rw [mem_span_pair_iff_map_dvd, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_expand, X_pow_dvd_iff]
    intro d hd
    rw [coeff_expand hℓ0]
    split_ifs with hdvd
    · interval_cases d
      · have : (f.map (Ideal.Quotient.mk (Ideal.span {π}))).coeff 0 = 0 := by
          rw [coeff_map, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
          exact (dvd_pow_self π two_ne_zero).trans hπ2
        simpa using this
      · exfalso
        have hl1 : ℓ = 1 := Nat.dvd_one.mp hdvd
        omega
    · rfl


omit [NumberField K] in
/-- Membership in `𝔪 ^ 2` depends only on the class modulo `𝔪 ^ 2`. -/
private theorem mem_sq_iff_of_sub_mem {I : Ideal ((𝓞 K)[X])} {x y : (𝓞 K)[X]}
    (h : x - y ∈ I ^ 2) : x ∈ I ^ 2 ↔ y ∈ I ^ 2 :=
  ⟨fun hx => (Submodule.sub_mem_iff_right _ hx).mp h,
    fun hy => (Submodule.sub_mem_iff_left _ hy).mp h⟩

/-- **Theorem 2.4 over a number field base**, with the Frobenius twist.  Let `gσ` be a monic
polynomial whose reduction is the Frobenius twist of that of `g`.  If `F ∈ ⟨π, gσ ^ 2⟩` then

    F ∈ ⟨π, gσ⟩ ^ 2  ↔  F(X ^ p) ∈ ⟨π, g⟩ ^ 2.

Over `𝔽ₚ` the twist is the identity and this is the paper's Theorem 2.4.  In general the two
sides pass through *different* primes of `(𝓞 K)[X]`, related by the Frobenius, which is
exactly the phenomenon isolated in `dvd_expand_iff_map_frobenius_dvd`.

The twisted statement is in fact easier than the absolute one: writing `F = π r + gσ ^ 2 q`,
both sides reduce by the cancellation lemma to the single divisibility
`gσ ∣ r` modulo `π`, and the two applications of the twist lemma are what identify them.
No integral Frobenius identity is needed, and the absolute proof's steps 3 and 4 disappear. -/
theorem mem_sq_span_iff_expand_mem_sq_span (hπ : Prime π) {p : ℕ} [Fact p.Prime]
    [CharP (𝓞 K ⧸ Ideal.span {π}) p] {g gσ : (𝓞 K)[X]}
    (hgirr : Irreducible (g.map (Ideal.Quotient.mk (Ideal.span {π}))))
    (hgσ0 : gσ.map (Ideal.Quotient.mk (Ideal.span {π})) ≠ 0)
    (htwist : gσ.map (Ideal.Quotient.mk (Ideal.span {π}))
      = (g.map (Ideal.Quotient.mk (Ideal.span {π}))).map (frobenius (𝓞 K ⧸ Ideal.span {π}) p))
    {F : (𝓞 K)[X]} (hF : F ∈ (Ideal.span {C π, gσ ^ 2} : Ideal ((𝓞 K)[X]))) :
    F ∈ (Ideal.span {C π, gσ} : Ideal ((𝓞 K)[X])) ^ 2 ↔
      Polynomial.expand (𝓞 K) p F ∈ (Ideal.span {C π, g} : Ideal ((𝓞 K)[X])) ^ 2 := by
  haveI hmax : (Ideal.span {π} : Ideal (𝓞 K)).IsMaximal :=
    ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ).isMaximal
      (by simpa [Ideal.span_singleton_eq_bot] using hπ.ne_zero)
  haveI : Finite (𝓞 K ⧸ Ideal.span {π}) := inferInstance
  haveI : PerfectField (𝓞 K ⧸ Ideal.span {π}) := PerfectField.ofFinite
  haveI : ExpChar (𝓞 K ⧸ Ideal.span {π}) p := ExpChar.prime Fact.out
  haveI : PerfectRing (𝓞 K ⧸ Ideal.span {π}) p := PerfectField.toPerfectRing p
  set mk := Ideal.Quotient.mk (Ideal.span {π} : Ideal (𝓞 K)) with hmk
  obtain ⟨r, q, hrq⟩ := Ideal.mem_span_pair.mp hF
  -- the left-hand side is `gσ ∣ r` mod `π`
  have hleft : F ∈ (Ideal.span {C π, gσ} : Ideal ((𝓞 K)[X])) ^ 2 ↔
      gσ.map mk ∣ r.map mk := by
    have hsub : F - C π * r ∈ (Ideal.span {C π, gσ} : Ideal ((𝓞 K)[X])) ^ 2 := by
      have heq : F - C π * r = gσ ^ 2 * q := by linear_combination -hrq
      rw [heq, sq, sq]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul (Ideal.subset_span (by simp))
        (Ideal.subset_span (by simp)))
    rw [mem_sq_iff_of_sub_mem hsub]
    exact ⟨fun h => mem_span_pair_iff_map_dvd.mp (mem_span_pair_of_C_mul_mem_sq hπ hgσ0 h),
      fun h => by
        obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp (mem_span_pair_iff_map_dvd.mpr h)
        refine Ideal.mem_span_pair_sq_iff.mpr ⟨a, b, 0, ?_⟩
        rw [← hab]; ring⟩
  -- the right-hand side is the same divisibility, after the twist
  have hexpσ : Polynomial.expand (𝓞 K) p gσ ∈ (Ideal.span {C π, g} : Ideal ((𝓞 K)[X])) := by
    rw [mem_span_pair_iff_map_dvd, Polynomial.map_expand, htwist,
      dvd_expand_iff_map_frobenius_dvd hgirr]
  have hright : Polynomial.expand (𝓞 K) p F ∈
      (Ideal.span {C π, g} : Ideal ((𝓞 K)[X])) ^ 2 ↔ gσ.map mk ∣ r.map mk := by
    have hsub : Polynomial.expand (𝓞 K) p F - C π * Polynomial.expand (𝓞 K) p r ∈
        (Ideal.span {C π, g} : Ideal ((𝓞 K)[X])) ^ 2 := by
      have heq : Polynomial.expand (𝓞 K) p F - C π * Polynomial.expand (𝓞 K) p r
          = (Polynomial.expand (𝓞 K) p gσ) ^ 2 * Polynomial.expand (𝓞 K) p q := by
        have hh := congrArg (Polynomial.expand (𝓞 K) p) hrq
        simp only [map_add, map_mul, map_pow, expand_C] at hh
        linear_combination -hh
      rw [heq, sq, sq]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul hexpσ hexpσ)
    rw [mem_sq_iff_of_sub_mem hsub]
    have hg0 : g.map mk ≠ 0 := hgirr.ne_zero
    constructor
    · intro h
      have h1 := mem_span_pair_iff_map_dvd.mp (mem_span_pair_of_C_mul_mem_sq hπ hg0 h)
      rw [Polynomial.map_expand, dvd_expand_iff_map_frobenius_dvd hgirr, ← htwist] at h1
      exact h1
    · intro h
      have h1 : g.map mk ∣ (Polynomial.expand (𝓞 K) p r).map mk := by
        rw [Polynomial.map_expand, dvd_expand_iff_map_frobenius_dvd hgirr, ← htwist]
        exact h
      obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp (mem_span_pair_iff_map_dvd.mpr h1)
      refine Ideal.mem_span_pair_sq_iff.mpr ⟨a, b, 0, ?_⟩
      rw [← hab]; ring
  rw [hleft, hright]


/-! ### Proposition 2.10 over a number field base -/

/-- **Proposition 2.10 over a number field base**, in ideal form.  Let `π` be a prime element
of `𝓞 K` whose residue field has characteristic `p`, and let `ℓ` be prime to `p`.  If
`f(X ^ ℓ)` lies in the square of a maximal ideal `⟨π, h⟩` of `(𝓞 K)[X]`, then either `f`
lies in the square of such an ideal, or `π ^ 2` divides `f(0)`.

The proof is the absolute one: split on whether the reduction of `h` is `X`; if not, the
prime of the residue polynomial ring lying below `h` along `X ↦ X ^ ℓ` gives a `G` whose
square divides the reduction of `f`, and lifting `G` and dividing `f = g q + r` produces the
required membership.  The residue field is no longer prime, but every lemma used has been
stated over an arbitrary perfect field of characteristic `p`, and the identity that fails
there — `f(X ^ p) = f ^ p` — is not used, since `p ∤ ℓ`. -/
theorem exists_mem_sq_or_sq_dvd_coeff_zero (hπ : Prime π) {p : ℕ}
    [CharP (𝓞 K ⧸ Ideal.span {π}) p] {f : (𝓞 K)[X]} (hfm : f.Monic) {ℓ : ℕ} (hℓ0 : 0 < ℓ)
    (hℓ : ¬ p ∣ ℓ) {h : (𝓞 K)[X]} (hhm : h.Monic)
    (hhirr : Irreducible (h.map (Ideal.Quotient.mk (Ideal.span {π}))))
    (hmem : Polynomial.expand (𝓞 K) ℓ f ∈
      (Ideal.span {C π, h} : Ideal ((𝓞 K)[X])) ^ 2) :
    (∃ g : (𝓞 K)[X], g.Monic ∧ Irreducible (g.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
      f ∈ (Ideal.span {C π, g} : Ideal ((𝓞 K)[X])) ^ 2) ∨ π ^ 2 ∣ f.coeff 0 := by
  classical
  haveI hmax : (Ideal.span {π} : Ideal (𝓞 K)).IsMaximal :=
    ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ).isMaximal
      (by simpa [Ideal.span_singleton_eq_bot] using hπ.ne_zero)
  haveI : Finite (𝓞 K ⧸ Ideal.span {π}) := inferInstance
  haveI : PerfectField (𝓞 K ⧸ Ideal.span {π}) := PerfectField.ofFinite
  set mk := Ideal.Quotient.mk (Ideal.span {π} : Ideal (𝓞 K)) with hmk
  have hsurj : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hhm' : (h.map mk).Monic := hhm.map _
  have hhd : 0 < (h.map mk).natDegree := by
    rcases Nat.eq_zero_or_pos (h.map mk).natDegree with h0 | hpos
    · rw [eq_one_of_monic_natDegree_zero hhm' h0] at hhirr
      exact absurd hhirr not_irreducible_one
    · exact hpos
  by_cases hX : h.map mk ∣ X
  · -- the reduction of `h` is `X`
    right
    by_contra hnot
    have hhX : h.map mk = X := by
      obtain ⟨w, hw⟩ := hX
      have hwm : w.Monic := hhm'.of_mul_monic_left (hw ▸ monic_X)
      have hdeg : (h.map mk).natDegree + w.natDegree = 1 := by
        have hd := congrArg natDegree hw
        rwa [natDegree_X, hhm'.natDegree_mul hwm, eq_comm] at hd
      rw [hw, eq_one_of_monic_natDegree_zero hwm (by omega), mul_one]
    have hle : (Ideal.span {C π, h} : Ideal ((𝓞 K)[X])) ≤ Ideal.span {C π, X} :=
      span_pair_le_of_map_dvd (by rw [Polynomial.map_X, hhX])
    refine notMem_sq_span_pair_X_of_sq_not_dvd_coeff_zero hπ
      (f := Polynomial.expand (𝓞 K) ℓ f) ?_ (Ideal.pow_right_mono hle 2 hmem)
    rwa [coeff_expand hℓ0, if_pos (dvd_zero ℓ), Nat.zero_div]
  · -- the reduction of `h` is not `X`
    left
    have hsq : (h.map mk) ^ 2 ∣ Polynomial.expand _ ℓ (f.map mk) := by
      have hm2 := sq_span_pair_le_span_pair_sq hmem
      rwa [mem_span_pair_iff_map_dvd, Polynomial.map_expand, Polynomial.map_pow] at hm2
    have hf0 : f.map mk ≠ 0 := (hfm.map _).ne_zero
    obtain ⟨G, hGm, hGirr, hGF, hhG⟩ :=
      exists_monic_irreducible_dvd_of_dvd_expand hf0 hhirr
        ((dvd_pow_self _ two_ne_zero).trans hsq)
    have hG2 : G ^ 2 ∣ f.map mk := sq_dvd_of_sq_dvd_expand (p := p) hℓ hGirr hGF hhirr hX hhG hsq
    obtain ⟨g, hgmap, -, hgmonic⟩ := lifts_and_degree_eq_and_monic
      ((mem_lifts G).mpr (Polynomial.map_surjective _ hsurj G)) hGm
    have hgdeg : 0 < g.natDegree := by
      rcases Nat.eq_zero_or_pos g.natDegree with h0 | hpos
      · rw [eq_one_of_monic_natDegree_zero hgmonic h0, Polynomial.map_one] at hgmap
        exact absurd (hgmap ▸ hGirr) not_irreducible_one
      · exact hpos
    have hgne1 : g ≠ 1 := fun h1 => by rw [h1] at hgdeg; simp at hgdeg
    have hgdegG : g.natDegree = G.natDegree := by rw [← hgmap, hgmonic.natDegree_map]
    refine ⟨g, hgmonic, by rw [hgmap]; exact hGirr, ?_⟩
    by_contra hnot
    set q := f /ₘ g with hqdef
    set r := f %ₘ g with hrdef
    have hdiv : r + g * q = f := modByMonic_add_div f g
    have hmapdiv : r.map mk + G * q.map mk = f.map mk := by
      have hd := congrArg (Polynomial.map mk) hdiv
      rwa [Polynomial.map_add, Polynomial.map_mul, hgmap] at hd
    have hrdeg : r.natDegree < G.natDegree := by
      have hlt : r.natDegree < g.natDegree := by
        rw [hrdef]; exact natDegree_modByMonic_lt f hgmonic hgne1
      omega
    have hrmap : r.map mk = 0 := by
      refine eq_zero_of_dvd_of_natDegree_lt ?_ (lt_of_le_of_lt natDegree_map_le hrdeg)
      have hreq : r.map mk = f.map mk - G * q.map mk := by linear_combination hmapdiv
      rw [hreq]
      exact dvd_sub hGF (dvd_mul_right G _)
    obtain ⟨s, hs⟩ : (C π : (𝓞 K)[X]) ∣ r := by
      rw [← map_quotient_span_eq_zero_iff]; exact hrmap
    have hGq : G ∣ q.map mk := by
      obtain ⟨m, hm⟩ := hG2
      have hcancel : G * q.map mk = G * (G * m) := by
        rw [← mul_assoc, ← sq, ← hm, ← hmapdiv, hrmap, zero_add]
      exact ⟨m, mul_left_cancel₀ hGirr.ne_zero hcancel⟩
    have hqmem : q ∈ (Ideal.span {C π, g} : Ideal ((𝓞 K)[X])) :=
      mem_span_pair_iff_map_dvd.mpr (by rw [hgmap]; exact hGq)
    have hgmem : g ∈ (Ideal.span {C π, g} : Ideal ((𝓞 K)[X])) := Ideal.subset_span (by simp)
    have hgq : g * q ∈ (Ideal.span {C π, g} : Ideal ((𝓞 K)[X])) ^ 2 := by
      rw [sq]; exact Ideal.mul_mem_mul hgmem hqmem
    have hCps : C π * s ∉ (Ideal.span {C π, g} : Ideal ((𝓞 K)[X])) ^ 2 := fun hcon =>
      hnot (by rw [← hdiv, hs]; exact Ideal.add_mem _ hcon hgq)
    have hsmap : s.map mk ≠ 0 := by
      intro h0
      obtain ⟨s', rfl⟩ : (C π : (𝓞 K)[X]) ∣ s := by
        rw [← map_quotient_span_eq_zero_iff]; exact h0
      refine hCps ?_
      have hsq2 : (Ideal.span {C π, g} : Ideal ((𝓞 K)[X])) ^ 2 =
          Ideal.span {C π, g} * Ideal.span {C π, g} := sq _
      have heq : C π * (C π * s') = C π * C π * s' := by ring
      rw [heq, hsq2]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul
        (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp)))
    have hrs : r.natDegree = s.natDegree := by
      rw [hs, natDegree_C_mul hπ.ne_zero]
    have hsdeg : (s.map mk).natDegree < G.natDegree :=
      lt_of_le_of_lt natDegree_map_le (by omega)
    have hGs : ¬ G ∣ s.map mk := fun hcon =>
      hsmap (eq_zero_of_dvd_of_natDegree_lt hcon hsdeg)
    have hcop : IsCoprime G (s.map mk) := (hGirr.coprime_iff_not_dvd).mpr hGs
    have hnhs : ¬ (h.map mk) ∣ Polynomial.expand _ ℓ (s.map mk) := fun hcon =>
      hhirr.not_isUnit ((hcop.map (Polynomial.expand _ ℓ).toRingHom).isUnit_of_dvd' hhG hcon)
    apply hnhs
    have hEg : Polynomial.expand (𝓞 K) ℓ g ∈ (Ideal.span {C π, h} : Ideal ((𝓞 K)[X])) :=
      mem_span_pair_iff_map_dvd.mpr (by rw [Polynomial.map_expand, hgmap]; exact hhG)
    have hEq : Polynomial.expand (𝓞 K) ℓ q ∈ (Ideal.span {C π, h} : Ideal ((𝓞 K)[X])) :=
      mem_span_pair_iff_map_dvd.mpr (by
        rw [Polynomial.map_expand]
        exact hhG.trans (map_dvd (Polynomial.expand _ ℓ) hGq))
    have hprod : Polynomial.expand (𝓞 K) ℓ g * Polynomial.expand (𝓞 K) ℓ q ∈
        (Ideal.span {C π, h} : Ideal ((𝓞 K)[X])) ^ 2 := by
      rw [sq]; exact Ideal.mul_mem_mul hEg hEq
    have hEs : C π * Polynomial.expand (𝓞 K) ℓ s ∈
        (Ideal.span {C π, h} : Ideal ((𝓞 K)[X])) ^ 2 := by
      have hexpand : Polynomial.expand (𝓞 K) ℓ f = C π * Polynomial.expand (𝓞 K) ℓ s +
          Polynomial.expand (𝓞 K) ℓ g * Polynomial.expand (𝓞 K) ℓ q := by
        rw [← hdiv, hs, map_add, map_mul, map_mul, expand_C]
      have hd := Ideal.sub_mem _ hmem hprod
      rwa [hexpand, add_sub_cancel_right] at hd
    have hfin := mem_span_pair_of_C_mul_mem_sq hπ hhm'.ne_zero hEs
    rw [mem_span_pair_iff_map_dvd, Polynomial.map_expand] at hfin
    exact hfin


/-- **The relative criterion at a prime not dividing `k`.**  Let `π` be a prime element of
`𝓞 K` whose residue field has characteristic `p`, and let `k ≥ 2` be prime to `p`.  Then `π`
is an index divisor of `f(X ^ k)` if and only if it is an index divisor of `f`, or
`π ^ 2` divides `f(0)`.

This is Theorem 1.1 of Kaur–Kumar–Remete, at the primes prime to `k`, over an arbitrary
number field base.  Combined with
`NumberField.Relative.isIndexDivisor_iff_exists_notMem` it decides `π`-saturation, and hence
— via `NumberField.Relative.adjoin_eq_top_of_forall_maximal_saturated` — contributes the
corresponding condition to relative monogenity. -/
theorem exists_expand_mem_sq_iff (hπ : Prime π) {p : ℕ}
    [CharP (𝓞 K ⧸ Ideal.span {π}) p] {f : (𝓞 K)[X]} (hfm : f.Monic) {k : ℕ} (hk : 2 ≤ k)
    (hpk : ¬ p ∣ k) :
    (∃ h : (𝓞 K)[X], h.Monic ∧ Irreducible (h.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
        Polynomial.expand (𝓞 K) k f ∈ (Ideal.span {C π, h} : Ideal ((𝓞 K)[X])) ^ 2) ↔
      (∃ g : (𝓞 K)[X], g.Monic ∧ Irreducible (g.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
        f ∈ (Ideal.span {C π, g} : Ideal ((𝓞 K)[X])) ^ 2) ∨ π ^ 2 ∣ f.coeff 0 := by
  haveI hmax : (Ideal.span {π} : Ideal (𝓞 K)).IsMaximal :=
    ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ).isMaximal
      (by simpa [Ideal.span_singleton_eq_bot] using hπ.ne_zero)
  constructor
  · rintro ⟨h, hhm, hhirr, hmem⟩
    exact exists_mem_sq_or_sq_dvd_coeff_zero hπ hfm (by omega) hpk hhm hhirr hmem
  · rintro (⟨g, hgm, hgirr, hmem⟩ | h2)
    · have hgd : 0 < g.natDegree := by
        rcases Nat.eq_zero_or_pos g.natDegree with h0 | hpos
        · rw [eq_one_of_monic_natDegree_zero hgm h0, Polynomial.map_one] at hgirr
          exact absurd hgirr not_irreducible_one
        · exact hpos
      exact exists_expand_mem_sq hπ hgm hgd (by omega) hmem
    · exact ⟨X, monic_X, by rw [Polynomial.map_X]; exact irreducible_X,
        expand_mem_sq_of_sq_dvd_coeff_zero hπ hk h2⟩



/-! ### Corollary 2.5 over a number field base -/

/-- One descent step: if `π` is an index divisor of `f(X ^ (p ^ (u+1)))` then it is one of
`f(X ^ (p ^ u))`, for `u ≥ 1`.

By Theorem 2.4 twisted, applied to `F = f(X ^ (p ^ u))`: the witness `h` for `F(X ^ p)`
produces the twisted witness `gσ` for `F`.  The hypothesis `F ∈ ⟨π, gσ ^ 2⟩` that Theorem 2.4
needs holds because `F` is itself an expansion, hence a `p ^ u`-th power modulo `π`, and
`p ^ u ≥ 2`. -/
theorem exists_expand_pow_mem_sq_of_succ (hπ : Prime π) {p : ℕ} [Fact p.Prime]
    [CharP (𝓞 K ⧸ Ideal.span {π}) p] {f : (𝓞 K)[X]} {u : ℕ} (hu : 0 < u)
    {h : (𝓞 K)[X]} (hhm : h.Monic)
    (hhirr : Irreducible (h.map (Ideal.Quotient.mk (Ideal.span {π}))))
    (hmem : Polynomial.expand (𝓞 K) (p ^ (u + 1)) f ∈
      (Ideal.span {C π, h} : Ideal ((𝓞 K)[X])) ^ 2) :
    ∃ g : (𝓞 K)[X], g.Monic ∧ Irreducible (g.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
      Polynomial.expand (𝓞 K) (p ^ u) f ∈ (Ideal.span {C π, g} : Ideal ((𝓞 K)[X])) ^ 2 := by
  classical
  haveI hmax : (Ideal.span {π} : Ideal (𝓞 K)).IsMaximal :=
    ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ).isMaximal
      (by simpa [Ideal.span_singleton_eq_bot] using hπ.ne_zero)
  haveI : Finite (𝓞 K ⧸ Ideal.span {π}) := inferInstance
  haveI : PerfectField (𝓞 K ⧸ Ideal.span {π}) := PerfectField.ofFinite
  haveI : ExpChar (𝓞 K ⧸ Ideal.span {π}) p := ExpChar.prime Fact.out
  haveI : PerfectRing (𝓞 K ⧸ Ideal.span {π}) p := PerfectField.toPerfectRing p
  set mk := Ideal.Quotient.mk (Ideal.span {π} : Ideal (𝓞 K)) with hmk
  set F := Polynomial.expand (𝓞 K) (p ^ u) f with hFdef
  have hexp : Polynomial.expand (𝓞 K) p F = Polynomial.expand (𝓞 K) (p ^ (u + 1)) f := by
    rw [hFdef, expand_expand, ← pow_succ']
  -- the twisted witness
  obtain ⟨gσ, hgσmap, -, hgσm⟩ := lifts_and_degree_eq_and_monic
    ((mem_lifts ((h.map mk).map (frobenius (𝓞 K ⧸ Ideal.span {π}) p))).mpr
      (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective _))
    (((hhm.map mk).map (frobenius (𝓞 K ⧸ Ideal.span {π}) p)))
  have hgσirr : Irreducible (gσ.map mk) := by
    rw [hgσmap]
    exact (MulEquiv.irreducible_iff
      (Polynomial.mapEquiv (frobeniusEquiv (𝓞 K ⧸ Ideal.span {π}) p)).toMulEquiv).mpr hhirr
  -- the square hypothesis for Theorem 2.4
  have hdvd1 : gσ.map mk ∣ F.map mk := by
    have h1 : (h.map mk) ∣ (Polynomial.expand (𝓞 K) p F).map mk := by
      have h2 := sq_span_pair_le_span_pair_sq (hexp ▸ hmem)
      rw [mem_span_pair_iff_map_dvd, Polynomial.map_pow] at h2
      exact (dvd_pow_self _ two_ne_zero).trans h2
    rw [Polynomial.map_expand, dvd_expand_iff_map_frobenius_dvd hhirr] at h1
    rwa [hgσmap]
  have hsq : F ∈ (Ideal.span {C π, gσ ^ 2} : Ideal ((𝓞 K)[X])) := by
    obtain ⟨A, hA⟩ := exists_pow_of_expand_pow (k := 𝓞 K ⧸ Ideal.span {π}) (p := p) u (f.map mk)
    have hFmap : F.map mk = A ^ p ^ u := by rw [hFdef, Polynomial.map_expand, hA]
    have hgA : gσ.map mk ∣ A := by
      refine (irreducible_iff_prime.mp hgσirr).dvd_of_dvd_pow (n := p ^ u) ?_
      rwa [← hFmap]
    have hle : 2 ≤ p ^ u := by
      calc 2 ≤ p := (Fact.out : p.Prime).two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ u := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hu
    rw [mem_span_pair_iff_map_dvd, Polynomial.map_pow, hFmap]
    exact (pow_dvd_pow _ hle).trans (pow_dvd_pow_of_dvd hgA _)
  refine ⟨gσ, hgσm, hgσirr, ?_⟩
  rw [mem_sq_span_iff_expand_mem_sq_span hπ hhirr hgσirr.ne_zero (by rw [hgσmap]) hsq]
  exact hexp ▸ hmem

/-- Descending the exponent: an index divisor of `f(X ^ (p ^ u))` is one of `f(X ^ p)`,
for every `u ≥ 1`.  Iterating `exists_expand_pow_mem_sq_of_succ`. -/
theorem exists_expand_pow_mem_sq_descend (hπ : Prime π) {p : ℕ} [Fact p.Prime]
    [CharP (𝓞 K ⧸ Ideal.span {π}) p] {f : (𝓞 K)[X]} :
    ∀ u : ℕ, 0 < u →
      (∃ h : (𝓞 K)[X], h.Monic ∧ Irreducible (h.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
        Polynomial.expand (𝓞 K) (p ^ u) f ∈ (Ideal.span {C π, h} : Ideal ((𝓞 K)[X])) ^ 2) →
      (∃ h : (𝓞 K)[X], h.Monic ∧ Irreducible (h.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
        Polynomial.expand (𝓞 K) p f ∈ (Ideal.span {C π, h} : Ideal ((𝓞 K)[X])) ^ 2) := by
  intro u
  induction u with
  | zero => intro hu; omega
  | succ n ih =>
    rintro - ⟨h, hhm, hhirr, hmem⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨h, hhm, hhirr, by simpa using hmem⟩
    · obtain ⟨g, hgm, hgirr, hgmem⟩ := exists_expand_pow_mem_sq_of_succ hπ hn hhm hhirr hmem
      exact ih hn ⟨g, hgm, hgirr, hgmem⟩

/-- **Corollary 2.5 over a number field base.**  For `u ≥ 1`, the prime `π` is an index
divisor of `f(X ^ p)` if and only if it is one of `f(X ^ (p ^ u))`.

So the criterion cannot see the exponent of `p`, exactly as in the absolute case — the
Frobenius twist permutes the witnessing primes at each step but does not affect the
existential statement. -/
theorem exists_expand_pow_mem_sq_iff (hπ : Prime π) {p : ℕ} [Fact p.Prime]
    [CharP (𝓞 K ⧸ Ideal.span {π}) p] {f : (𝓞 K)[X]} {u : ℕ} (hu : 0 < u) :
    (∃ h : (𝓞 K)[X], h.Monic ∧ Irreducible (h.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
        Polynomial.expand (𝓞 K) p f ∈ (Ideal.span {C π, h} : Ideal ((𝓞 K)[X])) ^ 2) ↔
      (∃ h : (𝓞 K)[X], h.Monic ∧ Irreducible (h.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
        Polynomial.expand (𝓞 K) (p ^ u) f ∈ (Ideal.span {C π, h} : Ideal ((𝓞 K)[X])) ^ 2) := by
  constructor
  · rintro ⟨h, hhm, hhirr, hmem⟩
    have hgd : 0 < h.natDegree := by
      rcases Nat.eq_zero_or_pos h.natDegree with h0 | hpos
      · rw [eq_one_of_monic_natDegree_zero hhm h0, Polynomial.map_one] at hhirr
        exact absurd hhirr not_irreducible_one
      · exact hpos
    obtain ⟨h', hh'm, hh'irr, hmem'⟩ :=
      exists_expand_mem_sq (ℓ := p ^ (u - 1)) hπ hhm hgd (pow_pos (Fact.out : p.Prime).pos _) hmem
    refine ⟨h', hh'm, hh'irr, ?_⟩
    rwa [expand_expand, ← pow_succ, Nat.sub_add_cancel hu] at hmem'
  · exact exists_expand_pow_mem_sq_descend hπ u hu




/-! ### Theorem 1.1 over a number field base -/

/-- **Theorem 1.1 of Kaur–Kumar–Remete over a number field base, prime by prime.**  Let `π`
be a prime element of `𝓞 K` whose residue field has characteristic `p`, and let `k ≥ 2`.
Then `π` is an index divisor of `f(X ^ k)` if and only if

* `π` is an index divisor of `f(X ^ p)`, when `p ∣ k`, or of `f` itself, when `p ∤ k`;
* or `π ^ 2` divides `f(0)`.

Writing `k = p ^ u * m` with `p ∤ m`, Corollary 2.5 contracts `p ^ u` to `p` and
Proposition 2.10 strips `m`, exactly as in the absolute case; the Frobenius twist that
appears at each contraction is invisible here because the statement quantifies over the
witnessing prime. -/
theorem exists_expand_mem_sq_iff_of_dvd (hπ : Prime π) {p : ℕ} [Fact p.Prime]
    [CharP (𝓞 K ⧸ Ideal.span {π}) p] {f : (𝓞 K)[X]} (hfm : f.Monic) {k : ℕ} (hk : 2 ≤ k)
    (hpk : p ∣ k) :
    (∃ h : (𝓞 K)[X], h.Monic ∧ Irreducible (h.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
        Polynomial.expand (𝓞 K) k f ∈ (Ideal.span {C π, h} : Ideal ((𝓞 K)[X])) ^ 2) ↔
      (∃ h : (𝓞 K)[X], h.Monic ∧ Irreducible (h.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
        Polynomial.expand (𝓞 K) p f ∈ (Ideal.span {C π, h} : Ideal ((𝓞 K)[X])) ^ 2) ∨
      π ^ 2 ∣ f.coeff 0 := by
  haveI hmax : (Ideal.span {π} : Ideal (𝓞 K)).IsMaximal :=
    ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ).isMaximal
      (by simpa [Ideal.span_singleton_eq_bot] using hπ.ne_zero)
  have hppos : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨u, m, hm, hkeq⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (n := k) (by omega) p (Fact.out : p.Prime).ne_one
  have hu : 0 < u := by
    rcases Nat.eq_zero_or_pos u with rfl | h
    · rw [pow_zero, one_mul] at hkeq; exact absurd (hkeq ▸ hpk) hm
    · exact h
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · rw [mul_zero] at hkeq; omega
    · exact h
  have hcoeff : (Polynomial.expand (𝓞 K) (p ^ u) f).coeff 0 = f.coeff 0 := by
    rw [coeff_expand (pow_pos hppos u), if_pos (dvd_zero _), Nat.zero_div]
  rcases eq_or_lt_of_le (show 1 ≤ m from hm0) with hm1 | hm2
  · -- `k = p ^ u`
    have hkpu : k = p ^ u := by rw [hkeq, ← hm1, mul_one]
    subst hkpu
    refine ⟨fun h => Or.inl ((exists_expand_pow_mem_sq_iff hπ hu).mpr h), ?_⟩
    rintro (h | h)
    · exact (exists_expand_pow_mem_sq_iff hπ hu).mp h
    · exact ⟨X, monic_X, by rw [Polynomial.map_X]; exact irreducible_X,
        expand_mem_sq_of_sq_dvd_coeff_zero hπ hk h⟩
  · -- `k = p ^ u * m` with `m ≥ 2`: strip `m` by Proposition 2.10
    have hexp : Polynomial.expand (𝓞 K) m (Polynomial.expand (𝓞 K) (p ^ u) f)
        = Polynomial.expand (𝓞 K) k f := by
      rw [expand_expand, hkeq, mul_comm]
    have h210 := exists_expand_mem_sq_iff (π := π) hπ (hfm.expand (pow_pos hppos u)) hm2 hm
    rw [hexp, hcoeff] at h210
    rw [h210]
    constructor
    · rintro (h | h)
      · exact Or.inl ((exists_expand_pow_mem_sq_iff hπ hu).mpr h)
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl ((exists_expand_pow_mem_sq_iff hπ hu).mp h)
      · exact Or.inr h



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

/-- **Problem 2, the global step, with no class number hypothesis.**  If at every maximal
ideal `𝔭` of `𝓞 K` some prime element lying in `𝔭` fails to be an index divisor of the
minimal polynomial of `θ`, then `𝓞 K[θ] = 𝓞 K₁`.

This assembles Uchida's criterion over a number field base
(`isIndexDivisor_iff_exists_notMem`) with the ideal-theoretic global packaging
(`adjoin_eq_top_of_forall_maximal_saturated`): the latter factors the denominator-clearing
discriminant as an ideal rather than as an element, so no hypothesis on the class number of
`K` is needed.  Note that a prime element lying in `𝔭` generates it, so the hypothesis can
only be met at principal `𝔭`; at the remaining maximal ideals one has to localise. -/
theorem adjoin_eq_top_of_forall_maximal_exists_prime_not_isIndexDivisor
    (hgen : Algebra.adjoin K {algebraMap (𝓞 K₁) K₁ θ} = ⊤)
    (h : ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsMaximal → ∃ π : 𝓞 K, Prime π ∧ π ∈ 𝔭 ∧
      ¬ IsIndexDivisor π (minpoly (𝓞 K) θ)) :
    Algebra.adjoin (𝓞 K) {θ} = ⊤ := by
  refine adjoin_eq_top_of_forall_maximal_saturated hgen fun 𝔭 h𝔭 y hy => ?_
  obtain ⟨π, hπ, hπ𝔭, hnid⟩ := h 𝔭 h𝔭
  by_contra hynot
  exact hnid ((isIndexDivisor_iff_exists_notMem hπ).mpr ⟨y, hy π hπ𝔭, hynot⟩)

/-- The two forms of "index divisor" agree: the decomposition form used by the obstruction
lemma, and the ideal form `f ∈ ⟨π, h⟩ ^ 2` used throughout Section 2. -/
theorem isIndexDivisor_iff_exists_mem_sq {π : 𝓞 K} (hπ : Prime π) :
    IsIndexDivisor π (minpoly (𝓞 K) θ) ↔
      ∃ h : (𝓞 K)[X], h.Monic ∧ Irreducible (h.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
        minpoly (𝓞 K) θ ∈ (Ideal.span {C π, h} : Ideal ((𝓞 K)[X])) ^ 2 := by
  haveI hmax : (Ideal.span {π} : Ideal (𝓞 K)).IsMaximal :=
    ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ).isMaximal
      (by simpa [Ideal.span_singleton_eq_bot] using hπ.ne_zero)
  constructor
  · intro hid
    obtain ⟨β, hβ, hβnot⟩ := (isIndexDivisor_iff_exists_notMem hπ).mp hid
    obtain ⟨Pi, A, B, N, hPim, hPiirr, hsplit, hPiA, hPiB, hPiN⟩ :=
      exists_splitting_of_not_saturated hπ hβnot hβ
    obtain ⟨P, hPmap, -, hPm⟩ := lifts_and_degree_eq_and_monic
      ((mem_lifts Pi).mpr (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective Pi)) hPim
    refine ⟨P, hPm, by rw [hPmap]; exact hPiirr, ?_⟩
    rw [hsplit, sq]
    exact Ideal.add_mem _
      (Ideal.mul_mem_mul (mem_span_pair_iff_map_dvd.mpr (hPmap ▸ hPiA))
        (mem_span_pair_iff_map_dvd.mpr (hPmap ▸ hPiB)))
      (Ideal.mul_mem_mul (Ideal.subset_span (by simp))
        (mem_span_pair_iff_map_dvd.mpr (hPmap ▸ hPiN)))
  · rintro ⟨h, hhm, hhirr, hmem⟩
    have hhd : 0 < h.natDegree := by
      rcases Nat.eq_zero_or_pos h.natDegree with h0 | hpos
      · rw [eq_one_of_monic_natDegree_zero hhm h0, Polynomial.map_one] at hhirr
        exact absurd hhirr not_irreducible_one
      · exact hpos
    obtain ⟨u, v, w, huvw⟩ := Ideal.mem_span_pair_sq_iff.mp hmem
    refine isIndexDivisor_of_splitting hπ (minpoly.monic (IsIntegral.tower_top θ.isIntegral))
      (Pi := h.map (Ideal.Quotient.mk (Ideal.span {π}))) (hhm.map _) (by rwa [hhm.natDegree_map])
      (A := h) (B := h * w) (N := C π * u + h * v) ?_ dvd_rfl ?_ ?_
    · rw [huvw]; ring
    · rw [Polynomial.map_mul]; exact dvd_mul_right _ _
    · rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, map_C,
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self π), C_0, zero_mul,
        zero_add]
      exact dvd_mul_right _ _

/-- **Theorem 1.1 of Kaur–Kumar–Remete over a number field base.**  Let `f` be monic over
`𝓞 K`, let `k ≥ 2`, and let `ω` be a root of `f(X ^ k)` generating `K₁` over `K`.  If at every
maximal ideal `𝔭` of `𝓞 K` there is a prime element `π ∈ 𝔭`, with residue characteristic `p`,
such that

* `π ^ 2` does not divide `f(0)`, and
* `π` is not an index divisor of `f(X ^ p)` when `p ∣ k`, and not one of `f` when `p ∤ k`,

then `𝓞 K[ω] = 𝓞 K₁`.

This is the relative form of Theorem 1.1.  The conditions are exactly the paper's (1), (2)
and (3), read at each prime: monogenity of `f`, no index divisor of `f(X ^ p)` for `p ∣ k`,
and squarefreeness of `f(0)`.  As in
`adjoin_eq_top_of_forall_maximal_exists_prime_not_isIndexDivisor`, the hypothesis can only be
met at principal maximal ideals, so this is a statement about bases of class number one until
the local certificate is available at a non-principal `𝔭`. -/
theorem adjoin_eq_top_of_forall_maximal_expand (hπgen : Algebra.adjoin K
      {algebraMap (𝓞 K₁) K₁ θ} = ⊤) {f : (𝓞 K)[X]} (hfm : f.Monic) {k : ℕ} (hk : 2 ≤ k)
    (hmin : minpoly (𝓞 K) θ = Polynomial.expand (𝓞 K) k f)
    (h : ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsMaximal → ∃ (π : 𝓞 K) (p : ℕ) (_ : Fact p.Prime)
      (_ : CharP (𝓞 K ⧸ Ideal.span {π}) p), Prime π ∧ π ∈ 𝔭 ∧ ¬ π ^ 2 ∣ f.coeff 0 ∧
      ¬ ∃ g : (𝓞 K)[X], g.Monic ∧
        Irreducible (g.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
        Polynomial.expand (𝓞 K) (if p ∣ k then p else 1) f ∈
          (Ideal.span {C π, g} : Ideal ((𝓞 K)[X])) ^ 2) :
    Algebra.adjoin (𝓞 K) {θ} = ⊤ := by
  refine adjoin_eq_top_of_forall_maximal_exists_prime_not_isIndexDivisor hπgen fun 𝔭 h𝔭 => ?_
  obtain ⟨π, p, hp, hchar, hπ, hπ𝔭, hcoeff, hnid⟩ := h 𝔭 h𝔭
  refine ⟨π, hπ, hπ𝔭, ?_⟩
  rw [isIndexDivisor_iff_exists_mem_sq hπ, hmin]
  intro hcon
  refine hnid ?_
  by_cases hpk : p ∣ k
  · rw [if_pos hpk]
    exact ((exists_expand_mem_sq_iff_of_dvd hπ hfm hk hpk).mp hcon).resolve_right hcoeff
  · rw [if_neg hpk, expand_one]
    exact ((exists_expand_mem_sq_iff hπ hfm hk hpk).mp hcon).resolve_right hcoeff



end NumberField.Relative
