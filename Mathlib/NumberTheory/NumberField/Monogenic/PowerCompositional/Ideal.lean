/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.ZMod

/-!
# The ideal calculus of power-compositional polynomials

This file develops the commutative-algebra core of S. Kaur, S. Kumar and L. Remete,
*On the index of power compositional polynomials*,
Finite Fields Appl. **107** (2025), 102642, Section 2.  Everything proved here is a
statement about ideals of `ℤ[X]`; no number theory is involved.

Fix a prime `p` and a monic `g : ℤ[X]` whose reduction mod `p` is irreducible, and
write `𝔪 = ⟨p, g⟩` for the associated maximal ideal of `ℤ[X]`.  By Uchida's theorem a
rational prime `p` divides the index `[𝓞 K : ℤ[θ]]` precisely when the minimal polynomial
of `θ` lies in `𝔪 ^ 2` for some such `𝔪`, so the membership `f ∈ 𝔪 ^ 2` is the object of
interest throughout.

## Main results

* `Polynomial.C_natCast_dvd_expand_sub_pow`: the integral Frobenius identity
  `p ∣ g(Xᵖ) - g(X)ᵖ` in `ℤ[X]`.  Mathlib has the characteristic-`p` statement
  `Polynomial.map_frobenius_expand`, but not this integral form.

* `Ideal.mem_span_pair_sq_iff`: elementwise description of `⟨a, b⟩ ^ 2` in a commutative
  ring, namely `x = a ^ 2 * u + a * b * v + b ^ 2 * w`.  In the case `⟨p, g⟩ ^ 2` this is
  exactly the shape of the hypothesis of
  `RingOfIntegers.dvd_exponent_of_sq_factor`.

* `Polynomial.mem_sq_span_iff_expand_mem_sq_span`: **Theorem 2.4** of the paper.  If
  `f ∈ ⟨p, g ^ 2⟩` then `f ∈ ⟨p, g⟩ ^ 2 ↔ f(Xᵖ) ∈ ⟨p, g⟩ ^ 2`.  This is the result that
  makes the monogenicity of `f(X ^ k)` independent of the exponents of the primes in the
  factorisation of `k`, and the authors single it out as being of independent interest.

## Implementation notes

The paper's proof of Theorem 2.4 first divides the cofactor `r` by `g` so as to arrange
`deg t < deg g`.  That step is not needed.  The argument uses only `g ^ 2 ∈ 𝔪 ^ 2` and
`p * g ∈ 𝔪 ^ 2`, so one may take the remainder to be `r` itself; we therefore work
directly with the decomposition `f = g ^ 2 * q + p * r` supplied by the hypothesis
`f ∈ ⟨p, g ^ 2⟩`.  The degree hypothesis reappears only in Proposition 2.10, where it is
genuinely used.

## References

* [S. Kaur, S. Kumar, L. Remete, *On the index of power compositional polynomials*][KKR2025]
* [K. Uchida, *When is `ℤ[θ]` the ring of integers?*][Uchida1977]
-/

@[expose] public section

noncomputable section

open Polynomial

namespace Ideal

variable {R : Type*} [CommRing R] {a b x : R}

/-- Elementwise description of the square of a two-generated ideal:
`⟨a, b⟩ ^ 2 = ⟨a ^ 2, a * b, b ^ 2⟩`. -/
theorem mem_span_pair_sq_iff :
    x ∈ (Ideal.span {a, b} : Ideal R) ^ 2 ↔
      ∃ u v w : R, x = a ^ 2 * u + a * b * v + b ^ 2 * w := by
  have ha : a ∈ (Ideal.span {a, b} : Ideal R) := subset_span (by simp)
  have hb : b ∈ (Ideal.span {a, b} : Ideal R) := subset_span (by simp)
  rw [sq]
  constructor
  · refine fun hx => Submodule.mul_induction_on hx (fun m hm n hn => ?_) ?_
    · obtain ⟨c, d, rfl⟩ := mem_span_pair.mp hm
      obtain ⟨e, f, rfl⟩ := mem_span_pair.mp hn
      exact ⟨c * e, c * f + d * e, d * f, by ring⟩
    · rintro _ _ ⟨u₁, v₁, w₁, rfl⟩ ⟨u₂, v₂, w₂, rfl⟩
      exact ⟨u₁ + u₂, v₁ + v₂, w₁ + w₂, by ring⟩
  · rintro ⟨u, v, w, rfl⟩
    refine add_mem (add_mem ?_ ?_) ?_
    · exact Ideal.mul_mem_right _ _ (sq a ▸ Ideal.mul_mem_mul ha ha)
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul ha hb)
    · exact Ideal.mul_mem_right _ _ (sq b ▸ Ideal.mul_mem_mul hb hb)

end Ideal

namespace Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

/-- Univariate analogue of `MvPolynomial.C_dvd_iff_map_hom_eq_zero`. -/
theorem C_dvd_iff_map_hom_eq_zero {R S : Type*} [CommSemiring R] [Semiring S] (q : R →+* S)
    (r : R) (hr : ∀ r' : R, q r' = 0 ↔ r ∣ r') (φ : R[X]) : C r ∣ φ ↔ φ.map q = 0 := by
  rw [C_dvd_iff_dvd_coeff, Polynomial.ext_iff]
  simp [hr]

/-- Univariate analogue of `MvPolynomial.C_dvd_iff_zmod`: a polynomial over `ℤ` is
divisible by the constant polynomial `n` exactly when it reduces to `0` mod `n`. -/
theorem C_dvd_iff_zmod (n : ℕ) (φ : ℤ[X]) :
    C (n : ℤ) ∣ φ ↔ φ.map (Int.castRingHom (ZMod n)) = 0 :=
  C_dvd_iff_map_hom_eq_zero _ _ (fun r => ZMod.intCast_zmod_eq_zero_iff_dvd r n) _

/-- **The integral Frobenius identity.**  In `ℤ[X]` the constant polynomial `p` divides
`g(Xᵖ) - g(X)ᵖ`.

Mathlib provides the characteristic-`p` identity `ZMod.expand_card`; this is its integral
shadow, obtained by reducing mod `p`. -/
theorem C_natCast_dvd_expand_sub_pow (g : ℤ[X]) :
    C (p : ℤ) ∣ expand ℤ p g - g ^ p := by
  rw [C_dvd_iff_zmod, Polynomial.map_sub, Polynomial.map_expand,
    Polynomial.map_pow, ZMod.expand_card, sub_self]

variable {g : ℤ[X]}

/-- `⟨p, g⟩` is the contraction, along reduction mod `p`, of the principal ideal
generated by the reduction of `g`.

Reduction mod `p` is surjective with kernel `⟨p⟩`, so this is `Ideal.comap_map_of_surjective`
combined with `Polynomial.ker_mapRingHom` and `ZMod.ker_intCastRingHom`. -/
theorem span_pair_C_natCast_eq_comap :
    (Ideal.span {C (p : ℤ), g} : Ideal ℤ[X]) =
      Ideal.comap (Polynomial.mapRingHom (Int.castRingHom (ZMod p)))
        (Ideal.span {g.map (Int.castRingHom (ZMod p))}) := by
  have hsurj : Function.Surjective (Polynomial.mapRingHom (Int.castRingHom (ZMod p))) :=
    Polynomial.map_surjective _ ZMod.intCast_surjective
  have hmap : Ideal.map (Polynomial.mapRingHom (Int.castRingHom (ZMod p)))
      (Ideal.span {g}) = Ideal.span {g.map (Int.castRingHom (ZMod p))} := by
    rw [Ideal.map_span]; simp [Polynomial.coe_mapRingHom]
  rw [← hmap, Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot,
    Polynomial.ker_mapRingHom, ZMod.ker_intCastRingHom, Ideal.map_span, Ideal.span_insert]
  simp [sup_comm]

/-- Membership in `⟨p, g⟩` is exactly divisibility of the reductions mod `p`. -/
theorem mem_span_pair_C_natCast_iff {f : ℤ[X]} :
    f ∈ (Ideal.span {C (p : ℤ), g} : Ideal ℤ[X]) ↔
      g.map (Int.castRingHom (ZMod p)) ∣ f.map (Int.castRingHom (ZMod p)) := by
  rw [span_pair_C_natCast_eq_comap, Ideal.mem_comap, Ideal.mem_span_singleton]
  rfl

/-- If the reduction of `g` mod `p` is irreducible then `⟨p, g⟩` is a prime ideal of
`ℤ[X]`: it is the contraction of the prime ideal that reduction generates in
`(ZMod p)[X]`. -/
theorem isPrime_span_pair_C_natCast
    (hgirr : Irreducible (g.map (Int.castRingHom (ZMod p)))) :
    (Ideal.span {C (p : ℤ), g} : Ideal ℤ[X]).IsPrime := by
  have : (Ideal.span {g.map (Int.castRingHom (ZMod p))}).IsPrime :=
    (Ideal.span_singleton_prime hgirr.ne_zero).mpr (irreducible_iff_prime.mp hgirr)
  rw [span_pair_C_natCast_eq_comap]
  infer_instance

/-- `g(Xᵖ)` lies in `⟨p, g⟩`, since mod `p` it is the `p`-th power of the reduction
of `g`. -/
theorem expand_mem_span_pair (g : ℤ[X]) :
    expand ℤ p g ∈ (Ideal.span {C (p : ℤ), g} : Ideal ℤ[X]) := by
  rw [mem_span_pair_C_natCast_iff, Polynomial.map_expand, ZMod.expand_card]
  exact dvd_pow_self _ hp.out.ne_zero

/-- Membership in `𝔪 ^ 2` depends only on the class modulo `𝔪 ^ 2`. -/
private theorem mem_sq_iff_of_sub_mem {I : Ideal ℤ[X]} {x y : ℤ[X]} (h : x - y ∈ I ^ 2) :
    x ∈ I ^ 2 ↔ y ∈ I ^ 2 :=
  ⟨fun hx => (Submodule.sub_mem_iff_right _ hx).mp h,
    fun hy => (Submodule.sub_mem_iff_left _ hy).mp h⟩

/-- Auxiliary step in Theorem 2.4: if `p * rᵖ ∈ ⟨p, g⟩ ^ 2` then already
`p * r ∈ ⟨p, g⟩ ^ 2`.  This is the only place where irreducibility of the reduction
of `g` is used. -/
theorem C_mul_mem_sq_of_C_mul_pow_mem_sq
    (hgirr : Irreducible (g.map (Int.castRingHom (ZMod p)))) {r : ℤ[X]}
    (h : C (p : ℤ) * r ^ p ∈ (Ideal.span {C (p : ℤ), g} : Ideal ℤ[X]) ^ 2) :
    C (p : ℤ) * r ∈ (Ideal.span {C (p : ℤ), g} : Ideal ℤ[X]) ^ 2 := by
  set φ := Int.castRingHom (ZMod p) with hφ
  have hCp0 : (C (p : ℤ) : ℤ[X]) ≠ 0 := by
    simpa using Int.natCast_ne_zero.mpr hp.out.ne_zero
  obtain ⟨u, v, w, huvw⟩ := Ideal.mem_span_pair_sq_iff.mp h
  -- Reduce mod `p`: the equation collapses to `g ^ 2 * w = 0`, so `p ∣ w`.
  have hwdvd : C (p : ℤ) ∣ w := by
    rw [C_dvd_iff_zmod]
    have hgw : (g ^ 2 * w).map φ = 0 := by
      have h2 : g ^ 2 * w = C (p : ℤ) * r ^ p - C (p : ℤ) ^ 2 * u - C (p : ℤ) * g * v := by
        linear_combination -huvw
      rw [h2]
      simp [Polynomial.map_sub, Polynomial.map_mul]
    rw [Polynomial.map_mul, Polynomial.map_pow] at hgw
    exact (mul_eq_zero.mp hgw).resolve_left (pow_ne_zero _ hgirr.ne_zero)
  obtain ⟨w', rfl⟩ := hwdvd
  -- Cancel one factor of `p` to see that `rᵖ ∈ ⟨p, g⟩`, hence `r ∈ ⟨p, g⟩`.
  have hcancel : r ^ p = C (p : ℤ) * u + g * v + g ^ 2 * w' :=
    mul_left_cancel₀ hCp0 (by linear_combination huvw)
  have hrmem : r ∈ (Ideal.span {C (p : ℤ), g} : Ideal ℤ[X]) :=
    (isPrime_span_pair_C_natCast hgirr).mem_of_pow_mem p
      (Ideal.mem_span_pair.mpr ⟨u, v + g * w', by rw [hcancel]; ring⟩)
  rw [sq]
  exact Ideal.mul_mem_mul (Ideal.subset_span (by simp)) hrmem

/-- **Theorem 2.4** of Kaur–Kumar–Remete.  Let `p` be a prime and `g : ℤ[X]` a polynomial
whose reduction mod `p` is irreducible, and suppose `f ∈ ⟨p, g ^ 2⟩` — equivalently, that
the reduction of `g` is a repeated factor of that of `f`.  Then

`f ∈ ⟨p, g⟩ ^ 2 ↔ f(Xᵖ) ∈ ⟨p, g⟩ ^ 2`.

Via Uchida's criterion this says that `p` divides the index of `f` if and only if it
divides the index of `f(Xᵖ)`, which is what makes the monogenicity of `f(X ^ k)` depend
only on `rad k` and not on the exponents of the primes dividing `k`. -/
theorem mem_sq_span_iff_expand_mem_sq_span
    (hgirr : Irreducible (g.map (Int.castRingHom (ZMod p)))) {f : ℤ[X]}
    (hf : f ∈ (Ideal.span {C (p : ℤ), g ^ 2} : Ideal ℤ[X])) :
    f ∈ (Ideal.span {C (p : ℤ), g} : Ideal ℤ[X]) ^ 2 ↔
      expand ℤ p f ∈ (Ideal.span {C (p : ℤ), g} : Ideal ℤ[X]) ^ 2 := by
  set I : Ideal ℤ[X] := Ideal.span {C (p : ℤ), g} with hI
  have hgI : g ∈ I := Ideal.subset_span (by simp)
  have hpI : (C (p : ℤ) : ℤ[X]) ∈ I := Ideal.subset_span (by simp)
  have hg2 : g ^ 2 ∈ I ^ 2 := by rw [sq, sq]; exact Ideal.mul_mem_mul hgI hgI
  -- Write `f = r * p + q * g ^ 2`.
  obtain ⟨r, q, hrq⟩ := Ideal.mem_span_pair.mp hf
  -- Step 1: `f ∈ I ^ 2 ↔ p * r ∈ I ^ 2`, since `g ^ 2 * q ∈ I ^ 2`.
  have step1 : f ∈ I ^ 2 ↔ C (p : ℤ) * r ∈ I ^ 2 := by
    refine mem_sq_iff_of_sub_mem ?_
    have : f - C (p : ℤ) * r = g ^ 2 * q := by linear_combination -hrq
    rw [this]
    exact Ideal.mul_mem_right _ _ hg2
  -- Step 2: the same computation after substituting `Xᵖ`, using `g(Xᵖ) ∈ I`.
  have hexg : expand ℤ p g ∈ I := expand_mem_span_pair g
  have step2 : expand ℤ p f ∈ I ^ 2 ↔ C (p : ℤ) * expand ℤ p r ∈ I ^ 2 := by
    refine mem_sq_iff_of_sub_mem ?_
    have hexp : expand ℤ p f - C (p : ℤ) * expand ℤ p r =
        (expand ℤ p g) ^ 2 * expand ℤ p q := by
      have := congrArg (expand ℤ p) hrq
      simp only [map_add, map_mul, map_pow, expand_C] at this
      linear_combination -this
    rw [hexp]
    exact Ideal.mul_mem_right _ _ (by rw [sq, sq]; exact Ideal.mul_mem_mul hexg hexg)
  -- Step 3: `p * r(Xᵖ) ≡ p * r ^ p` modulo `p ^ 2 ∈ I ^ 2`.
  have step3 : C (p : ℤ) * expand ℤ p r ∈ I ^ 2 ↔ C (p : ℤ) * r ^ p ∈ I ^ 2 := by
    refine mem_sq_iff_of_sub_mem ?_
    obtain ⟨c, hc⟩ := C_natCast_dvd_expand_sub_pow (p := p) r
    have : C (p : ℤ) * expand ℤ p r - C (p : ℤ) * r ^ p = C (p : ℤ) ^ 2 * c := by
      linear_combination C (p : ℤ) * hc
    rw [this, sq, sq]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul hpI hpI)
  -- Step 4: `p * r ∈ I ^ 2 ↔ p * rᵖ ∈ I ^ 2`.
  have step4 : C (p : ℤ) * r ∈ I ^ 2 ↔ C (p : ℤ) * r ^ p ∈ I ^ 2 := by
    refine ⟨fun hpr => ?_, fun hpr => C_mul_mem_sq_of_C_mul_pow_mem_sq hgirr hpr⟩
    have hp1 : p - 1 + 1 = p := by have := hp.out.pos; omega
    have hpow : C (p : ℤ) * r ^ p = (C (p : ℤ) * r) * r ^ (p - 1) := by
      rw [mul_assoc, ← pow_succ', hp1]
    rw [hpow]
    exact Ideal.mul_mem_right _ _ hpr
  rw [step1, step2, step3, step4]

end Polynomial
