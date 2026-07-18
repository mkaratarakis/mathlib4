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

/-- If `p * s` lies in `⟨p, g⟩ ^ 2` then `s` already lies in `⟨p, g⟩`.  Only nonvanishing of
the reduction of `g` is needed, not irreducibility. -/
theorem mem_span_pair_of_C_mul_mem_sq (hg0 : g.map (Int.castRingHom (ZMod p)) ≠ 0) {s : ℤ[X]}
    (hs : C (p : ℤ) * s ∈ (Ideal.span {C (p : ℤ), g} : Ideal ℤ[X]) ^ 2) :
    s ∈ (Ideal.span {C (p : ℤ), g} : Ideal ℤ[X]) := by
  have hCp0 : (C (p : ℤ) : ℤ[X]) ≠ 0 := by
    simpa using Int.natCast_ne_zero.mpr hp.out.ne_zero
  obtain ⟨u, v, w, huvw⟩ := Ideal.mem_span_pair_sq_iff.mp hs
  -- Reduce mod `p`: the equation collapses to `g ^ 2 * w = 0`, so `p ∣ w`.
  have hwdvd : C (p : ℤ) ∣ w := by
    rw [C_dvd_iff_zmod]
    have hgw : (g ^ 2 * w).map (Int.castRingHom (ZMod p)) = 0 := by
      have h2 : g ^ 2 * w = C (p : ℤ) * s - C (p : ℤ) ^ 2 * u - C (p : ℤ) * g * v := by
        linear_combination -huvw
      rw [h2]
      simp [Polynomial.map_sub, Polynomial.map_mul]
    rw [Polynomial.map_mul, Polynomial.map_pow] at hgw
    exact (mul_eq_zero.mp hgw).resolve_left (pow_ne_zero _ hg0)
  obtain ⟨w', rfl⟩ := hwdvd
  -- Cancel one factor of `p`.
  have hcancel : s = C (p : ℤ) * u + g * v + g ^ 2 * w' :=
    mul_left_cancel₀ hCp0 (by linear_combination huvw)
  exact Ideal.mem_span_pair.mpr ⟨u, v + g * w', by rw [hcancel]; ring⟩

/-- An element of `⟨p, g⟩ ^ 2` whose degree is below `2 * deg g` is divisible by `p`:
modulo `p` it is a multiple of the reduction of `g ^ 2`, which has degree `2 * deg g`. -/
theorem C_dvd_of_mem_sq_of_natDegree_lt (hg : g.Monic) {r : ℤ[X]}
    (hr : r ∈ (Ideal.span {C (p : ℤ), g} : Ideal ℤ[X]) ^ 2)
    (hdeg : r.natDegree < 2 * g.natDegree) : C (p : ℤ) ∣ r := by
  rw [C_dvd_iff_zmod]
  by_contra hne
  obtain ⟨u, v, w, huvw⟩ := Ideal.mem_span_pair_sq_iff.mp hr
  have hdvd : (g.map (Int.castRingHom (ZMod p))) ^ 2 ∣ r.map (Int.castRingHom (ZMod p)) := by
    refine ⟨w.map (Int.castRingHom (ZMod p)), ?_⟩
    rw [huvw]
    simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]
  have hle := Polynomial.natDegree_le_of_dvd hdvd hne
  rw [(hg.map _).natDegree_pow, hg.natDegree_map] at hle
  exact absurd (hle.trans natDegree_map_le) (by omega)

/-- Reduction mod `p` of `f(X ^ (p ^ u))` is the `p ^ u`-th power of the reduction of `f`. -/
theorem map_expand_pow_card (u : ℕ) (f : ℤ[X]) :
    (expand ℤ (p ^ u) f).map (Int.castRingHom (ZMod p)) =
      (f.map (Int.castRingHom (ZMod p))) ^ p ^ u := by
  induction u generalizing f with
  | zero => simp
  | succ n ih =>
    rw [show p ^ (n + 1) = p ^ n * p from pow_succ p n, expand_mul, ih (expand ℤ p f),
      Polynomial.map_expand, ZMod.expand_card, ← pow_mul]
    congr 1
    ring

/-- `⟨p, g⟩ ^ 2 ⊆ ⟨p, g ^ 2⟩`: a repeated factor of the square is a repeated factor. -/
theorem sq_span_pair_le_span_pair_sq :
    (Ideal.span {C (p : ℤ), g} : Ideal ℤ[X]) ^ 2 ≤ Ideal.span {C (p : ℤ), g ^ 2} := by
  intro z hz
  obtain ⟨a, b, c, habc⟩ := Ideal.mem_span_pair_sq_iff.mp hz
  rw [mem_span_pair_C_natCast_iff]
  exact ⟨c.map (Int.castRingHom (ZMod p)), by
    rw [habc]; simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]⟩

/-- The hypothesis of Theorem 2.4 is stable under `X ↦ X ^ p`, so the theorem can be
iterated. -/
theorem expand_mem_span_pair_sq_of_mem_span_pair_sq {f : ℤ[X]}
    (hf : f ∈ (Ideal.span {C (p : ℤ), g ^ 2} : Ideal ℤ[X])) :
    expand ℤ p f ∈ (Ideal.span {C (p : ℤ), g ^ 2} : Ideal ℤ[X]) := by
  rw [mem_span_pair_C_natCast_iff] at hf ⊢
  rw [Polynomial.map_expand, ZMod.expand_card]
  exact hf.trans (dvd_pow_self _ hp.out.ne_zero)

omit hp in
/-- Substituting `X ^ ℓ` carries `⟨p, g⟩ ^ 2` into `⟨p, g(X ^ ℓ)⟩ ^ 2`, since `expand` is a
ring homomorphism fixing the constants. -/
theorem expand_mem_sq_span_of_mem_sq_span {ℓ : ℕ} {f : ℤ[X]}
    (hf : f ∈ (Ideal.span {C (p : ℤ), g} : Ideal ℤ[X]) ^ 2) :
    expand ℤ ℓ f ∈ (Ideal.span {C (p : ℤ), expand ℤ ℓ g} : Ideal ℤ[X]) ^ 2 := by
  obtain ⟨u, v, w, huvw⟩ := Ideal.mem_span_pair_sq_iff.mp hf
  refine Ideal.mem_span_pair_sq_iff.mpr ⟨expand ℤ ℓ u, expand ℤ ℓ v, expand ℤ ℓ w, ?_⟩
  rw [huvw]
  simp only [map_add, map_mul, map_pow, expand_C]

/-- If the reduction of `h` divides that of `G`, then `⟨p, G⟩ ⊆ ⟨p, h⟩`. -/
theorem span_pair_le_of_map_dvd {G h : ℤ[X]}
    (hdvd : h.map (Int.castRingHom (ZMod p)) ∣ G.map (Int.castRingHom (ZMod p))) :
    (Ideal.span {C (p : ℤ), G} : Ideal ℤ[X]) ≤ Ideal.span {C (p : ℤ), h} := by
  intro x hx
  rw [mem_span_pair_C_natCast_iff] at hx ⊢
  exact hdvd.trans hx

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
  have hrmem : r ∈ (Ideal.span {C (p : ℤ), g} : Ideal ℤ[X]) :=
    (isPrime_span_pair_C_natCast hgirr).mem_of_pow_mem p
      (mem_span_pair_of_C_mul_mem_sq hgirr.ne_zero h)
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

/-- **Corollary 2.5** at the level of ideals: iterating Theorem 2.4.  If `f ∈ ⟨p, g ^ 2⟩`
then for every `u`,
`f ∈ ⟨p, g⟩ ^ 2 ↔ f(X ^ (p ^ u)) ∈ ⟨p, g⟩ ^ 2`.

This is what makes membership independent of the exponent of `p`. -/
theorem mem_sq_span_iff_expand_pow_mem_sq_span
    (hgirr : Irreducible (g.map (Int.castRingHom (ZMod p)))) :
    ∀ (u : ℕ) {f : ℤ[X]}, f ∈ (Ideal.span {C (p : ℤ), g ^ 2} : Ideal ℤ[X]) →
      (f ∈ (Ideal.span {C (p : ℤ), g} : Ideal ℤ[X]) ^ 2 ↔
        expand ℤ (p ^ u) f ∈ (Ideal.span {C (p : ℤ), g} : Ideal ℤ[X]) ^ 2) := by
  intro u
  induction u with
  | zero => intro f _; simp
  | succ n ih =>
    intro f hf
    rw [show p ^ (n + 1) = p ^ n * p from pow_succ p n, expand_mul,
      mem_sq_span_iff_expand_mem_sq_span hgirr hf]
    exact ih (expand_mem_span_pair_sq_of_mem_span_pair_sq hf)

/-- **Lemma 2.1** of Kaur–Kumar–Remete: `⟨p, g⟩ ^ 2 = ⟨p ^ 2, g⟩ ⊓ ⟨p, g ^ 2⟩`.

The published proof deduces the nontrivial inclusion from primality of `⟨g⟩` in `ℤ[X]`,
which needs `g` monic with irreducible reduction.  Reducing mod `p` instead gives it
directly from nonvanishing of the reduction of `g`: comparing the two decompositions of
`z` forces that reduction to divide the cofactor of `g`. -/
theorem span_pair_sq_eq_inf (hg0 : g.map (Int.castRingHom (ZMod p)) ≠ 0) :
    (Ideal.span {C (p : ℤ), g} : Ideal ℤ[X]) ^ 2 =
      Ideal.span {C (p : ℤ) ^ 2, g} ⊓ Ideal.span {C (p : ℤ), g ^ 2} := by
  refine le_antisymm (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨a, b, c, habc⟩ := Ideal.mem_span_pair_sq_iff.mp hz
    exact ⟨Ideal.mem_span_pair.mpr ⟨a, C (p : ℤ) * b + g * c, by rw [habc]; ring⟩,
      Ideal.mem_span_pair.mpr ⟨C (p : ℤ) * a + g * b, c, by rw [habc]; ring⟩⟩
  · obtain ⟨hz1, hz2⟩ := hz
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hz1
    obtain ⟨c, d, hcd⟩ := Ideal.mem_span_pair.mp hz2
    -- Modulo `p` the two decompositions of `z` agree; cancelling the reduction of `g`
    -- shows it divides the reduction of `b`.
    have hb : b ∈ (Ideal.span {C (p : ℤ), g} : Ideal ℤ[X]) := by
      rw [mem_span_pair_C_natCast_iff]
      have h := congrArg (Polynomial.map (Int.castRingHom (ZMod p))) (hab.trans hcd.symm)
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_C,
        Int.coe_castRingHom, Int.cast_natCast, ZMod.natCast_self, C_0] at h
      refine Dvd.intro (d.map (Int.castRingHom (ZMod p))) ?_
      have hcancel : b.map (Int.castRingHom (ZMod p)) =
          d.map (Int.castRingHom (ZMod p)) * g.map (Int.castRingHom (ZMod p)) :=
        mul_right_cancel₀ hg0 (by linear_combination h)
      linear_combination -hcancel
    obtain ⟨e', e, he⟩ := Ideal.mem_span_pair.mp hb
    exact Ideal.mem_span_pair_sq_iff.mpr ⟨a, e', e, by rw [← hab, ← he]; ring⟩

/-- **Corollary 2.2** of Kaur–Kumar–Remete.  If the reduction of `g` is a repeated factor
of that of `f`, then
membership of `f` in `⟨p, g⟩ ^ 2` is decided by the remainder of `f` on division by `g`
being a multiple of `p ^ 2`. -/
theorem mem_sq_span_iff_mem_span_C_sq (hg0 : g.map (Int.castRingHom (ZMod p)) ≠ 0)
    {f : ℤ[X]} (hf : f ∈ (Ideal.span {C (p : ℤ), g ^ 2} : Ideal ℤ[X])) :
    f ∈ (Ideal.span {C (p : ℤ), g} : Ideal ℤ[X]) ^ 2 ↔
      f ∈ (Ideal.span {C (p : ℤ) ^ 2, g} : Ideal ℤ[X]) := by
  rw [span_pair_sq_eq_inf hg0]
  exact ⟨fun h => h.1, fun h => ⟨h, hf⟩⟩

omit hp in
/-- Membership in `⟨p ^ 2, X⟩` is divisibility of the constant term by `p ^ 2`. -/
theorem mem_span_pair_C_sq_X_iff {f : ℤ[X]} :
    f ∈ (Ideal.span {C (p : ℤ) ^ 2, X} : Ideal ℤ[X]) ↔ (p : ℤ) ^ 2 ∣ f.coeff 0 := by
  constructor
  · rintro hf
    obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hf
    simp [coeff_zero_eq_eval_zero]
  · rintro ⟨c, hc⟩
    obtain ⟨q, hq⟩ : (X : ℤ[X]) ∣ f - C (f.coeff 0) := by
      rw [X_dvd_iff]; simp
    refine Ideal.mem_span_pair.mpr ⟨C c, q, ?_⟩
    have : C (f.coeff 0) = C (p : ℤ) ^ 2 * C c := by rw [hc, map_mul, map_pow]
    linear_combination -hq - this

/-- First sub-case of Proposition 2.10: if `p ^ 2` does not divide the constant term, then
`f` avoids `⟨p, X⟩ ^ 2`.  Combined with `span_pair_sq_eq_inf`, since the reduction of `X`
is nonzero. -/
theorem notMem_sq_span_pair_X_of_sq_not_dvd_coeff_zero {f : ℤ[X]}
    (h : ¬ (p : ℤ) ^ 2 ∣ f.coeff 0) :
    f ∉ (Ideal.span {C (p : ℤ), X} : Ideal ℤ[X]) ^ 2 := by
  have hX0 : (X : ℤ[X]).map (Int.castRingHom (ZMod p)) ≠ 0 := by
    rw [Polynomial.map_X]; exact X_ne_zero
  rw [span_pair_sq_eq_inf hX0]
  exact fun hm => h (mem_span_pair_C_sq_X_iff.mp hm.1)

omit hp in
/-- A repeated factor divides the derivative. -/
theorem dvd_derivative_of_sq_dvd {R : Type*} [CommRing R] {h E : R[X]} (hd : h ^ 2 ∣ E) :
    h ∣ derivative E := by
  obtain ⟨m, rfl⟩ := hd
  refine ⟨C 2 * derivative h * m + h * derivative m, ?_⟩
  rw [derivative_mul, derivative_pow]
  push_cast
  ring

/-- Second step toward Proposition 2.10.  Let `p ∤ ℓ` and let `h` be irreducible mod `p`,
not dividing `X`.  If `h ^ 2` divides `q(X ^ ℓ)` then `h` divides `q'(X ^ ℓ)`.

The derivative of `q(X ^ ℓ)` is `q'(X ^ ℓ) · ℓ X ^ (ℓ - 1)`; the factor `ℓ` is a unit
because `p ∤ ℓ`, and `h` misses `X ^ (ℓ - 1)` because it is prime and does not divide `X`. -/
theorem dvd_expand_derivative_of_sq_dvd_expand {ℓ : ℕ} (hℓ : ¬ (p : ℕ) ∣ ℓ)
    {q h : (ZMod p)[X]} (hirr : Irreducible h) (hX : ¬ h ∣ X)
    (hsq : h ^ 2 ∣ expand (ZMod p) ℓ q) :
    h ∣ expand (ZMod p) ℓ (derivative q) := by
  have h1 : h ∣ expand (ZMod p) ℓ (derivative q) * ((ℓ : (ZMod p)[X]) * X ^ (ℓ - 1)) := by
    rw [← derivative_expand]; exact dvd_derivative_of_sq_dvd hsq
  have hprime := irreducible_iff_prime.mp hirr
  -- `h` divides neither `ℓ` (a unit) nor `X ^ (ℓ - 1)`.
  rcases hprime.dvd_mul.mp h1 with hcase | hcase
  · exact hcase
  · exfalso
    rcases hprime.dvd_mul.mp hcase with hu | hxp
    · have hne : ((ℓ : ZMod p)) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
      have hunit : IsUnit ((ℓ : (ZMod p)[X])) := by
        rw [show ((ℓ : (ZMod p)[X])) = C ((ℓ : ZMod p)) by simp]
        exact isUnit_C.mpr hne.isUnit
      exact hirr.not_isUnit (isUnit_of_dvd_unit hu hunit)
    · exact hX (hprime.dvd_of_dvd_pow hxp)

/-- Third step toward Proposition 2.10.  If `h ^ 2` divides `q(X ^ ℓ)` for some irreducible
`h` not dividing `X`, and `p ∤ ℓ`, then `q` is not separable.

Indeed `h` divides both `q(X ^ ℓ)` and `q'(X ^ ℓ)`, so applying `expand` to a Bézout
identity `u q + v q' = 1` would exhibit `h` as a unit. -/
theorem not_separable_of_sq_dvd_expand {ℓ : ℕ} (hℓ : ¬ (p : ℕ) ∣ ℓ)
    {q h : (ZMod p)[X]} (hirr : Irreducible h) (hX : ¬ h ∣ X)
    (hsq : h ^ 2 ∣ expand (ZMod p) ℓ q) :
    ¬ q.Separable := by
  intro hsep
  obtain ⟨u, v, huv⟩ := hsep
  have h1 : h ∣ expand (ZMod p) ℓ q := (dvd_pow_self h two_ne_zero).trans hsq
  have h2 : h ∣ expand (ZMod p) ℓ (derivative q) :=
    dvd_expand_derivative_of_sq_dvd_expand hℓ hirr hX hsq
  have hone : h ∣ 1 := by
    have hexp := congrArg (expand (ZMod p) ℓ) huv
    rw [map_add, map_mul, map_mul, map_one] at hexp
    rw [← hexp]
    exact dvd_add (h1.mul_left _) (h2.mul_left _)
  exact hirr.not_isUnit (isUnit_of_dvd_one hone)

end Polynomial
