/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.Monogenic.PowerCompositional.Uchida

/-!
# Transfer of the index along `X ↦ X ^ ℓ`

This file proves Lemma 2.6 of S. Kaur, S. Kumar and L. Remete,
*On the index of power compositional polynomials*,
Finite Fields Appl. **107** (2025), 102642: a prime dividing the index of `f` also divides
the index of `f(X ^ ℓ)`; and Corollary 2.5, that the index at `p` cannot distinguish
`f(X ^ p)` from `f(X ^ (p ^ u))`.

Both statements are about roots in *different* number fields — a root of `f` and a root of
`f(X ^ ℓ)` — so the results below take two algebraic integers `θ` and `ω` together with
hypotheses naming their minimal polynomials, rather than being statements about a single
field.

## Main results

* `Polynomial.exists_monic_map_irreducible_dvd`: a monic nonconstant polynomial over `ℤ`
  admits a monic `h` whose reduction is an irreducible factor of its own reduction.

* `RingOfIntegers.dvd_exponent_expand_of_dvd_exponent`: Lemma 2.6.

* `RingOfIntegers.dvd_exponent_expand_pow_iff`: Corollary 2.5 --- `p` divides the index of
  `f(X ^ p)` iff it divides the index of `f(X ^ (p ^ u))`.

## References

* [S. Kaur, S. Kumar, L. Remete, *On the index of power compositional polynomials*][KKR2025]
-/

@[expose] public section

noncomputable section

open Polynomial NumberField

namespace Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

/-- A monic nonconstant `G : ℤ[X]` admits a monic `h : ℤ[X]`, itself nonconstant, whose
reduction mod `p` is an irreducible factor of the reduction of `G`. -/
theorem exists_monic_map_irreducible_dvd {G : ℤ[X]} (hG : G.Monic) (hGd : 0 < G.natDegree) :
    ∃ h : ℤ[X], h.Monic ∧ 0 < h.natDegree ∧
      Irreducible (h.map (Int.castRingHom (ZMod p))) ∧
      h.map (Int.castRingHom (ZMod p)) ∣ G.map (Int.castRingHom (ZMod p)) := by
  have hsurj : Function.Surjective (Int.castRingHom (ZMod p)) := ZMod.intCast_surjective
  have hGm : (G.map (Int.castRingHom (ZMod p))).Monic := hG.map _
  have hGd' : 0 < (G.map (Int.castRingHom (ZMod p))).natDegree := by rwa [hG.natDegree_map]
  -- An irreducible factor of the reduction, normalised to be monic.
  obtain ⟨π₀, hπ₀irr, hπ₀dvd⟩ := WfDvdMonoid.exists_irreducible_factor
    (not_isUnit_of_natDegree_pos _ hGd') hGm.ne_zero
  set π := normalize π₀ with hπdef
  have hπirr : Irreducible π := (associated_normalize π₀).irreducible hπ₀irr
  have hπmonic : π.Monic := monic_normalize hπ₀irr.ne_zero
  have hπdvd : π ∣ G.map (Int.castRingHom (ZMod p)) := by
    rw [hπdef, normalize_dvd_iff]; exact hπ₀dvd
  -- Lift it to a monic polynomial over `ℤ`.
  obtain ⟨h, hhmap, -, hhmonic⟩ :=
    lifts_and_degree_eq_and_monic ((mem_lifts π).mpr
      (Polynomial.map_surjective _ hsurj π)) hπmonic
  refine ⟨h, hhmonic, ?_, by rw [hhmap]; exact hπirr, by rw [hhmap]; exact hπdvd⟩
  rcases Nat.eq_zero_or_pos h.natDegree with h0 | hpos
  · exact absurd (by rw [← hhmap, eq_one_of_monic_natDegree_zero hhmonic h0,
      Polynomial.map_one] : π = 1) (fun he => not_irreducible_one (he ▸ hπirr))
  · exact hpos

end Polynomial

namespace RingOfIntegers

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
variable {θ : 𝓞 K} {ω : 𝓞 L} {p : ℕ} [hp : Fact p.Prime]

/-- **Lemma 2.6** of Kaur–Kumar–Remete.  If a prime `p` divides the index of `f`, then it
divides the index of `f(X ^ ℓ)`.

Here `θ` is a root of `f` and `ω` a root of `f(X ^ ℓ)`, generating (possibly different)
number fields `K` and `L`.  Via Uchida's criterion the proof is short: `f` lies in
`⟨p, Pi⟩ ^ 2` for some monic `Pi` irreducible mod `p`; applying `X ↦ X ^ ℓ` puts
`f(X ^ ℓ)` in `⟨p, Pi(X ^ ℓ)⟩ ^ 2`, and any monic irreducible factor `h` of the reduction
of `Pi(X ^ ℓ)` gives `⟨p, Pi(X ^ ℓ)⟩ ⊆ ⟨p, h⟩`, hence `f(X ^ ℓ) ∈ ⟨p, h⟩ ^ 2`. -/
theorem dvd_exponent_expand_of_dvd_exponent {f : ℤ[X]} {ℓ : ℕ} (hℓ : 0 < ℓ)
    (hθ : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hmθ : minpoly ℤ θ = f) (hmω : minpoly ℤ ω = expand ℤ ℓ f)
    (hdvd : p ∣ exponent θ) :
    p ∣ exponent ω := by
  obtain ⟨Pi, hPim, hPiirr, hmem⟩ :=
    exists_monic_irreducible_minpoly_mem_sq_of_dvd_exponent hθ hdvd
  rw [hmθ] at hmem
  -- `Pi` is nonconstant, hence so is `Pi(X ^ ℓ)`.
  have hPid : 0 < Pi.natDegree := by
    rcases Nat.eq_zero_or_pos Pi.natDegree with h0 | hpos
    · rw [eq_one_of_monic_natDegree_zero hPim h0, Polynomial.map_one] at hPiirr
      exact absurd hPiirr not_irreducible_one
    · exact hpos
  have hEm : (expand ℤ ℓ Pi).Monic := hPim.expand hℓ
  have hEd : 0 < (expand ℤ ℓ Pi).natDegree := by
    rw [natDegree_expand]; positivity
  -- Choose a monic `h` whose reduction is an irreducible factor of that of `Pi(X ^ ℓ)`.
  obtain ⟨h, hhm, hhd, hhirr, hhdvd⟩ := exists_monic_map_irreducible_dvd (p := p) hEm hEd
  refine dvd_exponent_of_minpoly_mem_sq hhm hhd ?_
  rw [hmω]
  exact Ideal.pow_right_mono (span_pair_le_of_map_dvd hhdvd) 2
    (expand_mem_sq_span_of_mem_sq_span hmem)

/-- **Corollary 2.5** of Kaur–Kumar–Remete.  For a monic `f`, the prime `p` divides the
index of `f(X ^ p)` if and only if it divides the index of `f(X ^ (p ^ u))`, for every
`u ≥ 1`.

So the monogenicity question at `p` does not see the exponent of `p` in `k`; this is what
lets Theorem 1.1 depend only on `rad k`.  Both sides are rewritten by Uchida's criterion,
after which the statement is the iterated Theorem 2.4,
`Polynomial.mem_sq_span_iff_expand_pow_mem_sq_span`. -/
theorem dvd_exponent_expand_pow_iff {f : ℤ[X]} {u : ℕ} (hu : 0 < u)
    (hθ : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hω : Algebra.adjoin ℚ {(ω : L)} = ⊤)
    (hmθ : minpoly ℤ θ = expand ℤ p f) (hmω : minpoly ℤ ω = expand ℤ (p ^ u) f) :
    p ∣ exponent θ ↔ p ∣ exponent ω := by
  -- Peeling off one `expand` from `p ^ u`.
  have hexp : expand ℤ (p ^ (u - 1)) (expand ℤ p f) = expand ℤ (p ^ u) f := by
    rw [← expand_mul, ← pow_succ, Nat.sub_add_cancel hu]
  rw [dvd_exponent_iff_exists_monic_irreducible_minpoly_mem_sq hθ,
    dvd_exponent_iff_exists_monic_irreducible_minpoly_mem_sq hω, hmθ, hmω]
  constructor
  · rintro ⟨Pi, hm, hirr, hmem⟩
    refine ⟨Pi, hm, hirr, ?_⟩
    rw [← hexp]
    exact (mem_sq_span_iff_expand_pow_mem_sq_span hirr (u - 1)
      (sq_span_pair_le_span_pair_sq hmem)).mp hmem
  · rintro ⟨Pi, hm, hirr, hmem⟩
    refine ⟨Pi, hm, hirr, ?_⟩
    -- `f(X ^ p)` still has the reduction of `Pi` as a repeated factor.
    have hsq : expand ℤ p f ∈ (Ideal.span {C (p : ℤ), Pi ^ 2} : Ideal ℤ[X]) := by
      have h1 : (Pi.map (Int.castRingHom (ZMod p))) ^ 2 ∣
          (f.map (Int.castRingHom (ZMod p))) ^ p ^ u := by
        have h := sq_span_pair_le_span_pair_sq hmem
        rwa [mem_span_pair_C_natCast_iff, map_expand_pow_card, Polynomial.map_pow] at h
      have h2 : Pi.map (Int.castRingHom (ZMod p)) ∣ f.map (Int.castRingHom (ZMod p)) :=
        (irreducible_iff_prime.mp hirr).dvd_of_dvd_pow
          ((dvd_pow_self _ two_ne_zero).trans h1)
      rw [mem_span_pair_C_natCast_iff, Polynomial.map_expand, ZMod.expand_card,
        Polynomial.map_pow]
      exact (pow_dvd_pow_of_dvd h2 2).trans (pow_dvd_pow _ hp.out.two_le)
    exact (mem_sq_span_iff_expand_pow_mem_sq_span hirr (u - 1) hsq).mpr (by rw [hexp]; exact hmem)

end RingOfIntegers
