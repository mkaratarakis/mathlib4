/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.Monogenic.PowerCompositional.Basic
public import Mathlib.NumberTheory.NumberField.Monogenic.PowerCompositional.Uchida

/-!
# Transfer of the index along `X ↦ X ^ ℓ`

This file proves Lemma 2.6 of S. Kaur, S. Kumar and L. Remete,
*On the index of power compositional polynomials*,
Finite Fields Appl. **107** (2025), 102642: a prime dividing the index of `f` also divides
the index of `f(X ^ ℓ)`; Corollary 2.5, that the index at `p` cannot distinguish
`f(X ^ p)` from `f(X ^ (p ^ u))`; and Proposition 2.10, which for `p ∤ ℓ` decides the index
of `f(X ^ ℓ)` at `p` in terms of `f`.

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

* `RingOfIntegers.dvd_exponent_or_sq_dvd_coeff_zero_of_dvd_exponent_expand` and
  `RingOfIntegers.dvd_exponent_expand_iff`: Proposition 2.10 --- for `2 ≤ ℓ` prime to `p`,
  the prime `p` divides the index of `f(X ^ ℓ)` iff it divides the index of `f` or
  `p ^ 2 ∣ f(0)`.  The published proof of the forward direction uses the discriminant
  identity `disc(f) = [𝓞 K : ℤ[θ]] ^ 2 · disc(K)`, which Mathlib does not have; the proof
  here is ideal-theoretic and avoids it.

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

/-- **Proposition 2.10** of Kaur–Kumar–Remete, the substantial direction.  Let `p ∤ ℓ`, let
`θ` be a root of `f` and `ω` a root of `f(X ^ ℓ)`.  If `p` divides the index of `f(X ^ ℓ)`,
then either it already divides the index of `f`, or `p ^ 2` divides `f(0)`.

The published proof treats the case `p ∤ f(0)` by discriminants, through
`disc(f) = [𝓞 K : ℤ[θ]] ^ 2 · disc(K)`, which is not available in Mathlib.  The argument
below is ideal-theoretic throughout and needs no discriminant.  By Uchida's criterion
`f(X ^ ℓ) ∈ ⟨p, h⟩ ^ 2` for some `h` monic and irreducible mod `p`, and the proof splits on
the reduction of `h`:

* if it is `X`, then `⟨p, h⟩ = ⟨p, X⟩` and membership in `⟨p, X⟩ ^ 2` says exactly
  `p ^ 2 ∣ f(0)`;
* otherwise the prime below `h` along `X ↦ X ^ ℓ` is a `G` whose square divides the
  reduction of `f` (`Polynomial.sq_dvd_of_sq_dvd_expand`, where `p ∤ ℓ` enters).  Lifting
  `G` to a monic `g : ℤ[X]` and dividing `f = g * q + r`, one shows `f ∈ ⟨p, g⟩ ^ 2` —
  hence `p` divides the index of `f` — by contradiction: otherwise `r = p * s` with `s`
  nonzero mod `p` and of degree below that of `G`, so the reduction of `s` is coprime to
  `G` and `h ∤ s(X ^ ℓ)`, while `f(X ^ ℓ) ∈ ⟨p, h⟩ ^ 2`
  forces `p * s(X ^ ℓ) ∈ ⟨p, h⟩ ^ 2` and therefore `h ∣ s(X ^ ℓ)`. -/
theorem dvd_exponent_or_sq_dvd_coeff_zero_of_dvd_exponent_expand {f : ℤ[X]} {ℓ : ℕ}
    (hℓ0 : 0 < ℓ) (hℓ : ¬ (p : ℕ) ∣ ℓ) (hω : Algebra.adjoin ℚ {(ω : L)} = ⊤)
    (hmθ : minpoly ℤ θ = f) (hmω : minpoly ℤ ω = expand ℤ ℓ f)
    (hdvd : p ∣ exponent ω) :
    p ∣ exponent θ ∨ (p : ℤ) ^ 2 ∣ f.coeff 0 := by
  obtain ⟨h, hhm, hhirr, hmem⟩ :=
    exists_monic_irreducible_minpoly_mem_sq_of_dvd_exponent hω hdvd
  rw [hmω] at hmem
  have hfm : f.Monic := hmθ ▸ minpoly.monic θ.isIntegral
  have hhm' : (h.map (Int.castRingHom (ZMod p))).Monic := hhm.map _
  have hhd : 0 < (h.map (Int.castRingHom (ZMod p))).natDegree := by
    rcases Nat.eq_zero_or_pos (h.map (Int.castRingHom (ZMod p))).natDegree with h0 | hpos
    · rw [eq_one_of_monic_natDegree_zero hhm' h0] at hhirr
      exact absurd hhirr not_irreducible_one
    · exact hpos
  by_cases hX : h.map (Int.castRingHom (ZMod p)) ∣ X
  · -- The reduction of `h` is `X`: read off the constant term.
    right
    by_contra hnot
    have hhX : h.map (Int.castRingHom (ZMod p)) = X := by
      obtain ⟨w, hw⟩ := hX
      have hwm : w.Monic := hhm'.of_mul_monic_left (hw ▸ monic_X)
      have hdeg : (h.map (Int.castRingHom (ZMod p))).natDegree + w.natDegree = 1 := by
        have hd := congrArg natDegree hw
        rwa [natDegree_X, hhm'.natDegree_mul hwm, eq_comm] at hd
      rw [hw, eq_one_of_monic_natDegree_zero hwm (by omega), mul_one]
    have hle : (Ideal.span {C (p : ℤ), h} : Ideal ℤ[X]) ≤ Ideal.span {C (p : ℤ), X} :=
      span_pair_le_of_map_dvd (by rw [Polynomial.map_X, hhX])
    refine notMem_sq_span_pair_X_of_sq_not_dvd_coeff_zero (p := p) (f := expand ℤ ℓ f) ?_
      (Ideal.pow_right_mono hle 2 hmem)
    rwa [coeff_expand hℓ0, if_pos (dvd_zero ℓ), Nat.zero_div]
  · -- The reduction of `h` is not `X`: descend the repeated factor to `f`.
    left
    have hsq : (h.map (Int.castRingHom (ZMod p))) ^ 2 ∣
        expand (ZMod p) ℓ (f.map (Int.castRingHom (ZMod p))) := by
      have hm2 := sq_span_pair_le_span_pair_sq hmem
      rwa [mem_span_pair_C_natCast_iff, Polynomial.map_expand, Polynomial.map_pow] at hm2
    have hf0 : f.map (Int.castRingHom (ZMod p)) ≠ 0 := (hfm.map _).ne_zero
    obtain ⟨G, hGm, hGirr, hGF, hhG⟩ :=
      exists_monic_irreducible_dvd_of_dvd_expand hf0 hhirr ((dvd_pow_self _ two_ne_zero).trans hsq)
    have hG2 : G ^ 2 ∣ f.map (Int.castRingHom (ZMod p)) :=
      sq_dvd_of_sq_dvd_expand hℓ hGirr hGF hhirr hX hhG hsq
    -- Lift `G` to a monic `g : ℤ[X]`.
    have hsurj : Function.Surjective (Int.castRingHom (ZMod p)) := ZMod.intCast_surjective
    obtain ⟨g, hgmap, -, hgmonic⟩ := lifts_and_degree_eq_and_monic
      ((mem_lifts G).mpr (Polynomial.map_surjective _ hsurj G)) hGm
    have hgdeg : 0 < g.natDegree := by
      rcases Nat.eq_zero_or_pos g.natDegree with h0 | hpos
      · rw [eq_one_of_monic_natDegree_zero hgmonic h0, Polynomial.map_one] at hgmap
        exact absurd (hgmap ▸ hGirr) not_irreducible_one
      · exact hpos
    have hgne1 : g ≠ 1 := fun h1 => by rw [h1] at hgdeg; simp at hgdeg
    have hgdegG : g.natDegree = G.natDegree := by rw [← hgmap, hgmonic.natDegree_map]
    refine dvd_exponent_of_minpoly_mem_sq hgmonic hgdeg ?_
    rw [hmθ]
    by_contra hnot
    set q := f /ₘ g with hqdef
    set r := f %ₘ g with hrdef
    have hdiv : r + g * q = f := modByMonic_add_div f g
    have hmapdiv : r.map (Int.castRingHom (ZMod p)) +
        G * q.map (Int.castRingHom (ZMod p)) = f.map (Int.castRingHom (ZMod p)) := by
      have hd := congrArg (Polynomial.map (Int.castRingHom (ZMod p))) hdiv
      rwa [Polynomial.map_add, Polynomial.map_mul, hgmap] at hd
    have hrdeg : r.natDegree < G.natDegree := by
      have hlt : r.natDegree < g.natDegree := by
        rw [hrdef]; exact natDegree_modByMonic_lt f hgmonic hgne1
      omega
    -- The remainder vanishes mod `p`.
    have hrmap : r.map (Int.castRingHom (ZMod p)) = 0 := by
      refine eq_zero_of_dvd_of_natDegree_lt ?_ (lt_of_le_of_lt natDegree_map_le hrdeg)
      have hreq : r.map (Int.castRingHom (ZMod p)) =
          f.map (Int.castRingHom (ZMod p)) - G * q.map (Int.castRingHom (ZMod p)) := by
        linear_combination hmapdiv
      rw [hreq]
      exact dvd_sub hGF (dvd_mul_right G _)
    obtain ⟨s, hs⟩ : C (p : ℤ) ∣ r := (C_dvd_iff_zmod p r).mpr hrmap
    -- The quotient is divisible by `G` mod `p`, so `g * q` already lies in `⟨p, g⟩ ^ 2`.
    have hGq : G ∣ q.map (Int.castRingHom (ZMod p)) := by
      obtain ⟨m, hm⟩ := hG2
      have hcancel : G * q.map (Int.castRingHom (ZMod p)) = G * (G * m) := by
        rw [← mul_assoc, ← sq, ← hm, ← hmapdiv, hrmap, zero_add]
      exact ⟨m, mul_left_cancel₀ hGirr.ne_zero hcancel⟩
    have hqmem : q ∈ (Ideal.span {C (p : ℤ), g} : Ideal ℤ[X]) :=
      mem_span_pair_C_natCast_iff.mpr (by rw [hgmap]; exact hGq)
    have hgmem : g ∈ (Ideal.span {C (p : ℤ), g} : Ideal ℤ[X]) := Ideal.subset_span (by simp)
    have hgq : g * q ∈ (Ideal.span {C (p : ℤ), g} : Ideal ℤ[X]) ^ 2 := by
      rw [sq]; exact Ideal.mul_mem_mul hgmem hqmem
    -- Hence `p * s` avoids `⟨p, g⟩ ^ 2`, so `s` is a unit mod `p`.
    have hCps : C (p : ℤ) * s ∉ (Ideal.span {C (p : ℤ), g} : Ideal ℤ[X]) ^ 2 := fun hcon =>
      hnot (by rw [← hdiv, hs]; exact Ideal.add_mem _ hcon hgq)
    have hsmap : s.map (Int.castRingHom (ZMod p)) ≠ 0 := by
      intro h0
      obtain ⟨s', rfl⟩ : C (p : ℤ) ∣ s := (C_dvd_iff_zmod p s).mpr h0
      refine hCps ?_
      have hsq2 : (Ideal.span {C (p : ℤ), g} : Ideal ℤ[X]) ^ 2 =
          Ideal.span {C (p : ℤ), g} * Ideal.span {C (p : ℤ), g} := sq _
      have heq : C (p : ℤ) * (C (p : ℤ) * s') = C (p : ℤ) * C (p : ℤ) * s' := by ring
      rw [heq, hsq2]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul
        (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp)))
    have hrs : r.natDegree = s.natDegree := by
      rw [hs, natDegree_C_mul (Int.natCast_ne_zero.mpr hp.out.ne_zero)]
    have hsdeg : (s.map (Int.castRingHom (ZMod p))).natDegree < G.natDegree :=
      lt_of_le_of_lt natDegree_map_le (by omega)
    -- The reduction of `s` is coprime to `G`, so `h` cannot divide `s(X ^ ℓ)`.
    have hGs : ¬ G ∣ s.map (Int.castRingHom (ZMod p)) := fun hcon =>
      hsmap (eq_zero_of_dvd_of_natDegree_lt hcon hsdeg)
    have hcop : IsCoprime G (s.map (Int.castRingHom (ZMod p))) :=
      (hGirr.coprime_iff_not_dvd).mpr hGs
    have hnhs : ¬ h.map (Int.castRingHom (ZMod p)) ∣
        expand (ZMod p) ℓ (s.map (Int.castRingHom (ZMod p))) := fun hcon =>
      hhirr.not_isUnit ((hcop.map (expand (ZMod p) ℓ).toRingHom).isUnit_of_dvd' hhG hcon)
    -- But `f(X ^ ℓ) ∈ ⟨p, h⟩ ^ 2` forces exactly that.
    apply hnhs
    have hEg : expand ℤ ℓ g ∈ (Ideal.span {C (p : ℤ), h} : Ideal ℤ[X]) :=
      mem_span_pair_C_natCast_iff.mpr (by rw [Polynomial.map_expand, hgmap]; exact hhG)
    have hEq : expand ℤ ℓ q ∈ (Ideal.span {C (p : ℤ), h} : Ideal ℤ[X]) :=
      mem_span_pair_C_natCast_iff.mpr (by
        rw [Polynomial.map_expand]
        exact hhG.trans (map_dvd (expand (ZMod p) ℓ) hGq))
    have hprod : expand ℤ ℓ g * expand ℤ ℓ q ∈
        (Ideal.span {C (p : ℤ), h} : Ideal ℤ[X]) ^ 2 := by
      rw [sq]; exact Ideal.mul_mem_mul hEg hEq
    have hEs : C (p : ℤ) * expand ℤ ℓ s ∈ (Ideal.span {C (p : ℤ), h} : Ideal ℤ[X]) ^ 2 := by
      have hexpand : expand ℤ ℓ f = C (p : ℤ) * expand ℤ ℓ s + expand ℤ ℓ g * expand ℤ ℓ q := by
        rw [← hdiv, hs, map_add, map_mul, map_mul, expand_C]
      have := Ideal.sub_mem _ hmem hprod
      rwa [hexpand, add_sub_cancel_right] at this
    have := mem_span_pair_of_C_mul_mem_sq (hhm'.ne_zero) hEs
    rw [mem_span_pair_C_natCast_iff, Polynomial.map_expand] at this
    exact this

/-- **Proposition 2.10** of Kaur–Kumar–Remete.  For `ℓ ≥ 2` prime to `p`, the prime `p`
divides the index of `f(X ^ ℓ)` if and only if it divides the index of `f` or `p ^ 2`
divides `f(0)`.

The forward direction is
`dvd_exponent_or_sq_dvd_coeff_zero_of_dvd_exponent_expand`; the two cases of the converse
are Lemma 2.6 (`dvd_exponent_expand_of_dvd_exponent`) and Proposition 2.3
(`dvd_exponent_of_sq_dvd_coeff_zero`). -/
theorem dvd_exponent_expand_iff {f : ℤ[X]} {ℓ : ℕ} (hℓ2 : 2 ≤ ℓ) (hℓ : ¬ (p : ℕ) ∣ ℓ)
    (hθ : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hω : Algebra.adjoin ℚ {(ω : L)} = ⊤)
    (hmθ : minpoly ℤ θ = f) (hmω : minpoly ℤ ω = expand ℤ ℓ f) :
    p ∣ exponent ω ↔ p ∣ exponent θ ∨ (p : ℤ) ^ 2 ∣ f.coeff 0 := by
  have hfm : f.Monic := hmθ ▸ minpoly.monic θ.isIntegral
  refine ⟨dvd_exponent_or_sq_dvd_coeff_zero_of_dvd_exponent_expand (by omega) hℓ hω hmθ hmω,
    ?_⟩
  rintro (hdvd | hp2)
  · exact dvd_exponent_expand_of_dvd_exponent (by omega) hθ hmθ hmω hdvd
  · exact dvd_exponent_of_sq_dvd_coeff_zero hfm hℓ2 hp2 hmω

end RingOfIntegers
