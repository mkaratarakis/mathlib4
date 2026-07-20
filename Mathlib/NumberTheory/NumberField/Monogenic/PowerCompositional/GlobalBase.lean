/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.Monogenic.PowerCompositional.GeneralBase
public import Mathlib.NumberTheory.NumberField.Monogenic.GlobalCriterion

/-!
# Problem 2 of Kaur–Kumar–Remete: Theorem 1.1 over an arbitrary number field base

This file completes the answer to Problem 2 of

* S. Kaur, S. Kumar, L. Remete, *On the index of power compositional polynomials*,
  Finite Fields Appl. **107** (2025), 102642,

which asks for their Theorem 1.1 over a base other than `ℚ`.

The chain is:

1. `Monogenic.saturated_of_forall_notMem_sq` turns the ideal-theoretic criterion of Section 2
   into `π`-saturation of `R[θ]` in `S`, over an arbitrary integrally closed base.  It is the
   contrapositive of `Monogenic.exists_splitting_of_not_saturated`: a failure of saturation
   produces a splitting `minpoly = A B + π N` with a common irreducible factor modulo `π`,
   and such a splitting places `minpoly` in `⟨π, P⟩ ^ 2`.

2. `Monogenic.saturated_of_expand` feeds that criterion from the Section 2 analysis of
   `f (X ^ k)`, so the hypothesis becomes the two conditions of Theorem 1.1: `π ^ 2` does not
   divide `f (0)`, and `π` is not an index divisor of the relevant expansion of `f`.

3. `NumberField.Relative.minpoly_map_localization` transports the hypothesis `minpoly = f (X ^ k)`
   to the localisation, so the conditions may be stated for `f` over `𝓞 K` itself.

4. `NumberField.Relative.adjoin_eq_top_of_forall_maximal_localized_expand` applies this at the
   uniformiser of `(𝓞 K)_𝔭` for every maximal ideal `𝔭`, and assembles the result with
   `adjoin_eq_top_of_forall_maximal_localized_saturated`.  **No hypothesis on the class
   number of `K`**: the prime element that `𝔭` may fail to provide always exists after
   localising, because `(𝓞 K)_𝔭` is a discrete valuation ring.

The residue field of `(𝓞 K)_𝔭` is `𝓞 K ⧸ 𝔭`, which is finite and hence perfect, so the
perfectness hypothesis of Section 2 is discharged automatically here.
-/

@[expose] public section

noncomputable section

open Polynomial NumberField Monogenic

namespace Monogenic

section Saturation

attribute [local instance] Ideal.Quotient.field

variable {R S : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [CommRing S] [IsDomain S] [Algebra R S] [Module.IsTorsionFree R S] [FaithfulSMul R S]
  [Algebra.IsIntegral R S] {θ : S} {π : R}

/-- **The ideal criterion gives saturation, over an integrally closed base.**  If the minimal
polynomial of `θ` lies outside `⟨π, P⟩ ^ 2` for every monic `P` with irreducible reduction,
then `R[θ]` is `π`-saturated in `S`: `π β ∈ R[θ]` forces `β ∈ R[θ]`.

This is the contrapositive of `Monogenic.exists_splitting_of_not_saturated`.  A failure of
saturation yields a splitting `minpoly = A B + π N` in which one monic irreducible `Pi` of
`(R ⧸ (π))[X]` divides all three reductions; lifting `Pi` to a monic `P`, each of `A`, `B`
and `N` lies in `⟨π, P⟩`, so `A B` lies in `⟨π, P⟩ ^ 2` and `π N` lies in
`⟨π⟩ * ⟨π, P⟩ ⊆ ⟨π, P⟩ ^ 2`. -/
theorem saturated_of_forall_notMem_sq (hπ0 : π ≠ 0)
    (hmax : (Ideal.span {π} : Ideal R).IsMaximal)
    (hcrit : ∀ P : R[X], P.Monic →
      Irreducible (P.map (Ideal.Quotient.mk (Ideal.span {π}))) →
      minpoly R θ ∉ (Ideal.span {C π, P} : Ideal (R[X])) ^ 2) :
    ∀ y : S, algebraMap R S π * y ∈ Algebra.adjoin R {θ} → y ∈ Algebra.adjoin R {θ} := by
  haveI := hmax
  intro y hy
  by_contra hynot
  obtain ⟨Pi, A, B, N, hPim, hPiirr, hsplit, hPiA, hPiB, hPiN⟩ :=
    exists_splitting_of_not_saturated hπ0 hmax hynot hy
  -- lift the common irreducible factor to a monic `P` over `R`
  obtain ⟨P, hPmap, -, hPm⟩ := lifts_and_degree_eq_and_monic
    ((mem_lifts Pi).mpr (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective Pi)) hPim
  refine hcrit P hPm (by rw [hPmap]; exact hPiirr) ?_
  -- the splitting places the minimal polynomial in `⟨π, P⟩ ^ 2`
  rw [hsplit, sq]
  exact Ideal.add_mem _
    (Ideal.mul_mem_mul (mem_span_pair_iff_map_dvd.mpr (hPmap ▸ hPiA))
      (mem_span_pair_iff_map_dvd.mpr (hPmap ▸ hPiB)))
    (Ideal.mul_mem_mul (Ideal.subset_span (by simp))
      (mem_span_pair_iff_map_dvd.mpr (hPmap ▸ hPiN)))

variable [hmax : (Ideal.span {π} : Ideal R).IsMaximal]
  [PerfectField (R ⧸ Ideal.span {π})]

/-- **Theorem 1.1 of Kaur–Kumar–Remete at a prime element, over an arbitrary base.**  Let
`θ` have minimal polynomial `f (X ^ k)` over `R`, let `π` be a prime element of `R` and `p`
the characteristic of the residue field.  If `π ^ 2` does not divide `f (0)` and `π` is not
an index divisor of `f (X ^ p)` — respectively of `f` itself, when `p` does not divide `k` —
then `R[θ]` is `π`-saturated in `S`.

Only the radical of `k` enters, through whether `p` divides `k`; this is the content of
Corollary 2.5, which `exists_expand_mem_sq_iff` and `exists_expand_mem_sq_iff_of_dvd`
package. -/
theorem saturated_of_expand (hπ : Prime π) {p : ℕ} [Fact p.Prime]
    [CharP (R ⧸ Ideal.span {π}) p] {f : R[X]} (hfm : f.Monic) {k : ℕ} (hk : 2 ≤ k)
    (hmin : minpoly R θ = Polynomial.expand R k f)
    (hcoeff : ¬ π ^ 2 ∣ f.coeff 0)
    (hnid : ¬ ∃ g : R[X], g.Monic ∧
      Irreducible (g.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
      Polynomial.expand R (if p ∣ k then p else 1) f ∈
        (Ideal.span {C π, g} : Ideal (R[X])) ^ 2) :
    ∀ y : S, algebraMap R S π * y ∈ Algebra.adjoin R {θ} → y ∈ Algebra.adjoin R {θ} := by
  refine saturated_of_forall_notMem_sq hπ.ne_zero ‹(Ideal.span {π} : Ideal R).IsMaximal›
    fun P hPm hPirr hmem => hnid ?_
  rw [hmin] at hmem
  by_cases hpk : p ∣ k
  · rw [if_pos hpk]
    exact ((exists_expand_mem_sq_iff_of_dvd hπ hfm hk hpk).mp ⟨P, hPm, hPirr, hmem⟩).resolve_right
      hcoeff
  · rw [if_neg hpk, expand_one]
    exact ((exists_expand_mem_sq_iff hπ hfm hk hpk).mp ⟨P, hPm, hPirr, hmem⟩).resolve_right hcoeff

end Saturation

end Monogenic

namespace NumberField.Relative

open IsLocalization

attribute [local instance] Ideal.Quotient.field

variable {K K₁ : Type*} [Field K] [NumberField K] [Field K₁] [NumberField K₁]
  [Algebra K K₁] {θ : 𝓞 K₁}

/-- **The minimal polynomial transfers to the localisation.**  The minimal polynomial of `θ`
over `(𝓞 K)_𝔭` is the image of its minimal polynomial over `𝓞 K`.

This is `Monogenic.minpoly_map_eq_minpoly` — the minimal polynomial is insensitive to
enlarging an integrally closed base inside its fraction field — applied to
`𝓞 K ⊆ (𝓞 K)_𝔭`, both with fraction field `K`.  It is stated for `θ` viewed in `K₁`, which
is where the two bases meet; `minpoly.algebraMap_eq` then moves it to `(𝓞 K₁)_𝔭`. -/
theorem minpoly_map_localization (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] :
    (minpoly (𝓞 K) θ).map (algebraMap (𝓞 K) (Localization 𝔭.primeCompl)) =
      minpoly (Localization 𝔭.primeCompl)
        (algebraMap (𝓞 K₁) (LocalizedAt (𝓞 K₁) 𝔭) θ) := by
  -- `(𝓞 K)_𝔭` sits between `𝓞 K` and `K`, with `K` as its fraction field
  letI : Algebra (Localization 𝔭.primeCompl) K :=
    localizationAlgebraOfSubmonoidLe _ _ 𝔭.primeCompl (nonZeroDivisors (𝓞 K))
      𝔭.primeCompl_le_nonZeroDivisors
  haveI : IsScalarTower (𝓞 K) (Localization 𝔭.primeCompl) K :=
    localization_isScalarTower_of_submonoid_le _ _ _ _ 𝔭.primeCompl_le_nonZeroDivisors
  haveI : IsFractionRing (Localization 𝔭.primeCompl) K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      𝔭.primeCompl (Localization 𝔭.primeCompl) K
  have hle := algebraMapSubmonoid_primeCompl_le_nonZeroDivisors (K₁ := K₁) 𝔭
  letI : Algebra (LocalizedAt (𝓞 K₁) 𝔭) K₁ :=
    localizationAlgebraOfSubmonoidLe _ _ _ (nonZeroDivisors (𝓞 K₁)) hle
  haveI : IsScalarTower (𝓞 K₁) (LocalizedAt (𝓞 K₁) 𝔭) K₁ :=
    localization_isScalarTower_of_submonoid_le _ _ _ _ hle
  haveI : IsFractionRing (LocalizedAt (𝓞 K₁) 𝔭) K₁ :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Algebra.algebraMapSubmonoid (𝓞 K₁) 𝔭.primeCompl) (LocalizedAt (𝓞 K₁) 𝔭) K₁
  letI : Algebra (Localization 𝔭.primeCompl) K₁ :=
    ((algebraMap K K₁).comp (algebraMap (Localization 𝔭.primeCompl) K)).toAlgebra
  haveI : IsScalarTower (Localization 𝔭.primeCompl) K K₁ :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower (𝓞 K) (Localization 𝔭.primeCompl) K₁ :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra, RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq,
        ← IsScalarTower.algebraMap_eq])
  haveI : IsScalarTower (𝓞 K) (LocalizedAt (𝓞 K₁) 𝔭) K₁ := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    rw [IsScalarTower.algebraMap_eq (𝓞 K) (𝓞 K₁) (LocalizedAt (𝓞 K₁) 𝔭), ← RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq (𝓞 K₁) (LocalizedAt (𝓞 K₁) 𝔭) K₁,
      ← IsScalarTower.algebraMap_eq]
  haveI : IsScalarTower (Localization 𝔭.primeCompl) (LocalizedAt (𝓞 K₁) 𝔭) K₁ := by
    refine IsScalarTower.of_algebraMap_eq' (IsLocalization.ringHom_ext 𝔭.primeCompl ?_)
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
    exact IsScalarTower.algebraMap_eq (𝓞 K) (LocalizedAt (𝓞 K₁) 𝔭) K₁
  -- both sides equal the minimal polynomial of `θ` viewed in `K₁`
  have hinjS : Function.Injective (algebraMap (LocalizedAt (𝓞 K₁) 𝔭) K₁) :=
    FaithfulSMul.algebraMap_injective _ _
  have hint : IsIntegral (𝓞 K) ((θ : K₁)) :=
    (IsIntegral.tower_top (R := ℤ) θ.isIntegral).map (IsScalarTower.toAlgHom (𝓞 K) (𝓞 K₁) K₁)
  rw [← minpoly.algebraMap_eq hinjS, ← IsScalarTower.algebraMap_apply,
    ← minpoly.algebraMap_eq (FaithfulSMul.algebraMap_injective (𝓞 K₁) K₁),
    ← Monogenic.minpoly_map_eq_minpoly (R := 𝓞 K) (R' := Localization 𝔭.primeCompl)
      (K := K) (S := K₁) hint,
    minpoly.algebraMap_eq (FaithfulSMul.algebraMap_injective (𝓞 K₁) K₁)]

/-- **Theorem 1.1 of Kaur–Kumar–Remete over an arbitrary number field base.**  Let `K ⊆ K₁`
be an extension of number fields, `θ : 𝓞 K₁` a generator of `K₁` over `K`, and suppose the
minimal polynomial of `θ` over `𝓞 K` is `f (X ^ k)` with `f` monic and `k ≥ 2`.

If at every maximal ideal `𝔭` of `𝓞 K`, for every prime element `π` of `(𝓞 K)_𝔭` and `p` the
residue characteristic, the image of `f` in `(𝓞 K)_𝔭[X]` satisfies

* `π ^ 2 ∤ f (0)`, and
* `π` is not an index divisor of `f (X ^ p)` — of `f` itself when `p ∤ k` —

then `𝓞 K[θ] = 𝓞 K₁`.

**This answers Problem 2 of Kaur–Kumar–Remete, with no hypothesis on the class number of
`K`.**  The two conditions are theirs, transported to the localisation: `(𝓞 K)_𝔭` is a
discrete valuation ring, so the prime element the criterion needs exists even when `𝔭` is not
principal in `𝓞 K`, and its residue field is `𝓞 K ⧸ 𝔭` — finite, hence perfect, which
discharges the standing hypothesis of Section 2.  Only the radical of `k` enters, through
whether `p` divides `k`. -/
theorem adjoin_eq_top_of_forall_maximal_localized_expand
    (hgen : Algebra.adjoin K {(θ : K₁)} = ⊤)
    {f : (𝓞 K)[X]} (hfm : f.Monic) {k : ℕ} (hk : 2 ≤ k)
    (hmin : minpoly (𝓞 K) θ = Polynomial.expand (𝓞 K) k f)
    (hcond : ∀ (𝔭 : Ideal (𝓞 K)) (h𝔭 : 𝔭.IsMaximal),
      letI := h𝔭.isPrime
      ∀ π : Localization 𝔭.primeCompl, Prime π →
        ∀ (p : ℕ) (_ : Fact p.Prime),
          CharP (Localization 𝔭.primeCompl ⧸ Ideal.span {π}) p →
          ¬ π ^ 2 ∣ (f.map (algebraMap (𝓞 K) (Localization 𝔭.primeCompl))).coeff 0 ∧
          ¬ ∃ g : (Localization 𝔭.primeCompl)[X], g.Monic ∧
            Irreducible (g.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
            Polynomial.expand (Localization 𝔭.primeCompl) (if p ∣ k then p else 1)
                (f.map (algebraMap (𝓞 K) (Localization 𝔭.primeCompl))) ∈
              (Ideal.span {C π, g} : Ideal ((Localization 𝔭.primeCompl)[X])) ^ 2) :
    Algebra.adjoin (𝓞 K) {θ} = ⊤ := by
  refine adjoin_eq_top_of_forall_maximal_localized_saturated hgen fun 𝔭 h𝔭 => ?_
  haveI := h𝔭
  haveI := h𝔭.isPrime
  intro π hπ
  -- a prime of the discrete valuation ring `(𝓞 K)_𝔭` generates its maximal ideal
  haveI hm : (Ideal.span {π} : Ideal (Localization 𝔭.primeCompl)).IsMaximal :=
    ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ).isMaximal
      (by simpa [Ideal.span_singleton_eq_bot] using hπ.ne_zero)
  -- the residue field is `𝓞 K ⧸ 𝔭`: finite, hence perfect, of prime characteristic
  haveI : Finite (Localization 𝔭.primeCompl ⧸ Ideal.span {π}) := by
    rw [IsLocalRing.eq_maximalIdeal hm]
    exact inferInstanceAs (Finite 𝔭.ResidueField)
  haveI : PerfectField (Localization 𝔭.primeCompl ⧸ Ideal.span {π}) := PerfectField.ofFinite
  obtain ⟨p, hchar⟩ := CharP.exists (Localization 𝔭.primeCompl ⧸ Ideal.span {π})
  haveI := hchar
  haveI : Fact p.Prime := ⟨CharP.char_is_prime (Localization 𝔭.primeCompl ⧸ Ideal.span {π}) p⟩
  obtain ⟨hcoeff, hnid⟩ := hcond 𝔭 h𝔭 π hπ p inferInstance hchar
  refine Monogenic.saturated_of_expand hπ (hfm.map _) hk ?_ hcoeff hnid
  rw [← Polynomial.map_expand, ← hmin]
  exact (minpoly_map_localization (θ := θ) 𝔭).symm

end NumberField.Relative
