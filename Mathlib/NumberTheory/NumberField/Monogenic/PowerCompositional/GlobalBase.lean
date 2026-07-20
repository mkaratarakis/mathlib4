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

omit [IsIntegrallyClosed R] [PerfectField (R ⧸ Ideal.span {π})] in
/-- **From the ideal criterion to a repeated-factor decomposition, over an arbitrary base.**
If the monic `f` lies in `⟨π, P⟩ ^ 2` for a monic `P` with irreducible reduction, then `f`
admits a decomposition `P ^ 2 q + π (k P) + π ^ 2 c` with `P q` monic of degree `< deg f`.

This is the converse of `saturated_of_forall_notMem_sq`, and it is what makes the criterion
an equivalence rather than a one-way implication.  Dividing `f` by `P ^ 2` leaves a remainder
`r` of small degree which still lies in `⟨π, P⟩ ^ 2`; being of degree below `2 deg P`, such an
`r` is divisible by `π` (`C_dvd_of_mem_sq_of_natDegree_lt`) and its quotient lies in `⟨π, P⟩`
(`mem_span_pair_of_C_mul_mem_sq`), which is exactly the shape required. -/
theorem exists_sq_factor_of_mem_sq (hπ : Prime π) {f : R[X]} (hfm : f.Monic)
    {P : R[X]} (hPm : P.Monic)
    (hPirr : Irreducible (P.map (Ideal.Quotient.mk (Ideal.span {π}))))
    (hfmem : f ∈ (Ideal.span {C π, P} : Ideal (R[X])) ^ 2) :
    ∃ h g k t : R[X], (h * g).Monic ∧ (h * g).natDegree < f.natDegree ∧
      f = h ^ 2 * g + C π * (k * h) + C π ^ 2 * t := by
  have hP0 : P.map (Ideal.Quotient.mk (Ideal.span {π})) ≠ 0 := hPirr.ne_zero
  have hPd : 0 < P.natDegree := by
    rcases Nat.eq_zero_or_pos P.natDegree with h0 | hpos
    · rw [Polynomial.eq_one_of_monic_natDegree_zero hPm h0, Polynomial.map_one] at hPirr
      exact absurd hPirr not_irreducible_one
    · exact hpos
  have hP2m : (P ^ 2).Monic := hPm.pow 2
  set q := f /ₘ P ^ 2 with hqdef
  set r := f %ₘ P ^ 2 with hrdef
  have hdiv : r + P ^ 2 * q = f := modByMonic_add_div f (P ^ 2)
  -- the reduction of `P ^ 2` divides that of `f`, so `2 deg P ≤ deg f`
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
  have hrdegf : r.degree < f.degree := by
    refine (degree_modByMonic_lt _ hP2m).trans_le ?_
    rw [degree_eq_natDegree hP2m.ne_zero, degree_eq_natDegree hfm.ne_zero, hPm.natDegree_pow]
    exact_mod_cast hle
  -- the remainder still lies in the square, and is small
  have hrmem : r ∈ (Ideal.span {C π, P} : Ideal (R[X])) ^ 2 := by
    have hsub : r = f - P ^ 2 * q := by linear_combination hdiv
    rw [hsub]
    refine Ideal.sub_mem _ hfmem (Ideal.mul_mem_right _ _ ?_)
    rw [sq, sq]
    exact Ideal.mul_mem_mul (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
  have hrsmall : r.natDegree < 2 * P.natDegree := by
    have hne1 : P ^ 2 ≠ 1 := fun h => by
      have h0 : (P ^ 2).natDegree = 0 := by rw [h]; simp
      rw [hPm.natDegree_pow] at h0; omega
    have h := natDegree_modByMonic_lt f hP2m hne1
    rwa [hPm.natDegree_pow] at h
  obtain ⟨s, hs⟩ := C_dvd_of_mem_sq_of_natDegree_lt hPm hrmem hrsmall
  obtain ⟨c, k, hck⟩ := Ideal.mem_span_pair.mp
    (mem_span_pair_of_C_mul_mem_sq hπ hP0 (hs ▸ hrmem))
  -- the quotient is monic, and `P q` has the right degree
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

/-- **The local obstruction is global.**  If at some maximal ideal `𝔭` the localised minimal
polynomial lies in `⟨π, P⟩ ^ 2` for a prime `π` of `(𝓞 K)_𝔭` and a monic `P` with irreducible
reduction, then `𝓞 K[θ] ≠ 𝓞 K₁`.

This is the necessity half of Problem 2.  The obstruction lemma over an integrally closed
base produces, from the decomposition of `exists_sq_factor_of_mem_sq`, an element of
`(𝓞 K₁)_𝔭` outside `(𝓞 K)_𝔭[θ]`; and `adjoin_localizedAt_eq_top_of_adjoin_eq_top` says that
`𝓞 K[θ] = 𝓞 K₁` would force the localised equality. -/
theorem adjoin_ne_top_of_localized_mem_sq (𝔭 : Ideal (𝓞 K)) (h𝔭 : 𝔭.IsMaximal)
    {π : Localization 𝔭.primeCompl} (hπ : Prime π)
    {P : (Localization 𝔭.primeCompl)[X]} (hPm : P.Monic)
    (hPirr : Irreducible (P.map (Ideal.Quotient.mk (Ideal.span {π}))))
    (hmem : minpoly (Localization 𝔭.primeCompl)
        (algebraMap (𝓞 K₁) (LocalizedAt (𝓞 K₁) 𝔭) θ) ∈
      (Ideal.span {C π, P} : Ideal ((Localization 𝔭.primeCompl)[X])) ^ 2) :
    Algebra.adjoin (𝓞 K) {θ} ≠ ⊤ := by
  haveI := h𝔭
  haveI := h𝔭.isPrime
  -- the localisations sit inside `K` and `K₁`
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
  -- a prime of the discrete valuation ring `(𝓞 K)_𝔭` generates its maximal ideal
  haveI hm : (Ideal.span {π} : Ideal (Localization 𝔭.primeCompl)).IsMaximal :=
    ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ).isMaximal
      (by simpa [Ideal.span_singleton_eq_bot] using hπ.ne_zero)
  -- the decomposition, and the obstruction it produces
  obtain ⟨h, g, k, t, hW, hdeg, hfeq⟩ :=
    Monogenic.exists_sq_factor_of_mem_sq hπ
      (minpoly.monic (Algebra.IsIntegral.isIntegral _)) hPm hPirr hmem
  have hlocal : Algebra.adjoin (Localization 𝔭.primeCompl)
      {algebraMap (𝓞 K₁) (LocalizedAt (𝓞 K₁) 𝔭) θ} ≠ ⊤ :=
    Monogenic.adjoin_ne_top_of_sq_factor (K := K) (L := K₁) hπ hW hdeg hfeq
  -- so `𝓞 K[θ]` cannot be everything either
  intro htop
  exact hlocal (Monogenic.adjoin_localizedAt_eq_top_of_adjoin_eq_top htop 𝔭)

/-- **Problem 2 of Kaur–Kumar–Remete, solved.**  Let `K ⊆ K₁` be an extension of number
fields, `θ : 𝓞 K₁` a generator of `K₁` over `K`, and suppose the minimal polynomial of `θ`
over `𝓞 K` is `f (X ^ k)` with `f` monic and `k ≥ 2`.  Then

`𝓞 K[θ] = 𝓞 K₁`

**if and only if** at every maximal ideal `𝔭` of `𝓞 K`, for every prime element `π` of the
localisation `(𝓞 K)_𝔭` and `p` the residue characteristic, the image of `f` satisfies

* `π ^ 2 ∤ f (0)`, and
* `π` is not an index divisor of `f (X ^ p)` — of `f` itself when `p ∤ k`.

These are the two conditions of their Theorem 1.1, transported to the localisations.  **No
hypothesis on the class number of `K` appears**: `(𝓞 K)_𝔭` is a discrete valuation ring, so
the prime element the criterion needs exists even where `𝔭` is not principal, and its residue
field `𝓞 K ⧸ 𝔭` is finite, hence perfect.

Sufficiency is `adjoin_eq_top_of_forall_maximal_localized_expand`; necessity comes from
`adjoin_ne_top_of_localized_mem_sq`, since either failing condition places the localised
minimal polynomial in the square of a maximal ideal — the constant-term condition via
`expand_mem_sq_of_sq_dvd_coeff_zero`, whose witness `X` is monic with irreducible
reduction, and the index-divisor condition via `exists_expand_mem_sq_iff`. -/
theorem adjoin_eq_top_iff_forall_maximal_localized_expand
    (hgen : Algebra.adjoin K {(θ : K₁)} = ⊤)
    {f : (𝓞 K)[X]} (hfm : f.Monic) {k : ℕ} (hk : 2 ≤ k)
    (hmin : minpoly (𝓞 K) θ = Polynomial.expand (𝓞 K) k f) :
    Algebra.adjoin (𝓞 K) {θ} = ⊤ ↔
      ∀ (𝔭 : Ideal (𝓞 K)) (h𝔭 : 𝔭.IsMaximal),
        letI := h𝔭.isPrime
        ∀ π : Localization 𝔭.primeCompl, Prime π →
          ∀ (p : ℕ) (_ : Fact p.Prime),
            CharP (Localization 𝔭.primeCompl ⧸ Ideal.span {π}) p →
            ¬ π ^ 2 ∣ (f.map (algebraMap (𝓞 K) (Localization 𝔭.primeCompl))).coeff 0 ∧
            ¬ ∃ g : (Localization 𝔭.primeCompl)[X], g.Monic ∧
              Irreducible (g.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
              Polynomial.expand (Localization 𝔭.primeCompl) (if p ∣ k then p else 1)
                  (f.map (algebraMap (𝓞 K) (Localization 𝔭.primeCompl))) ∈
                (Ideal.span {C π, g} : Ideal ((Localization 𝔭.primeCompl)[X])) ^ 2 := by
  refine ⟨fun htop 𝔭 h𝔭 π hπ p hp hchar => ?_,
    adjoin_eq_top_of_forall_maximal_localized_expand hgen hfm hk hmin⟩
  haveI := h𝔭
  haveI := h𝔭.isPrime
  haveI := hp
  haveI := hchar
  haveI hm : (Ideal.span {π} : Ideal (Localization 𝔭.primeCompl)).IsMaximal :=
    ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ).isMaximal
      (by simpa [Ideal.span_singleton_eq_bot] using hπ.ne_zero)
  -- the residue field is finite, hence perfect
  haveI : Finite (Localization 𝔭.primeCompl ⧸ Ideal.span {π}) := by
    rw [IsLocalRing.eq_maximalIdeal hm]
    exact inferInstanceAs (Finite 𝔭.ResidueField)
  haveI : PerfectField (Localization 𝔭.primeCompl ⧸ Ideal.span {π}) := PerfectField.ofFinite
  -- the localised minimal polynomial is `f (X ^ k)` over `(𝓞 K)_𝔭`
  have hminloc : minpoly (Localization 𝔭.primeCompl)
      (algebraMap (𝓞 K₁) (LocalizedAt (𝓞 K₁) 𝔭) θ) =
      Polynomial.expand (Localization 𝔭.primeCompl) k
        (f.map (algebraMap (𝓞 K) (Localization 𝔭.primeCompl))) := by
    rw [← Polynomial.map_expand, ← hmin, minpoly_map_localization (θ := θ) 𝔭]
  -- either failure would put it in the square of a maximal ideal
  have key : ∀ h : (Localization 𝔭.primeCompl)[X], h.Monic →
      Irreducible (h.map (Ideal.Quotient.mk (Ideal.span {π}))) →
      Polynomial.expand (Localization 𝔭.primeCompl) k
          (f.map (algebraMap (𝓞 K) (Localization 𝔭.primeCompl))) ∈
        (Ideal.span {C π, h} : Ideal ((Localization 𝔭.primeCompl)[X])) ^ 2 → False := by
    intro h hhm hhirr hmem
    exact adjoin_ne_top_of_localized_mem_sq 𝔭 h𝔭 hπ hhm hhirr (hminloc ▸ hmem) htop
  constructor
  · -- the constant-term condition
    intro hdvd
    exact key X monic_X (by simpa using irreducible_X)
      (Monogenic.expand_mem_sq_of_sq_dvd_coeff_zero hk hdvd)
  · -- the index-divisor condition
    rintro ⟨g, hgm, hgirr, hmem⟩
    obtain ⟨h, hhm, hhirr, hmemk⟩ : ∃ h : (Localization 𝔭.primeCompl)[X], h.Monic ∧
        Irreducible (h.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
        Polynomial.expand (Localization 𝔭.primeCompl) k
            (f.map (algebraMap (𝓞 K) (Localization 𝔭.primeCompl))) ∈
          (Ideal.span {C π, h} : Ideal ((Localization 𝔭.primeCompl)[X])) ^ 2 := by
      by_cases hpk : p ∣ k
      · rw [if_pos hpk] at hmem
        exact (Monogenic.exists_expand_mem_sq_iff_of_dvd hπ (hfm.map _) hk hpk).mpr
          (Or.inl ⟨g, hgm, hgirr, hmem⟩)
      · rw [if_neg hpk, expand_one] at hmem
        exact (Monogenic.exists_expand_mem_sq_iff hπ (hfm.map _) hk hpk).mpr
          (Or.inl ⟨g, hgm, hgirr, hmem⟩)
    exact key h hhm hhirr hmemk

end NumberField.Relative
