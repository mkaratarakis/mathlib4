/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.Monogenic.Relative

/-!
# Dedekind's criterion over an integrally closed base

The relative results of `Mathlib/NumberTheory/NumberField/Monogenic/Relative.lean` are stated
for the ring of integers of a number field.  This file restates the existence half of
Dedekind's argument for an arbitrary integrally closed base `R`, with `S` integral over `R`
and `π` an element generating a maximal ideal.

The point of the generality is localisation: `𝓞 K` localised at a maximal ideal `𝔭` is a
discrete valuation ring, in which `𝔭` becomes principal, so the criterion becomes available
at maximal ideals that are not principal in `𝓞 K` itself.  That is the one remaining
obstruction to the relative theory over a base of class number greater than one.

## Main results

* `Monogenic.exists_splitting_of_not_saturated`: if `R[θ]` fails to be `π`-saturated in `S`,
  the minimal polynomial of `θ` admits a splitting `f = A B + π N` in which a single monic
  irreducible of `(R ⧸ (π))[X]` divides the reductions of `A`, `B` and `N`.
-/

@[expose] public section

noncomputable section

open Polynomial NumberField.Relative

namespace Monogenic

attribute [local instance] Ideal.Quotient.field

variable {R S : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
variable [CommRing S] [IsDomain S] [Algebra R S] [Module.IsTorsionFree R S] [FaithfulSMul R S]
variable [Algebra.IsIntegral R S] {θ : S}

section Localisation

/-- **The minimal polynomial is insensitive to enlarging an integrally closed base inside its
fraction field.**  If `R ⊆ R'` are integrally closed domains with the same fraction field `K`
and `θ` is integral over `R`, then the minimal polynomial of `θ` over `R'` is the image of the
one over `R`.

The case of interest is `R' = R` localised at a maximal ideal: the hypotheses of the
criterion, which are statements about `minpoly R θ`, transfer unchanged to the localisation. -/
theorem minpoly_map_eq_minpoly {R R' K S : Type*}
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing R'] [IsDomain R'] [IsIntegrallyClosed R']
    [Field K] [CommRing S] [IsDomain S]
    [Algebra R R'] [Algebra R K] [Algebra R' K] [IsScalarTower R R' K]
    [IsFractionRing R K] [IsFractionRing R' K]
    [Algebra R S] [Algebra R' S] [IsScalarTower R R' S]
    [Algebra K S] [IsScalarTower R K S] [IsScalarTower R' K S]
    {θ : S} (hθ : IsIntegral R θ) :
    (minpoly R θ).map (algebraMap R R') = minpoly R' θ := by
  have hθ' : IsIntegral R' θ := hθ.tower_top
  have h1 : minpoly K θ = (minpoly R θ).map (algebraMap R K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' K hθ
  have h2 : minpoly K θ = (minpoly R' θ).map (algebraMap R' K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' K hθ'
  have h3 : ((minpoly R θ).map (algebraMap R R')).map (algebraMap R' K)
      = (minpoly R θ).map (algebraMap R K) := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  refine Polynomial.map_injective (algebraMap R' K)
    (FaithfulSMul.algebraMap_injective R' K) ?_
  rw [h3, ← h1, h2]

end Localisation

/-- **The existence half of Dedekind's argument over an integrally closed base.**  If some
`β ∉ R[θ]` has `π β ∈ R[θ]`, then the minimal polynomial of `θ` admits a splitting
`f = A B + π N` in which a single monic irreducible of `(R ⧸ (π))[X]` divides the reductions
of `A`, `B` and `N`.

This is `NumberField.Relative.exists_splitting_of_not_saturated` with the ring of integers of
a number field replaced by an arbitrary integrally closed base; the argument is unchanged,
only the provenance of the integrality facts differs. -/
theorem exists_splitting_of_not_saturated {π : R} (hπ0 : π ≠ 0)
    (hmax : (Ideal.span {π} : Ideal R).IsMaximal) {β : S}
    (hβnot : β ∉ Algebra.adjoin R {θ})
    (hβ : algebraMap R S π * β ∈ Algebra.adjoin R {θ}) :
    ∃ (Pi : (R ⧸ Ideal.span {π})[X]) (A B N : R[X]), Pi.Monic ∧ Irreducible Pi ∧
      minpoly R θ = A * B + C π * N ∧
      Pi ∣ A.map (Ideal.Quotient.mk (Ideal.span {π})) ∧
      Pi ∣ B.map (Ideal.Quotient.mk (Ideal.span {π})) ∧
      Pi ∣ N.map (Ideal.Quotient.mk (Ideal.span {π})) := by
  classical
  haveI := hmax
  have hint : IsIntegral R θ := Algebra.IsIntegral.isIntegral θ
  have hsurj : Function.Surjective (Ideal.Quotient.mk (Ideal.span {π} : Ideal R)) :=
    Ideal.Quotient.mk_surjective
  have hzπ : Ideal.Quotient.mk (Ideal.span {π}) π = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self π)
  have hπι0 : algebraMap R S π ≠ 0 := fun h0 =>
    hπ0 (FaithfulSMul.algebraMap_injective R S (by simpa using h0))
  have hfm : (minpoly R θ).Monic := minpoly.monic hint
  -- the numerator polynomial `r` of degree `< deg f`
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hβ
  obtain ⟨c, hc⟩ := hβ
  set r := c %ₘ minpoly R θ with hrdef
  have hc' : aeval θ c = algebraMap R S π * β := hc
  have hrθ : aeval θ r = algebraMap R S π * β := by
    have hdivmod := modByMonic_add_div c (minpoly R θ)
    have := congrArg (aeval θ) hdivmod
    rw [map_add, map_mul, minpoly.aeval, zero_mul, add_zero] at this
    rw [← hc', ← this]
  have hr0 : r.map (Ideal.Quotient.mk (Ideal.span {π})) ≠ 0 := by
    intro h0
    obtain ⟨r', hr'⟩ := map_quotient_span_eq_zero_iff.mp h0
    apply hβnot
    have hcalc : algebraMap R S π * aeval θ r'
        = algebraMap R S π * β := by
      rw [← hrθ, hr']
      simp [aeval_C, mul_comm]
    have := mul_left_cancel₀ hπι0 hcalc
    rw [← this, Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨r', rfl⟩
  have hrne : r ≠ 0 := fun h0 => hr0 (by rw [h0, Polynomial.map_zero])
  have hrdeg : r.natDegree < (minpoly R θ).natDegree :=
    natDegree_lt_natDegree hrne (degree_modByMonic_lt c hfm)
  -- the gcd `Ā` and a lift `A` with `A(θ) = π γ`
  set rbar := r.map (Ideal.Quotient.mk (Ideal.span {π})) with hrbar
  set fbar := (minpoly R θ).map (Ideal.Quotient.mk (Ideal.span {π})) with hfbar
  set Abar := EuclideanDomain.gcd rbar fbar with hAbardef
  have hAdvd_r : Abar ∣ rbar := EuclideanDomain.gcd_dvd_left _ _
  have hAdvd_f : Abar ∣ fbar := EuclideanDomain.gcd_dvd_right _ _
  have hA0 : Abar ≠ 0 := fun h0 => hr0 (EuclideanDomain.gcd_eq_zero_iff.mp h0).1
  have hf0 : fbar ≠ 0 := (hfm.map _).ne_zero
  obtain ⟨A, hAmap⟩ := Polynomial.map_surjective _ hsurj Abar
  obtain ⟨u, humap⟩ := Polynomial.map_surjective _ hsurj (EuclideanDomain.gcdA rbar fbar)
  obtain ⟨v, hvmap⟩ := Polynomial.map_surjective _ hsurj (EuclideanDomain.gcdB rbar fbar)
  have hkey : (A - (r * u + minpoly R θ * v)).map
      (Ideal.Quotient.mk (Ideal.span {π})) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
      hAmap, humap, hvmap, ← hrbar, ← hfbar, ← EuclideanDomain.gcd_eq_gcd_ab, ← hAbardef,
      sub_self]
  obtain ⟨w, hw⟩ := map_quotient_span_eq_zero_iff.mp hkey
  set γ : S := β * aeval θ u + aeval θ w with hγdef
  have hAθ : aeval θ A = algebraMap R S π * γ := by
    have hAeq : A = r * u + minpoly R θ * v + C π * w := by linear_combination hw
    rw [hAeq]
    simp only [map_add, map_mul, minpoly.aeval, zero_mul, add_zero, aeval_C, hrθ]
    rw [hγdef]
    ring
  -- scaled minimal polynomial of `γ` gives `Ā ^ d = f̄ k̄`
  have hγint : IsIntegral R γ := Algebra.IsIntegral.isIntegral γ
  set q := minpoly R γ with hqdef
  have hqm : q.Monic := minpoly.monic hγint
  set d := q.natDegree with hddef
  have hd1 : 0 < d := minpoly.natDegree_pos hγint
  have hP0 : aeval θ ((q.scaleRoots π).comp A) = 0 := by
    rw [aeval_comp, hAθ]
    exact scaleRoots_aeval_eq_zero (minpoly.aeval R γ)
  have hfP : minpoly R θ ∣ (q.scaleRoots π).comp A :=
    minpoly.isIntegrallyClosed_dvd hint hP0
  have hscale : (q.scaleRoots π).map (Ideal.Quotient.mk (Ideal.span {π})) = X ^ d := by
    ext i
    rw [coeff_map, coeff_scaleRoots, ← hddef, coeff_X_pow, map_mul, map_pow, hzπ]
    rcases lt_trichotomy i d with hlt | heq | hgt
    · rw [if_neg hlt.ne]
      have hne : d - i ≠ 0 := Nat.sub_ne_zero_of_lt hlt
      rw [zero_pow hne, mul_zero]
    · rw [if_pos heq]
      have hcd : q.coeff i = 1 := by rw [heq, hddef]; exact hqm.coeff_natDegree
      have hdi : d - i = 0 := by omega
      rw [hcd, hdi, pow_zero, mul_one, map_one]
    · rw [if_neg hgt.ne']
      have hc0 : q.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (hddef ▸ hgt)
      rw [hc0, map_zero, zero_mul]
  have hkdvd : fbar ∣ Abar ^ d := by
    have := Polynomial.map_dvd (Ideal.Quotient.mk (Ideal.span {π})) hfP
    rwa [Polynomial.map_comp, hscale, hAmap, X_pow_comp, ← hfbar] at this
  obtain ⟨k, hk⟩ := hkdvd
  -- the complementary factor `B̄` and a monic irreducible factor `π̄` of it
  obtain ⟨Bbar, hBbar⟩ := id hAdvd_f
  have hB0 : Bbar ≠ 0 := fun h0 => hf0 (by rw [hBbar, h0, mul_zero])
  have hdegA : Abar.natDegree < fbar.natDegree := by
    have h1 : Abar.natDegree ≤ rbar.natDegree := natDegree_le_of_dvd hAdvd_r hr0
    have h2 : rbar.natDegree ≤ r.natDegree := natDegree_map_le
    have h3 : fbar.natDegree = (minpoly R θ).natDegree := hfm.natDegree_map _
    omega
  have hBunit : ¬ IsUnit Bbar := by
    intro hu
    have hdeg : fbar.natDegree = Abar.natDegree := by
      rw [hBbar, natDegree_mul hA0 hB0, natDegree_eq_zero_of_isUnit hu, add_zero]
    omega
  obtain ⟨π₀, hπ₀irr, hπ₀dvd⟩ := WfDvdMonoid.exists_irreducible_factor hBunit hB0
  set πb := normalize π₀ with hπbdef
  have hπbirr : Irreducible πb := (associated_normalize π₀).irreducible hπ₀irr
  have hπbmonic : πb.Monic := monic_normalize hπ₀irr.ne_zero
  have hπbB : πb ∣ Bbar := by
    rw [hπbdef, normalize_dvd_iff]
    exact hπ₀dvd
  have hcancel : Abar ^ (d - 1) = Bbar * k := by
    apply mul_left_cancel₀ hA0
    have hpow : Abar * Abar ^ (d - 1) = Abar ^ d := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hpow, hk, hBbar]
    ring
  have hπbA : πb ∣ Abar := by
    rcases Nat.lt_or_ge d 2 with hlt | hge
    · exfalso
      have hd_eq : d = 1 := by omega
      rw [hd_eq] at hcancel
      simp only [Nat.sub_self, pow_zero] at hcancel
      exact hBunit (isUnit_of_dvd_one ⟨k, hcancel⟩)
    · have hπpow : πb ∣ Abar ^ (d - 1) := hcancel ▸ hπbB.mul_right k
      exact hπbirr.prime.dvd_of_dvd_pow hπpow
  have hπbf : πb ∣ fbar := hπbA.trans hAdvd_f
  obtain ⟨B, hBmap⟩ := Polynomial.map_surjective _ hsurj Bbar
  have hN0 : (minpoly R θ - A * B).map (Ideal.Quotient.mk (Ideal.span {π})) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_mul, hAmap, hBmap, ← hfbar, ← hBbar, sub_self]
  obtain ⟨N, hN⟩ := map_quotient_span_eq_zero_iff.mp hN0
  have hNθ : aeval θ N = -(γ * aeval θ B) := by
    apply mul_left_cancel₀ hπι0
    have hh0 := congrArg (aeval θ) hN
    simp only [map_sub, map_mul, minpoly.aeval, zero_sub, aeval_C] at hh0
    linear_combination -hh0 - aeval θ B * hAθ
  set Q : R[X] := ∑ i ∈ Finset.range (d + 1), C (q.coeff i) * B ^ (d - i) * (-N) ^ i
    with hQdef
  have hQθ : aeval θ Q = 0 := by
    rw [hQdef, map_sum]
    have hterm : ∀ i ∈ Finset.range (d + 1),
        aeval θ (C (q.coeff i) * B ^ (d - i) * (-N) ^ i) =
          algebraMap R S (q.coeff i) * γ ^ i * (aeval θ B) ^ d := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hile : i ≤ d := by omega
      rw [map_mul, map_mul, map_pow, map_pow, map_neg, hNθ, neg_neg, aeval_C, mul_pow]
      have hBpow : (aeval θ B) ^ (d - i) * (aeval θ B) ^ i = (aeval θ B) ^ d :=
        pow_sub_mul_pow (aeval θ B) hile
      calc algebraMap R S (q.coeff i) * (aeval θ B) ^ (d - i)
            * (γ ^ i * (aeval θ B) ^ i)
          = algebraMap R S (q.coeff i) * γ ^ i *
            ((aeval θ B) ^ (d - i) * (aeval θ B) ^ i) := by ring
        _ = algebraMap R S (q.coeff i) * γ ^ i * (aeval θ B) ^ d := by
            rw [hBpow]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
    have hsum := (aeval_eq_sum_range (R := R) (p := q) γ).symm
    simp only [Algebra.smul_def] at hsum
    rw [hsum, minpoly.aeval, zero_mul]
  have hfQ : minpoly R θ ∣ Q := minpoly.isIntegrallyClosed_dvd hint hQθ
  have hπbN : πb ∣ N.map (Ideal.Quotient.mk (Ideal.span {π})) := by
    have hπbQ : πb ∣ Q.map (Ideal.Quotient.mk (Ideal.span {π})) :=
      hπbf.trans (Polynomial.map_dvd _ hfQ)
    have hQmap : Q.map (Ideal.Quotient.mk (Ideal.span {π})) =
        ∑ i ∈ Finset.range (d + 1),
          C (Ideal.Quotient.mk (Ideal.span {π}) (q.coeff i)) * Bbar ^ (d - i) *
            (-(N.map (Ideal.Quotient.mk (Ideal.span {π})))) ^ i := by
      rw [hQdef, Polynomial.map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow,
        Polynomial.map_neg, map_C, hBmap]
    have hcd : q.coeff d = 1 := by rw [hddef]; exact hqm.coeff_natDegree
    have hsplit : Q.map (Ideal.Quotient.mk (Ideal.span {π})) =
        (-(N.map (Ideal.Quotient.mk (Ideal.span {π})))) ^ d +
          ∑ i ∈ Finset.range d,
            C (Ideal.Quotient.mk (Ideal.span {π}) (q.coeff i)) * Bbar ^ (d - i) *
              (-(N.map (Ideal.Quotient.mk (Ideal.span {π})))) ^ i := by
      rw [hQmap, Finset.sum_range_succ, hcd, map_one, map_one, Nat.sub_self, pow_zero]
      ring
    have hπbsum : πb ∣ ∑ i ∈ Finset.range d,
        C (Ideal.Quotient.mk (Ideal.span {π}) (q.coeff i)) * Bbar ^ (d - i) *
          (-(N.map (Ideal.Quotient.mk (Ideal.span {π})))) ^ i := by
      refine Finset.dvd_sum fun i hi => ?_
      rw [Finset.mem_range] at hi
      have : πb ∣ Bbar ^ (d - i) := hπbB.trans (dvd_pow_self Bbar (Nat.sub_ne_zero_of_lt hi))
      exact ((this.mul_left _).mul_right _)
    have hπbpow : πb ∣ (-(N.map (Ideal.Quotient.mk (Ideal.span {π})))) ^ d := by
      have := dvd_sub hπbQ hπbsum
      rw [hsplit, add_sub_cancel_right] at this
      exact this
    have := hπbirr.prime.dvd_of_dvd_pow hπbpow
    rwa [dvd_neg] at this
  exact ⟨πb, A, B, N, hπbmonic, hπbirr, by linear_combination hN,
    by rw [hAmap]; exact hπbA, by rw [hBmap]; exact hπbB, hπbN⟩


private theorem map_dvd_map_sub_of_map_dvd {R : Type*} [CommRing R] [IsDomain R]
    {π : R} (hπ : Prime π) {Pi A B g h N M : R[X]} (hPi : Pi.Monic)
    (hid : A * B + C π * N = g * h + C π * M)
    (hA : Pi.map (Ideal.Quotient.mk (Ideal.span {π}))
      ∣ A.map (Ideal.Quotient.mk (Ideal.span {π})))
    (hB : Pi.map (Ideal.Quotient.mk (Ideal.span {π}))
      ∣ B.map (Ideal.Quotient.mk (Ideal.span {π})))
    (hg : Pi.map (Ideal.Quotient.mk (Ideal.span {π}))
      ∣ g.map (Ideal.Quotient.mk (Ideal.span {π})))
    (hh : Pi.map (Ideal.Quotient.mk (Ideal.span {π}))
      ∣ h.map (Ideal.Quotient.mk (Ideal.span {π}))) :
    Pi.map (Ideal.Quotient.mk (Ideal.span {π})) ∣
      M.map (Ideal.Quotient.mk (Ideal.span {π}))
        - N.map (Ideal.Quotient.mk (Ideal.span {π})) := by
  haveI hprime : (Ideal.span {π} : Ideal R).IsPrime :=
    (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  haveI : IsDomain (R ⧸ Ideal.span {π}) := Ideal.Quotient.isDomain _
  have hp0 : (C π : R[X]) ≠ 0 := fun h0 => hπ.ne_zero (C_eq_zero.mp h0)
  have hzπ : Ideal.Quotient.mk (Ideal.span {π}) π = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self π)
  have key : ∀ X : R[X], Pi.map (Ideal.Quotient.mk (Ideal.span {π}))
      ∣ X.map (Ideal.Quotient.mk (Ideal.span {π})) →
      ∃ X₁ X₂ : R[X], X = Pi * X₁ + C π * X₂ := by
    intro X hX
    have h0 : (X %ₘ Pi).map (Ideal.Quotient.mk (Ideal.span {π})) = 0 := by
      rw [map_modByMonic _ hPi, (modByMonic_eq_zero_iff_dvd (hPi.map _)).mpr hX]
    obtain ⟨X₂, hX₂⟩ := map_quotient_span_eq_zero_iff.mp h0
    exact ⟨X /ₘ Pi, X₂, by linear_combination hX₂ - modByMonic_add_div X Pi⟩
  obtain ⟨A₁, A₂, hA'⟩ := key A hA
  obtain ⟨B₁, B₂, hB'⟩ := key B hB
  obtain ⟨g₁, g₂, hg'⟩ := key g hg
  obtain ⟨h₁, h₂, hh'⟩ := key h hh
  rw [hA', hB', hg', hh'] at hid
  have h1 : Pi ^ 2 * (A₁ * B₁ - g₁ * h₁) =
      C π * (Pi * (g₁ * h₂ + g₂ * h₁ - A₁ * B₂ - A₂ * B₁) +
        C π * (g₂ * h₂ - A₂ * B₂) + (M - N)) := by
    linear_combination hid
  have hPine : Pi.map (Ideal.Quotient.mk (Ideal.span {π})) ≠ 0 := (hPi.map _).ne_zero
  have h2 : (A₁ * B₁ - g₁ * h₁).map (Ideal.Quotient.mk (Ideal.span {π})) = 0 := by
    have := congrArg (Polynomial.map (Ideal.Quotient.mk (Ideal.span {π}))) h1
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add, map_C, hzπ,
      map_zero, zero_mul] at this
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h') hPine
    · exact h'
  obtain ⟨W, hW⟩ := map_quotient_span_eq_zero_iff.mp h2
  have h3 : Pi ^ 2 * W =
      Pi * (g₁ * h₂ + g₂ * h₁ - A₁ * B₂ - A₂ * B₁) +
        C π * (g₂ * h₂ - A₂ * B₂) + (M - N) := by
    apply mul_left_cancel₀ hp0
    linear_combination h1 - Pi ^ 2 * hW
  have h4 : M.map (Ideal.Quotient.mk (Ideal.span {π}))
        - N.map (Ideal.Quotient.mk (Ideal.span {π})) =
      (Pi.map (Ideal.Quotient.mk (Ideal.span {π}))) ^ 2
          * (W.map (Ideal.Quotient.mk (Ideal.span {π}))) -
        (Pi.map (Ideal.Quotient.mk (Ideal.span {π}))) *
          (g₁.map (Ideal.Quotient.mk (Ideal.span {π}))
              * h₂.map (Ideal.Quotient.mk (Ideal.span {π})) +
            g₂.map (Ideal.Quotient.mk (Ideal.span {π}))
              * h₁.map (Ideal.Quotient.mk (Ideal.span {π})) -
            A₁.map (Ideal.Quotient.mk (Ideal.span {π}))
              * B₂.map (Ideal.Quotient.mk (Ideal.span {π})) -
            A₂.map (Ideal.Quotient.mk (Ideal.span {π}))
              * B₁.map (Ideal.Quotient.mk (Ideal.span {π}))) := by
    have := congrArg (Polynomial.map (Ideal.Quotient.mk (Ideal.span {π}))) h3
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add,
      Polynomial.map_sub, map_C, hzπ, map_zero, zero_mul] at this
    linear_combination -this
  rw [h4]
  exact dvd_sub (Dvd.dvd.mul_right (dvd_pow_self _ two_ne_zero) _)
    (Dvd.dvd.mul_right dvd_rfl _)

/-- **Dedekind's criterion, sufficiency, over an integrally closed base.**  Let `π` generate
a maximal ideal of `R` and suppose `minpoly R θ = g h + π M` where, modulo `π`, the factor
`g` is squarefree, every irreducible factor of `h` divides `g`, and `g`, `h`, `M` generate
the unit ideal.  Then `R[θ]` is `π`-saturated in `S`.

This is `NumberField.Relative.mem_adjoin_of_algebraMap_mul_mem` over an arbitrary
integrally closed base.  Applied to `R = (𝓞 K)_𝔭`, a discrete valuation ring in which `𝔭`
is principal, it makes the certificate available at maximal ideals that are not principal in
`𝓞 K`. -/
theorem mem_adjoin_of_algebraMap_mul_mem {π : R} (hπ0 : π ≠ 0)
    (hmax : (Ideal.span {π} : Ideal R).IsMaximal)
    {g h M : R[X]}
    (hf : minpoly R θ = g * h + C π * M)
    (hsq : Squarefree (g.map (Ideal.Quotient.mk (Ideal.span {π}))))
    (hrad : ∀ q : (R ⧸ Ideal.span {π})[X], Irreducible q →
      q ∣ h.map (Ideal.Quotient.mk (Ideal.span {π})) →
      q ∣ g.map (Ideal.Quotient.mk (Ideal.span {π})))
    (hbez : ∃ u v w : (R ⧸ Ideal.span {π})[X],
      u * g.map (Ideal.Quotient.mk (Ideal.span {π})) +
        v * h.map (Ideal.Quotient.mk (Ideal.span {π})) +
        w * M.map (Ideal.Quotient.mk (Ideal.span {π})) = 1)
    {β : S} (hβ : algebraMap R S π * β ∈ Algebra.adjoin R {θ}) :
    β ∈ Algebra.adjoin R {θ} := by
  classical
  by_contra hβnot
  haveI := hmax
  have hπ : Prime π := (Ideal.span_singleton_prime hπ0).mp hmax.isPrime
  have hsurj : Function.Surjective (Ideal.Quotient.mk (Ideal.span {π} : Ideal R)) :=
    Ideal.Quotient.mk_surjective
  have hzπ : Ideal.Quotient.mk (Ideal.span {π}) π = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self π)
  obtain ⟨πb, A, B, N, hπbmonic, hπbirr, hN, hπbA, hπbB, hπbN⟩ :=
    exists_splitting_of_not_saturated hπ0 hmax hβnot hβ
  set fbar := (minpoly R θ).map (Ideal.Quotient.mk (Ideal.span {π})) with hfbar
  set Abar := A.map (Ideal.Quotient.mk (Ideal.span {π})) with hAmap
  set Bbar := B.map (Ideal.Quotient.mk (Ideal.span {π})) with hBmap
  have hBbar : fbar = Abar * Bbar := by
    rw [hfbar, hAmap, hBmap, hN]
    simp only [Polynomial.map_add, Polynomial.map_mul, map_C, hzπ, map_zero,
      zero_mul, add_zero]
  have hπbf : πb ∣ fbar := hBbar ▸ hπbA.mul_right Bbar
  -- `π̄` divides `ḡ` and `h̄`
  have hfgh : fbar = g.map (Ideal.Quotient.mk (Ideal.span {π}))
      * h.map (Ideal.Quotient.mk (Ideal.span {π})) := by
    have := congrArg (Polynomial.map (Ideal.Quotient.mk (Ideal.span {π}))) hf
    simpa only [Polynomial.map_add, Polynomial.map_mul, map_C, hzπ, map_zero, C_0,
      zero_mul, add_zero] using this
  have hπbg : πb ∣ g.map (Ideal.Quotient.mk (Ideal.span {π})) := by
    rcases hπbirr.prime.dvd_mul.mp (hfgh ▸ hπbf) with hcase | hcase
    · exact hcase
    · exact hrad πb hπbirr hcase
  have hπbh : πb ∣ h.map (Ideal.Quotient.mk (Ideal.span {π})) := by
    obtain ⟨g₁, hg₁⟩ := hπbg
    have hπ2 : πb ^ 2 ∣ fbar := by
      rw [hBbar, sq]
      exact mul_dvd_mul hπbA hπbB
    have hstep : πb ∣ g₁ * h.map (Ideal.Quotient.mk (Ideal.span {π})) := by
      have hh2 : πb * (g₁ * h.map (Ideal.Quotient.mk (Ideal.span {π}))) =
          g.map (Ideal.Quotient.mk (Ideal.span {π}))
            * h.map (Ideal.Quotient.mk (Ideal.span {π})) := by
        rw [hg₁]
        ring
      have := hfgh ▸ hπ2
      rw [← hh2, sq] at this
      exact (mul_dvd_mul_iff_left hπbirr.ne_zero).mp this
    rcases hπbirr.prime.dvd_mul.mp hstep with hcase | hcase
    · exfalso
      apply hπbirr.not_isUnit
      apply hsq πb
      rw [hg₁]
      exact mul_dvd_mul_left πb hcase
    · exact hcase
  -- the polynomial `N` with `f = A B + π N`, and `π̄ ∣ N̄`
  -- change of splitting transfers `π̄ ∣ N̄` to `π̄ ∣ M̄`
  obtain ⟨Pi, hPimap, _, hPimonic⟩ :=
    lifts_and_degree_eq_and_monic ((mem_lifts πb).mpr
      (Polynomial.map_surjective _ hsurj πb)) hπbmonic
  have hid : A * B + C π * N = g * h + C π * M := by
    linear_combination hf - hN
  have hπbMN : πb ∣ M.map (Ideal.Quotient.mk (Ideal.span {π}))
      - N.map (Ideal.Quotient.mk (Ideal.span {π})) := by
    have := map_dvd_map_sub_of_map_dvd hπ hPimonic hid
      (hPimap ▸ (hπbA.trans (dvd_of_eq hAmap.symm)))
      (hPimap ▸ (hπbB.trans (dvd_of_eq hBmap.symm)))
      (hPimap ▸ hπbg) (hPimap ▸ hπbh)
    rwa [hPimap] at this
  have hπbM : πb ∣ M.map (Ideal.Quotient.mk (Ideal.span {π})) := by
    have := dvd_add hπbMN hπbN
    rwa [sub_add_cancel] at this
  -- contradiction with the Bézout certificate
  obtain ⟨u', v', w', hbez'⟩ := hbez
  apply hπbirr.not_isUnit
  apply isUnit_of_dvd_one
  rw [← hbez']
  exact dvd_add (dvd_add (hπbg.mul_left u') (hπbh.mul_left v')) (hπbM.mul_left w')



/-! ### Global packaging over a principal ideal base

Assembling the local saturation statements at all primes into full relative monogenicity.
This requires the base `R` to be a principal ideal ring (class number one); over a
general Dedekind base the assembly needs localisation and is left open. -/



end Monogenic

end

end
