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

end Monogenic

end

end
