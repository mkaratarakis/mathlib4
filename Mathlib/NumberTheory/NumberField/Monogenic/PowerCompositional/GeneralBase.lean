/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.Monogenic.PowerCompositional.Ideal
public import Mathlib.NumberTheory.NumberField.Monogenic.Relative

/-!
# The ideal calculus of Section 2 over an arbitrary base

The lemmas of `PowerCompositional/Ideal.lean` are stated for `ℤ[X]` with a rational prime,
and those of `PowerCompositional/Relative.lean` for `(𝓞 K)[X]` with a prime element.  Neither
is general enough for the last step of Problem 2 of Kaur–Kumar–Remete, which needs them over
a localisation `(𝓞 K)_𝔭` — a discrete valuation ring, where the maximal ideal is principal
even when `𝔭` was not.

This file states them over any commutative domain `R` with an element `π` generating a
maximal ideal, which covers `ℤ`, `𝓞 K`, and every localisation of the latter at once.

## Main results

The membership calculus for the maximal ideal `⟨π, g⟩` of `R[X]`:
`mem_span_pair_iff_map_dvd`, `mem_span_pair_of_C_mul_mem_sq`,
`C_dvd_of_mem_sq_of_natDegree_lt`, `span_pair_le_of_map_dvd`,
`sq_span_pair_le_span_pair_sq`, `span_pair_sq_eq_inf` (Lemma 2.1),
`mem_span_pair_C_sq_X_iff` and `notMem_sq_span_pair_X_of_sq_not_dvd_coeff_zero`.

## Implementation notes

The proofs are those already given over `𝓞 K`.  The only hypothesis they use about the base
is that `R ⧸ (π)` is a field, which is why maximality of `Ideal.span {π}` appears as an
instance argument rather than being derived from primality: over a general domain a prime
element need not generate a maximal ideal, whereas over `ℤ`, over `𝓞 K` and over a discrete
valuation ring it does.
-/

@[expose] public section

noncomputable section

open Polynomial

namespace Monogenic

section IdealCalculus

attribute [local instance] Ideal.Quotient.field

variable {R : Type*} [CommRing R] [IsDomain R] {π : R}
  [hmax : (Ideal.span {π} : Ideal R).IsMaximal]

omit [IsDomain R] hmax in
/-- Membership in `⟨π, P⟩` is divisibility of the reductions modulo `π`. -/
theorem mem_span_pair_iff_map_dvd {P x : R[X]} :
    x ∈ (Ideal.span {C π, P} : Ideal (R[X])) ↔
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
    obtain ⟨z, hz⟩ := NumberField.Relative.map_quotient_span_eq_zero_iff.mp hzero
    exact Ideal.mem_span_pair.mpr ⟨z, y, by linear_combination -hz⟩

/-- If `π * s` lies in `⟨π, P⟩ ^ 2` then `s` lies in `⟨π, P⟩`. -/
theorem mem_span_pair_of_C_mul_mem_sq (hπ : Prime π) {P s : R[X]}
    (hP0 : P.map (Ideal.Quotient.mk (Ideal.span {π})) ≠ 0)
    (hs : C π * s ∈ (Ideal.span {C π, P} : Ideal (R[X])) ^ 2) :
    s ∈ (Ideal.span {C π, P} : Ideal (R[X])) := by
  have hCπ0 : (C π : R[X]) ≠ 0 := fun h => hπ.ne_zero (by simpa using congrArg (·.coeff 0) h)
  obtain ⟨u, v, w, huvw⟩ := Ideal.mem_span_pair_sq_iff.mp hs
  have hwdvd : (C π : R[X]) ∣ w := by
    rw [← NumberField.Relative.map_quotient_span_eq_zero_iff]
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

omit [IsDomain R] in
/-- An element of `⟨π, P⟩ ^ 2` of degree below `2 deg P` is divisible by `π`. -/
theorem C_dvd_of_mem_sq_of_natDegree_lt {P r : R[X]} (hPm : P.Monic)
    (hr : r ∈ (Ideal.span {C π, P} : Ideal (R[X])) ^ 2)
    (hdeg : r.natDegree < 2 * P.natDegree) : (C π : R[X]) ∣ r := by
  rw [← NumberField.Relative.map_quotient_span_eq_zero_iff]
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

omit [IsDomain R] hmax in
/-- If the reduction of `h` divides that of `G`, then `⟨π, G⟩ ⊆ ⟨π, h⟩`. -/
theorem span_pair_le_of_map_dvd {G h : R[X]}
    (hdvd : h.map (Ideal.Quotient.mk (Ideal.span {π}))
      ∣ G.map (Ideal.Quotient.mk (Ideal.span {π}))) :
    (Ideal.span {C π, G} : Ideal (R[X])) ≤ Ideal.span {C π, h} := by
  intro x hx
  rw [mem_span_pair_iff_map_dvd] at hx ⊢
  exact hdvd.trans hx

omit [IsDomain R] hmax in
/-- `⟨π, g⟩ ^ 2 ⊆ ⟨π, g ^ 2⟩`. -/
theorem sq_span_pair_le_span_pair_sq {g : R[X]} :
    (Ideal.span {C π, g} : Ideal (R[X])) ^ 2 ≤ Ideal.span {C π, g ^ 2} := by
  intro z hz
  obtain ⟨a, b, c, habc⟩ := Ideal.mem_span_pair_sq_iff.mp hz
  rw [mem_span_pair_iff_map_dvd]
  refine ⟨c.map (Ideal.Quotient.mk (Ideal.span {π})), ?_⟩
  rw [habc]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_C,
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self π), C_0, zero_mul,
    zero_pow two_ne_zero, zero_add]

omit [IsDomain R] in
/-- **Lemma 2.1 relatively**: `⟨π, g⟩ ^ 2 = ⟨π ^ 2, g⟩ ⊓ ⟨π, g ^ 2⟩`. -/
theorem span_pair_sq_eq_inf {g : R[X]}
    (hg0 : g.map (Ideal.Quotient.mk (Ideal.span {π})) ≠ 0) :
    (Ideal.span {C π, g} : Ideal (R[X])) ^ 2 =
      Ideal.span {C π ^ 2, g} ⊓ Ideal.span {C π, g ^ 2} := by
  refine le_antisymm (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨a, b, c, habc⟩ := Ideal.mem_span_pair_sq_iff.mp hz
    exact ⟨Ideal.mem_span_pair.mpr ⟨a, C π * b + g * c, by rw [habc]; ring⟩,
      Ideal.mem_span_pair.mpr ⟨C π * a + g * b, c, by rw [habc]; ring⟩⟩
  · obtain ⟨hz1, hz2⟩ := hz
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hz1
    obtain ⟨c, d, hcd⟩ := Ideal.mem_span_pair.mp hz2
    have hb : b ∈ (Ideal.span {C π, g} : Ideal (R[X])) := by
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

omit [IsDomain R] hmax in
/-- Membership in `⟨π ^ 2, X⟩` is divisibility of the constant term by `π ^ 2`. -/
theorem mem_span_pair_C_sq_X_iff {f : R[X]} :
    f ∈ (Ideal.span {C π ^ 2, X} : Ideal (R[X])) ↔ π ^ 2 ∣ f.coeff 0 := by
  constructor
  · rintro hf
    obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hf
    simp [coeff_zero_eq_eval_zero]
  · rintro ⟨c, hc⟩
    obtain ⟨q, hq⟩ : (X : R[X]) ∣ f - C (f.coeff 0) := by
      rw [X_dvd_iff]; simp
    refine Ideal.mem_span_pair.mpr ⟨C c, q, ?_⟩
    have hCf : C (f.coeff 0) = C π ^ 2 * C c := by rw [hc, map_mul, map_pow]
    linear_combination -hq - hCf

omit [IsDomain R] in
/-- If `π ^ 2` does not divide the constant term, then `f` avoids `⟨π, X⟩ ^ 2`. -/
theorem notMem_sq_span_pair_X_of_sq_not_dvd_coeff_zero {f : R[X]}
    (h : ¬ π ^ 2 ∣ f.coeff 0) :
    f ∉ (Ideal.span {C π, X} : Ideal (R[X])) ^ 2 := by
  have hX0 : (X : R[X]).map (Ideal.Quotient.mk (Ideal.span {π})) ≠ 0 := by
    rw [Polynomial.map_X]; exact X_ne_zero
  rw [span_pair_sq_eq_inf hX0]
  exact fun hm => h (mem_span_pair_C_sq_X_iff.mp hm.1)



end IdealCalculus

end Monogenic
