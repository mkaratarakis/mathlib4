/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.Monogenic.PowerCompositional.Ideal
public import Mathlib.NumberTheory.NumberField.Monogenic.Relative
public import Mathlib.NumberTheory.NumberField.Monogenic.PowerCompositional.Relative

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



omit [IsDomain R] hmax in
/-- Membership in `𝔪 ^ 2` depends only on the class modulo `𝔪 ^ 2`. -/
private theorem mem_sq_iff_of_sub_mem {I : Ideal (R[X])} {x y : R[X]}
    (h : x - y ∈ I ^ 2) : x ∈ I ^ 2 ↔ y ∈ I ^ 2 :=
  ⟨fun hx => (Submodule.sub_mem_iff_right _ hx).mp h,
    fun hy => (Submodule.sub_mem_iff_left _ hy).mp h⟩

/-! ### Section 2 over an arbitrary base

Proposition 2.10, Theorem 2.4 and Corollary 2.5 of Kaur–Kumar–Remete, over any base whose
residue field at `π` is perfect of characteristic `p`.

Perfectness is a genuine hypothesis, not an artifact: Proposition 2.10 uses that irreducibles
over the residue field are separable, and the Frobenius twist of Theorem 2.4 is a *bijection*
on irreducibles only when Frobenius is surjective.  Residue fields of number fields are
finite, hence perfect, so nothing is lost there; over an imperfect residue field the
statements themselves change. -/

section Section2

variable [PerfectField (R ⧸ Ideal.span {π})]

omit [IsDomain R] [PerfectField (R ⧸ Ideal.span {π})] in
/-- A monic nonconstant `G : R[X]` admits a monic `h` whose reduction is an irreducible
factor of the reduction of `G`. -/
theorem exists_monic_map_irreducible_dvd {G : R[X]} (hG : G.Monic)
    (hGd : 0 < G.natDegree) :
    ∃ h : R[X], h.Monic ∧ Irreducible (h.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
      h.map (Ideal.Quotient.mk (Ideal.span {π})) ∣ G.map (Ideal.Quotient.mk (Ideal.span {π})) := by
  classical
  have hsurj : Function.Surjective (Ideal.Quotient.mk (Ideal.span {π} : Ideal (R))) :=
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

omit [IsDomain R] [PerfectField (R ⧸ Ideal.span {π})] in
/-- **Lemma 2.6 relatively, in ideal form.** -/
theorem exists_expand_mem_sq {f g : R[X]} (hgm : g.Monic)
    (hgd : 0 < g.natDegree) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (hmem : f ∈ (Ideal.span {C π, g} : Ideal (R[X])) ^ 2) :
    ∃ h : R[X], h.Monic ∧ Irreducible (h.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
      Polynomial.expand (R) ℓ f ∈ (Ideal.span {C π, h} : Ideal (R[X])) ^ 2 := by
  have hEm : (Polynomial.expand (R) ℓ g).Monic := hgm.expand hℓ
  have hEd : 0 < (Polynomial.expand (R) ℓ g).natDegree := by
    rw [natDegree_expand]; positivity
  obtain ⟨h, hhm, hhirr, hhdvd⟩ := exists_monic_map_irreducible_dvd (π := π) hEm hEd
  refine ⟨h, hhm, hhirr, Ideal.pow_right_mono (span_pair_le_of_map_dvd hhdvd) 2 ?_⟩
  obtain ⟨u, v, w, huvw⟩ := Ideal.mem_span_pair_sq_iff.mp hmem
  refine Ideal.mem_span_pair_sq_iff.mpr ⟨Polynomial.expand (R) ℓ u,
    Polynomial.expand (R) ℓ v, Polynomial.expand (R) ℓ w, ?_⟩
  rw [huvw]
  simp only [map_add, map_mul, map_pow, expand_C]

omit [IsDomain R] [PerfectField (R ⧸ Ideal.span {π})] in
/-- **Proposition 2.3 relatively, in ideal form.** -/
theorem expand_mem_sq_of_sq_dvd_coeff_zero {f : R[X]} {ℓ : ℕ} (hℓ : 2 ≤ ℓ)
    (hπ2 : π ^ 2 ∣ f.coeff 0) :
    Polynomial.expand (R) ℓ f ∈ (Ideal.span {C π, X} : Ideal (R[X])) ^ 2 := by
  have hℓ0 : 0 < ℓ := by omega
  have hX0 : (X : R[X]).map (Ideal.Quotient.mk (Ideal.span {π})) ≠ 0 := by
    rw [Polynomial.map_X]; exact X_ne_zero
  rw [span_pair_sq_eq_inf hX0, Ideal.mem_inf]
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

/-- **Theorem 2.4 over a number field base**, with the Frobenius twist.  Let `gσ` be a monic
polynomial whose reduction is the Frobenius twist of that of `g`.  If `F ∈ ⟨π, gσ ^ 2⟩` then

    F ∈ ⟨π, gσ⟩ ^ 2  ↔  F(X ^ p) ∈ ⟨π, g⟩ ^ 2.

Over `𝔽ₚ` the twist is the identity and this is the paper's Theorem 2.4.  In general the two
sides pass through *different* primes of `R[X]`, related by the Frobenius, which is
exactly the phenomenon isolated in `NumberField.Relative.dvd_expand_iff_map_frobenius_dvd`.

The twisted statement is in fact easier than the absolute one: writing `F = π r + gσ ^ 2 q`,
both sides reduce by the cancellation lemma to the single divisibility
`gσ ∣ r` modulo `π`, and the two applications of the twist lemma are what identify them.
No integral Frobenius identity is needed, and the absolute proof's steps 3 and 4 disappear. -/
theorem mem_sq_span_iff_expand_mem_sq_span (hπ : Prime π) {p : ℕ} [Fact p.Prime]
    [CharP (R ⧸ Ideal.span {π}) p] {g gσ : R[X]}
    (hgirr : Irreducible (g.map (Ideal.Quotient.mk (Ideal.span {π}))))
    (hgσ0 : gσ.map (Ideal.Quotient.mk (Ideal.span {π})) ≠ 0)
    (htwist : gσ.map (Ideal.Quotient.mk (Ideal.span {π}))
      = (g.map (Ideal.Quotient.mk (Ideal.span {π}))).map (frobenius (R ⧸ Ideal.span {π}) p))
    {F : R[X]} (hF : F ∈ (Ideal.span {C π, gσ ^ 2} : Ideal (R[X]))) :
    F ∈ (Ideal.span {C π, gσ} : Ideal (R[X])) ^ 2 ↔
      Polynomial.expand (R) p F ∈ (Ideal.span {C π, g} : Ideal (R[X])) ^ 2 := by
  haveI : ExpChar (R ⧸ Ideal.span {π}) p := ExpChar.prime Fact.out
  haveI : PerfectRing (R ⧸ Ideal.span {π}) p := PerfectField.toPerfectRing p
  set mk := Ideal.Quotient.mk (Ideal.span {π} : Ideal (R)) with hmk
  obtain ⟨r, q, hrq⟩ := Ideal.mem_span_pair.mp hF
  -- the left-hand side is `gσ ∣ r` mod `π`
  have hleft : F ∈ (Ideal.span {C π, gσ} : Ideal (R[X])) ^ 2 ↔
      gσ.map mk ∣ r.map mk := by
    have hsub : F - C π * r ∈ (Ideal.span {C π, gσ} : Ideal (R[X])) ^ 2 := by
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
  have hexpσ : Polynomial.expand (R) p gσ ∈ (Ideal.span {C π, g} : Ideal (R[X])) := by
    rw [mem_span_pair_iff_map_dvd, Polynomial.map_expand, htwist,
      NumberField.Relative.dvd_expand_iff_map_frobenius_dvd hgirr]
  have hright : Polynomial.expand (R) p F ∈
      (Ideal.span {C π, g} : Ideal (R[X])) ^ 2 ↔ gσ.map mk ∣ r.map mk := by
    have hsub : Polynomial.expand (R) p F - C π * Polynomial.expand (R) p r ∈
        (Ideal.span {C π, g} : Ideal (R[X])) ^ 2 := by
      have heq : Polynomial.expand (R) p F - C π * Polynomial.expand (R) p r
          = (Polynomial.expand (R) p gσ) ^ 2 * Polynomial.expand (R) p q := by
        have hh := congrArg (Polynomial.expand (R) p) hrq
        simp only [map_add, map_mul, map_pow, expand_C] at hh
        linear_combination -hh
      rw [heq, sq, sq]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul hexpσ hexpσ)
    rw [mem_sq_iff_of_sub_mem hsub]
    have hg0 : g.map mk ≠ 0 := hgirr.ne_zero
    constructor
    · intro h
      have h1 := mem_span_pair_iff_map_dvd.mp (mem_span_pair_of_C_mul_mem_sq hπ hg0 h)
      rw [Polynomial.map_expand,
        NumberField.Relative.dvd_expand_iff_map_frobenius_dvd hgirr, ← htwist] at h1
      exact h1
    · intro h
      have h1 : g.map mk ∣ (Polynomial.expand (R) p r).map mk := by
        rw [Polynomial.map_expand,
          NumberField.Relative.dvd_expand_iff_map_frobenius_dvd hgirr, ← htwist]
        exact h
      obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp (mem_span_pair_iff_map_dvd.mpr h1)
      refine Ideal.mem_span_pair_sq_iff.mpr ⟨a, b, 0, ?_⟩
      rw [← hab]; ring
  rw [hleft, hright]

/-- **Proposition 2.10 over a number field base**, in ideal form.  Let `π` be a prime element
of `R` whose residue field has characteristic `p`, and let `ℓ` be prime to `p`.  If
`f(X ^ ℓ)` lies in the square of a maximal ideal `⟨π, h⟩` of `R[X]`, then either `f`
lies in the square of such an ideal, or `π ^ 2` divides `f(0)`.

The proof is the absolute one: split on whether the reduction of `h` is `X`; if not, the
prime of the residue polynomial ring lying below `h` along `X ↦ X ^ ℓ` gives a `G` whose
square divides the reduction of `f`, and lifting `G` and dividing `f = g q + r` produces the
required membership.  The residue field is no longer prime, but every lemma used has been
stated over an arbitrary perfect field of characteristic `p`, and the identity that fails
there — `f(X ^ p) = f ^ p` — is not used, since `p ∤ ℓ`. -/
theorem exists_mem_sq_or_sq_dvd_coeff_zero (hπ : Prime π) {p : ℕ} [Fact p.Prime]
    [CharP (R ⧸ Ideal.span {π}) p] {f : R[X]} (hfm : f.Monic) {ℓ : ℕ} (hℓ0 : 0 < ℓ)
    (hℓ : ¬ p ∣ ℓ) {h : R[X]} (hhm : h.Monic)
    (hhirr : Irreducible (h.map (Ideal.Quotient.mk (Ideal.span {π}))))
    (hmem : Polynomial.expand (R) ℓ f ∈
      (Ideal.span {C π, h} : Ideal (R[X])) ^ 2) :
    (∃ g : R[X], g.Monic ∧ Irreducible (g.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
      f ∈ (Ideal.span {C π, g} : Ideal (R[X])) ^ 2) ∨ π ^ 2 ∣ f.coeff 0 := by
  classical
  set mk := Ideal.Quotient.mk (Ideal.span {π} : Ideal (R)) with hmk
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
    have hle : (Ideal.span {C π, h} : Ideal (R[X])) ≤ Ideal.span {C π, X} :=
      span_pair_le_of_map_dvd (by rw [Polynomial.map_X, hhX])
    refine notMem_sq_span_pair_X_of_sq_not_dvd_coeff_zero
      (f := Polynomial.expand (R) ℓ f) ?_ (Ideal.pow_right_mono hle 2 hmem)
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
    obtain ⟨s, hs⟩ : (C π : R[X]) ∣ r := by
      rw [← NumberField.Relative.map_quotient_span_eq_zero_iff]; exact hrmap
    have hGq : G ∣ q.map mk := by
      obtain ⟨m, hm⟩ := hG2
      have hcancel : G * q.map mk = G * (G * m) := by
        rw [← mul_assoc, ← sq, ← hm, ← hmapdiv, hrmap, zero_add]
      exact ⟨m, mul_left_cancel₀ hGirr.ne_zero hcancel⟩
    have hqmem : q ∈ (Ideal.span {C π, g} : Ideal (R[X])) :=
      mem_span_pair_iff_map_dvd.mpr (by rw [hgmap]; exact hGq)
    have hgmem : g ∈ (Ideal.span {C π, g} : Ideal (R[X])) := Ideal.subset_span (by simp)
    have hgq : g * q ∈ (Ideal.span {C π, g} : Ideal (R[X])) ^ 2 := by
      rw [sq]; exact Ideal.mul_mem_mul hgmem hqmem
    have hCps : C π * s ∉ (Ideal.span {C π, g} : Ideal (R[X])) ^ 2 := fun hcon =>
      hnot (by rw [← hdiv, hs]; exact Ideal.add_mem _ hcon hgq)
    have hsmap : s.map mk ≠ 0 := by
      intro h0
      obtain ⟨s', rfl⟩ : (C π : R[X]) ∣ s := by
        rw [← NumberField.Relative.map_quotient_span_eq_zero_iff]; exact h0
      refine hCps ?_
      have hsq2 : (Ideal.span {C π, g} : Ideal (R[X])) ^ 2 =
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
    have hEg : Polynomial.expand (R) ℓ g ∈ (Ideal.span {C π, h} : Ideal (R[X])) :=
      mem_span_pair_iff_map_dvd.mpr (by rw [Polynomial.map_expand, hgmap]; exact hhG)
    have hEq : Polynomial.expand (R) ℓ q ∈ (Ideal.span {C π, h} : Ideal (R[X])) :=
      mem_span_pair_iff_map_dvd.mpr (by
        rw [Polynomial.map_expand]
        exact hhG.trans (map_dvd (Polynomial.expand _ ℓ) hGq))
    have hprod : Polynomial.expand (R) ℓ g * Polynomial.expand (R) ℓ q ∈
        (Ideal.span {C π, h} : Ideal (R[X])) ^ 2 := by
      rw [sq]; exact Ideal.mul_mem_mul hEg hEq
    have hEs : C π * Polynomial.expand (R) ℓ s ∈
        (Ideal.span {C π, h} : Ideal (R[X])) ^ 2 := by
      have hexpand : Polynomial.expand (R) ℓ f = C π * Polynomial.expand (R) ℓ s +
          Polynomial.expand (R) ℓ g * Polynomial.expand (R) ℓ q := by
        rw [← hdiv, hs, map_add, map_mul, map_mul, expand_C]
      have hd := Ideal.sub_mem _ hmem hprod
      rwa [hexpand, add_sub_cancel_right] at hd
    have hfin := mem_span_pair_of_C_mul_mem_sq hπ hhm'.ne_zero hEs
    rw [mem_span_pair_iff_map_dvd, Polynomial.map_expand] at hfin
    exact hfin

/-- One descent step: if `π` is an index divisor of `f(X ^ (p ^ (u+1)))` then it is one of
`f(X ^ (p ^ u))`, for `u ≥ 1`.

By Theorem 2.4 twisted, applied to `F = f(X ^ (p ^ u))`: the witness `h` for `F(X ^ p)`
produces the twisted witness `gσ` for `F`.  The hypothesis `F ∈ ⟨π, gσ ^ 2⟩` that Theorem 2.4
needs holds because `F` is itself an expansion, hence a `p ^ u`-th power modulo `π`, and
`p ^ u ≥ 2`. -/
theorem exists_expand_pow_mem_sq_of_succ (hπ : Prime π) {p : ℕ} [Fact p.Prime]
    [CharP (R ⧸ Ideal.span {π}) p] {f : R[X]} {u : ℕ} (hu : 0 < u)
    {h : R[X]} (hhm : h.Monic)
    (hhirr : Irreducible (h.map (Ideal.Quotient.mk (Ideal.span {π}))))
    (hmem : Polynomial.expand (R) (p ^ (u + 1)) f ∈
      (Ideal.span {C π, h} : Ideal (R[X])) ^ 2) :
    ∃ g : R[X], g.Monic ∧ Irreducible (g.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
      Polynomial.expand (R) (p ^ u) f ∈ (Ideal.span {C π, g} : Ideal (R[X])) ^ 2 := by
  classical
  haveI : ExpChar (R ⧸ Ideal.span {π}) p := ExpChar.prime Fact.out
  haveI : PerfectRing (R ⧸ Ideal.span {π}) p := PerfectField.toPerfectRing p
  set mk := Ideal.Quotient.mk (Ideal.span {π} : Ideal (R)) with hmk
  set F := Polynomial.expand (R) (p ^ u) f with hFdef
  have hexp : Polynomial.expand (R) p F = Polynomial.expand (R) (p ^ (u + 1)) f := by
    rw [hFdef, expand_expand, ← pow_succ']
  -- the twisted witness
  obtain ⟨gσ, hgσmap, -, hgσm⟩ := lifts_and_degree_eq_and_monic
    ((mem_lifts ((h.map mk).map (frobenius (R ⧸ Ideal.span {π}) p))).mpr
      (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective _))
    (((hhm.map mk).map (frobenius (R ⧸ Ideal.span {π}) p)))
  have hgσirr : Irreducible (gσ.map mk) := by
    rw [hgσmap]
    exact (MulEquiv.irreducible_iff
      (Polynomial.mapEquiv (frobeniusEquiv (R ⧸ Ideal.span {π}) p)).toMulEquiv).mpr hhirr
  -- the square hypothesis for Theorem 2.4
  have hdvd1 : gσ.map mk ∣ F.map mk := by
    have h1 : (h.map mk) ∣ (Polynomial.expand (R) p F).map mk := by
      have h2 := sq_span_pair_le_span_pair_sq (hexp ▸ hmem)
      rw [mem_span_pair_iff_map_dvd, Polynomial.map_pow] at h2
      exact (dvd_pow_self _ two_ne_zero).trans h2
    rw [Polynomial.map_expand, NumberField.Relative.dvd_expand_iff_map_frobenius_dvd hhirr] at h1
    rwa [hgσmap]
  have hsq : F ∈ (Ideal.span {C π, gσ ^ 2} : Ideal (R[X])) := by
    obtain ⟨A, hA⟩ := NumberField.Relative.exists_pow_of_expand_pow
      (k := R ⧸ Ideal.span {π}) (p := p) u (f.map mk)
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
    [CharP (R ⧸ Ideal.span {π}) p] {f : R[X]} :
    ∀ u : ℕ, 0 < u →
      (∃ h : R[X], h.Monic ∧ Irreducible (h.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
        Polynomial.expand (R) (p ^ u) f ∈ (Ideal.span {C π, h} : Ideal (R[X])) ^ 2) →
      (∃ h : R[X], h.Monic ∧ Irreducible (h.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
        Polynomial.expand (R) p f ∈ (Ideal.span {C π, h} : Ideal (R[X])) ^ 2) := by
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
    [CharP (R ⧸ Ideal.span {π}) p] {f : R[X]} {u : ℕ} (hu : 0 < u) :
    (∃ h : R[X], h.Monic ∧ Irreducible (h.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
        Polynomial.expand (R) p f ∈ (Ideal.span {C π, h} : Ideal (R[X])) ^ 2) ↔
      (∃ h : R[X], h.Monic ∧ Irreducible (h.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
        Polynomial.expand (R) (p ^ u) f ∈ (Ideal.span {C π, h} : Ideal (R[X])) ^ 2) := by
  constructor
  · rintro ⟨h, hhm, hhirr, hmem⟩
    have hgd : 0 < h.natDegree := by
      rcases Nat.eq_zero_or_pos h.natDegree with h0 | hpos
      · rw [eq_one_of_monic_natDegree_zero hhm h0, Polynomial.map_one] at hhirr
        exact absurd hhirr not_irreducible_one
      · exact hpos
    obtain ⟨h', hh'm, hh'irr, hmem'⟩ :=
      exists_expand_mem_sq (ℓ := p ^ (u - 1)) (π := π) hhm hgd
        (pow_pos (Fact.out : p.Prime).pos _) hmem
    refine ⟨h', hh'm, hh'irr, ?_⟩
    rwa [expand_expand, ← pow_succ, Nat.sub_add_cancel hu] at hmem'
  · exact exists_expand_pow_mem_sq_descend hπ u hu

/-- **The relative criterion at a prime not dividing `k`.**  Let `π` be a prime element of
`R` whose residue field has characteristic `p`, and let `k ≥ 2` be prime to `p`.  Then `π`
is an index divisor of `f(X ^ k)` if and only if it is an index divisor of `f`, or
`π ^ 2` divides `f(0)`.

This is Theorem 1.1 of Kaur–Kumar–Remete, at the primes prime to `k`, over an arbitrary
number field base.  Combined with
`NumberField.Relative.isIndexDivisor_iff_exists_notMem` it decides `π`-saturation, and hence
— via `NumberField.Relative.adjoin_eq_top_of_forall_maximal_saturated` — contributes the
corresponding condition to relative monogenity. -/
theorem exists_expand_mem_sq_iff (hπ : Prime π) {p : ℕ} [Fact p.Prime]
    [CharP (R ⧸ Ideal.span {π}) p] {f : R[X]} (hfm : f.Monic) {k : ℕ} (hk : 2 ≤ k)
    (hpk : ¬ p ∣ k) :
    (∃ h : R[X], h.Monic ∧ Irreducible (h.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
        Polynomial.expand (R) k f ∈ (Ideal.span {C π, h} : Ideal (R[X])) ^ 2) ↔
      (∃ g : R[X], g.Monic ∧ Irreducible (g.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
        f ∈ (Ideal.span {C π, g} : Ideal (R[X])) ^ 2) ∨ π ^ 2 ∣ f.coeff 0 := by
  constructor
  · rintro ⟨h, hhm, hhirr, hmem⟩
    exact exists_mem_sq_or_sq_dvd_coeff_zero hπ hfm (by omega) hpk hhm hhirr hmem
  · rintro (⟨g, hgm, hgirr, hmem⟩ | h2)
    · have hgd : 0 < g.natDegree := by
        rcases Nat.eq_zero_or_pos g.natDegree with h0 | hpos
        · rw [eq_one_of_monic_natDegree_zero hgm h0, Polynomial.map_one] at hgirr
          exact absurd hgirr not_irreducible_one
        · exact hpos
      exact exists_expand_mem_sq (π := π) hgm hgd (by omega) hmem
    · exact ⟨X, monic_X, by rw [Polynomial.map_X]; exact irreducible_X,
        expand_mem_sq_of_sq_dvd_coeff_zero hk h2⟩

/-- **Theorem 1.1 of Kaur–Kumar–Remete over a number field base, prime by prime.**  Let `π`
be a prime element of `R` whose residue field has characteristic `p`, and let `k ≥ 2`.
Then `π` is an index divisor of `f(X ^ k)` if and only if

* `π` is an index divisor of `f(X ^ p)`, when `p ∣ k`, or of `f` itself, when `p ∤ k`;
* or `π ^ 2` divides `f(0)`.

Writing `k = p ^ u * m` with `p ∤ m`, Corollary 2.5 contracts `p ^ u` to `p` and
Proposition 2.10 strips `m`, exactly as in the absolute case; the Frobenius twist that
appears at each contraction is invisible here because the statement quantifies over the
witnessing prime. -/
theorem exists_expand_mem_sq_iff_of_dvd (hπ : Prime π) {p : ℕ} [Fact p.Prime]
    [CharP (R ⧸ Ideal.span {π}) p] {f : R[X]} (hfm : f.Monic) {k : ℕ} (hk : 2 ≤ k)
    (hpk : p ∣ k) :
    (∃ h : R[X], h.Monic ∧ Irreducible (h.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
        Polynomial.expand (R) k f ∈ (Ideal.span {C π, h} : Ideal (R[X])) ^ 2) ↔
      (∃ h : R[X], h.Monic ∧ Irreducible (h.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
        Polynomial.expand (R) p f ∈ (Ideal.span {C π, h} : Ideal (R[X])) ^ 2) ∨
      π ^ 2 ∣ f.coeff 0 := by
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
  have hcoeff : (Polynomial.expand (R) (p ^ u) f).coeff 0 = f.coeff 0 := by
    rw [coeff_expand (pow_pos hppos u), if_pos (dvd_zero _), Nat.zero_div]
  rcases eq_or_lt_of_le (show 1 ≤ m from hm0) with hm1 | hm2
  · -- `k = p ^ u`
    have hkpu : k = p ^ u := by rw [hkeq, ← hm1, mul_one]
    subst hkpu
    refine ⟨fun h => Or.inl ((exists_expand_pow_mem_sq_iff hπ hu).mpr h), ?_⟩
    rintro (h | h)
    · exact (exists_expand_pow_mem_sq_iff hπ hu).mp h
    · exact ⟨X, monic_X, by rw [Polynomial.map_X]; exact irreducible_X,
        expand_mem_sq_of_sq_dvd_coeff_zero hk h⟩
  · -- `k = p ^ u * m` with `m ≥ 2`: strip `m` by Proposition 2.10
    have hexp : Polynomial.expand (R) m (Polynomial.expand (R) (p ^ u) f)
        = Polynomial.expand (R) k f := by
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

end Section2

end IdealCalculus

end Monogenic
