/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.NumberTheory.NumberField.Monogenic.Base

/-!
# Monogenity is a local property

The criteria of this development are stated at a prime *element* `π` of the base, so they
reach a maximal ideal `𝔭` only when `𝔭` is principal — that is, only over a base of class
number one.  The way out is that monogenity is local: `R[θ] = S` may be checked after
localising at each maximal ideal, and a localisation `R_𝔭` of a Dedekind domain is a discrete
valuation ring, whose maximal ideal *is* principal.  So a criterion stated with a prime
element, applied downstairs, decides the question at an arbitrary maximal ideal upstairs.

This file supplies the glue for that argument.

## Main results

* `Monogenic.mem_adjoin_of_smul_mem_of_exists_notMem`: if `x β ∈ R[θ]` for every `x` in a
  maximal ideal `𝔭`, and additionally `t β ∈ R[θ]` for a single `t ∉ 𝔭`, then `β ∈ R[θ]`.
  This is the local-global step in its sharpest form: `𝔭`-saturation plus one clearing
  element outside `𝔭` gives membership outright, because `𝔭` and `t` generate the unit ideal.

* `Monogenic.mem_adjoin_of_forall_maximal_exists_notMem`: consequently, if at every maximal
  ideal some element outside it clears `β` into `R[θ]`, then `β ∈ R[θ]` — no saturation
  hypothesis at all.

* `Monogenic.adjoin_eq_top_of_forall_maximal_localization_adjoin_eq_top`: if the localised
  question has a positive answer at every maximal ideal, then `R[θ] = S`.

* `Monogenic.adjoin_eq_top_of_forall_maximal_forall_prime_saturated`: the same conclusion from
  saturation at the prime elements of the localisations — the form in which the criteria of
  this development, which are stated at a prime *element*, apply over an arbitrary base.
  Over a Dedekind domain each localisation is a discrete valuation ring, so its prime element
  is its uniformiser and the hypothesis is one saturation check per maximal ideal.

The intended source of the clearing element is
`multiple_mem_adjoin_of_mem_localization_adjoin`: if `β` lies in `R_𝔭[θ]` inside the
localisation, then `t β ∈ R[θ]` for some `t ∉ 𝔭`.
-/

@[expose] public section

noncomputable section

open Algebra

namespace Monogenic

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {θ : S}

/-- **The local–global step.**  Let `𝔭` be a maximal ideal of `R`.  If `x β` lies in `R[θ]`
for every `x ∈ 𝔭`, and `t β` lies in `R[θ]` for some single `t ∉ 𝔭`, then `β ∈ R[θ]`.

Since `𝔭` is maximal and `t ∉ 𝔭`, the ideal `𝔭 ⊔ (t)` is everything, so `1 = a + b t` with
`a ∈ 𝔭`; then `β = a β + b (t β)` exhibits `β` as a sum of two elements of `R[θ]`. -/
theorem mem_adjoin_of_smul_mem_of_exists_notMem {𝔭 : Ideal R} (h𝔭 : 𝔭.IsMaximal) {β : S}
    (hsat : ∀ x ∈ 𝔭, algebraMap R S x * β ∈ Algebra.adjoin R {θ})
    {t : R} (ht𝔭 : t ∉ 𝔭) (ht : algebraMap R S t * β ∈ Algebra.adjoin R {θ}) :
    β ∈ Algebra.adjoin R {θ} := by
  -- `𝔭` is maximal and `t ∉ 𝔭`, so `𝔭 ⊔ (t) = ⊤`
  have htop : 𝔭 ⊔ Ideal.span {t} = ⊤ := by
    by_contra hne
    have heq := h𝔭.eq_of_le hne le_sup_left
    exact ht𝔭 (heq ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self t))
  have hone : (1 : R) ∈ 𝔭 ⊔ Ideal.span {t} := htop ▸ Submodule.mem_top
  rw [Submodule.mem_sup] at hone
  obtain ⟨a, ha, y, hy, hay⟩ := hone
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  -- `β = a β + b (t β)`
  have hβ : β = algebraMap R S a * β + algebraMap R S b * (algebraMap R S t * β) := by
    have h1 : algebraMap R S a + algebraMap R S b * algebraMap R S t = 1 := by
      rw [← map_mul, ← map_add, hay, map_one]
    calc β = (algebraMap R S a + algebraMap R S b * algebraMap R S t) * β := by rw [h1, one_mul]
    _ = algebraMap R S a * β + algebraMap R S b * (algebraMap R S t * β) := by ring
  rw [hβ]
  exact add_mem (hsat a ha) (mul_mem (Subalgebra.algebraMap_mem _ _) ht)

/-- If at every maximal ideal `𝔭` of `R` some element outside `𝔭` clears `β` into `R[θ]`,
then `β` already lies in `R[θ]`.

No saturation hypothesis is needed: the elements that clear `β` generate an ideal contained
in no maximal ideal, hence the unit ideal, and a partition of unity assembles `β`. -/
theorem mem_adjoin_of_forall_maximal_exists_notMem {β : S}
    (h : ∀ 𝔭 : Ideal R, 𝔭.IsMaximal → ∃ t : R, t ∉ 𝔭 ∧
      algebraMap R S t * β ∈ Algebra.adjoin R {θ}) :
    β ∈ Algebra.adjoin R {θ} := by
  classical
  -- the conductor-like ideal of elements clearing `β`
  set I : Ideal R :=
    { carrier := {r : R | algebraMap R S r * β ∈ Algebra.adjoin R {θ}}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add, add_mul] at ha hb ⊢
        exact add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun c {x} hx => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, mul_assoc] at hx ⊢
        exact mul_mem (Subalgebra.algebraMap_mem _ _) hx } with hI
  have hItop : I = ⊤ := by
    by_contra hne
    obtain ⟨𝔭, h𝔭, hle⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨t, ht𝔭, ht⟩ := h 𝔭 h𝔭
    exact ht𝔭 (hle ht)
  have hmem : ∀ r : R, r ∈ I → algebraMap R S r * β ∈ Algebra.adjoin R {θ} := fun _ hr => hr
  have h1 : (1 : R) ∈ I := hItop ▸ Submodule.mem_top
  simpa using hmem 1 h1

/-- **Monogenity is local.**  If, for every `β : S` and every maximal ideal `𝔭` of `R`, some
element outside `𝔭` clears `β` into `R[θ]`, then `R[θ] = S`. -/
theorem adjoin_eq_top_of_forall_maximal_exists_notMem
    (h : ∀ β : S, ∀ 𝔭 : Ideal R, 𝔭.IsMaximal → ∃ t : R, t ∉ 𝔭 ∧
      algebraMap R S t * β ∈ Algebra.adjoin R {θ}) :
    Algebra.adjoin R {θ} = ⊤ :=
  Algebra.eq_top_iff.mpr fun β => mem_adjoin_of_forall_maximal_exists_notMem (h β)

/-- **Monogenity may be checked after localising at each maximal ideal.**  If for every
maximal ideal `𝔭` the image of `β` lies in the subalgebra generated by `θ` over the
localisation `R_𝔭`, then `β` already lies in `R[θ]`.

This composes `exists_smul_mem_adjoin_of_mem_localization_adjoin`, which
turns membership after localising into a denominator outside `𝔭`, with
`Monogenic.mem_adjoin_of_forall_maximal_exists_notMem`, which assembles such denominators
into membership.  Since a localisation of a Dedekind domain at a maximal ideal is a discrete
valuation ring, whose maximal ideal is principal, this is what lets criteria stated with a
prime *element* decide the question at an arbitrary maximal ideal. -/
theorem mem_adjoin_of_forall_maximal_localization {β : S}
    (R' S' : Ideal R → Type*)
    [∀ 𝔭 : Ideal R, CommRing (R' 𝔭)] [∀ 𝔭 : Ideal R, CommRing (S' 𝔭)]
    [∀ 𝔭 : Ideal R, Algebra R (R' 𝔭)] [∀ 𝔭 : Ideal R, Algebra (R' 𝔭) (S' 𝔭)]
    [∀ 𝔭 : Ideal R, Algebra R (S' 𝔭)] [∀ 𝔭 : Ideal R, Algebra S (S' 𝔭)]
    [∀ 𝔭 : Ideal R, IsScalarTower R (R' 𝔭) (S' 𝔭)]
    [∀ 𝔭 : Ideal R, IsScalarTower R S (S' 𝔭)]
    [∀ (𝔭 : Ideal R) [𝔭.IsPrime], IsLocalization 𝔭.primeCompl (R' 𝔭)]
    (hinj : ∀ 𝔭 : Ideal R, Function.Injective (algebraMap S (S' 𝔭)))
    (h : ∀ 𝔭 : Ideal R, 𝔭.IsMaximal →
      algebraMap S (S' 𝔭) β ∈ Algebra.adjoin (R' 𝔭) {algebraMap S (S' 𝔭) θ}) :
    β ∈ Algebra.adjoin R {θ} := by
  refine mem_adjoin_of_forall_maximal_exists_notMem fun 𝔭 h𝔭 => ?_
  obtain ⟨t, htM, ht⟩ := exists_smul_mem_adjoin_of_mem_localization_adjoin
    𝔭.primeCompl (R' 𝔭) (S' 𝔭) (hinj 𝔭) (h 𝔭 h𝔭)
  exact ⟨t, htM, ht⟩

/-- **Monogenicity is detected by the localisations.**  If `R'_𝔭 [θ] = S'_𝔭` for every maximal
ideal `𝔭` of `R`, then `R[θ] = S`.

This is the form in which the local theory is applied: a criterion available over a base with
a prime *element* decides `Algebra.adjoin (R' 𝔭) {θ} = ⊤` at each `𝔭`, because `R' 𝔭` is a
discrete valuation ring, and this theorem assembles those local verdicts into the global one.
No hypothesis on the class number of `R` appears. -/
theorem adjoin_eq_top_of_forall_maximal_localization_adjoin_eq_top
    (R' S' : Ideal R → Type*)
    [∀ 𝔭 : Ideal R, CommRing (R' 𝔭)] [∀ 𝔭 : Ideal R, CommRing (S' 𝔭)]
    [∀ 𝔭 : Ideal R, Algebra R (R' 𝔭)] [∀ 𝔭 : Ideal R, Algebra (R' 𝔭) (S' 𝔭)]
    [∀ 𝔭 : Ideal R, Algebra R (S' 𝔭)] [∀ 𝔭 : Ideal R, Algebra S (S' 𝔭)]
    [∀ 𝔭 : Ideal R, IsScalarTower R (R' 𝔭) (S' 𝔭)]
    [∀ 𝔭 : Ideal R, IsScalarTower R S (S' 𝔭)]
    [∀ (𝔭 : Ideal R) [𝔭.IsPrime], IsLocalization 𝔭.primeCompl (R' 𝔭)]
    (hinj : ∀ 𝔭 : Ideal R, Function.Injective (algebraMap S (S' 𝔭)))
    (h : ∀ 𝔭 : Ideal R, 𝔭.IsMaximal →
      Algebra.adjoin (R' 𝔭) {algebraMap S (S' 𝔭) θ} = ⊤) :
    Algebra.adjoin R {θ} = ⊤ :=
  Algebra.eq_top_iff.mpr fun _ =>
    mem_adjoin_of_forall_maximal_localization R' S' hinj
      fun 𝔭 h𝔭 => (h 𝔭 h𝔭).symm ▸ Algebra.mem_top

section Saturation

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **Monogenicity from `π`-saturation at the uniformisers of the localisations.**  Suppose
that for every maximal ideal `𝔭` of `R` and every prime element `π` of the localisation
`R' 𝔭`, the subalgebra generated by `θ` over `R' 𝔭` is `π`-saturated in `S' 𝔭`.  Then
`R[θ] = S`.

Over a Dedekind domain each `R' 𝔭` is a discrete valuation ring, hence a principal ideal
ring with a single prime element up to units — its uniformiser — so the hypothesis is a
single saturation check per maximal ideal, and `adjoin_eq_top_of_forall_prime_saturated'`
turns it into `R' 𝔭 [θ] = S' 𝔭`.  This is what removes the class number restriction from the
criteria stated at a prime element: the element one needs need only exist after localising,
where it always does. -/
theorem adjoin_eq_top_of_forall_maximal_forall_prime_saturated
    (R' S' : Ideal R → Type*)
    [∀ 𝔭 : Ideal R, CommRing (R' 𝔭)] [∀ 𝔭 : Ideal R, CommRing (S' 𝔭)]
    [∀ 𝔭 : Ideal R, Algebra R (R' 𝔭)] [∀ 𝔭 : Ideal R, Algebra (R' 𝔭) (S' 𝔭)]
    [∀ 𝔭 : Ideal R, Algebra R (S' 𝔭)] [∀ 𝔭 : Ideal R, Algebra S (S' 𝔭)]
    [∀ 𝔭 : Ideal R, IsScalarTower R (R' 𝔭) (S' 𝔭)]
    [∀ 𝔭 : Ideal R, IsScalarTower R S (S' 𝔭)]
    [∀ (𝔭 : Ideal R) [𝔭.IsPrime], IsLocalization 𝔭.primeCompl (R' 𝔭)]
    [∀ 𝔭 : Ideal R, IsDomain (R' 𝔭)] [∀ 𝔭 : Ideal R, IsIntegrallyClosed (R' 𝔭)]
    [∀ 𝔭 : Ideal R, IsPrincipalIdealRing (R' 𝔭)]
    [∀ 𝔭 : Ideal R, IsDomain (S' 𝔭)]
    [∀ 𝔭 : Ideal R, Algebra (R' 𝔭) K] [∀ 𝔭 : Ideal R, IsFractionRing (R' 𝔭) K]
    [Algebra.IsSeparable K L] [Module.Finite K L]
    [∀ 𝔭 : Ideal R, Algebra (S' 𝔭) L] [∀ 𝔭 : Ideal R, Algebra (R' 𝔭) L]
    [∀ 𝔭 : Ideal R, IsScalarTower (R' 𝔭) (S' 𝔭) L]
    [∀ 𝔭 : Ideal R, IsScalarTower (R' 𝔭) K L]
    [∀ 𝔭 : Ideal R, FaithfulSMul (S' 𝔭) L]
    [∀ 𝔭 : Ideal R, Algebra.IsIntegral (R' 𝔭) (S' 𝔭)]
    (hinj : ∀ 𝔭 : Ideal R, Function.Injective (algebraMap S (S' 𝔭)))
    (hgen : ∀ 𝔭 : Ideal R, 𝔭.IsMaximal →
      Algebra.adjoin K {algebraMap (S' 𝔭) L (algebraMap S (S' 𝔭) θ)} = ⊤)
    (hsat : ∀ 𝔭 : Ideal R, 𝔭.IsMaximal → ∀ π : R' 𝔭, Prime π → ∀ y : S' 𝔭,
      algebraMap (R' 𝔭) (S' 𝔭) π * y ∈ Algebra.adjoin (R' 𝔭) {algebraMap S (S' 𝔭) θ} →
      y ∈ Algebra.adjoin (R' 𝔭) {algebraMap S (S' 𝔭) θ}) :
    Algebra.adjoin R {θ} = ⊤ :=
  adjoin_eq_top_of_forall_maximal_localization_adjoin_eq_top R' S' hinj fun 𝔭 h𝔭 =>
    adjoin_eq_top_of_forall_prime_saturated' (K := K) (L := L) (hgen 𝔭 h𝔭) (hsat 𝔭 h𝔭)

end Saturation

end Monogenic
