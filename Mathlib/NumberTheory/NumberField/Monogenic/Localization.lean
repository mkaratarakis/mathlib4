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

* `Monogenic.adjoin_eq_top_of_forall_maximal_exists_notMem`: consequently, if at every maximal
  ideal some element outside it clears every `β` into `R[θ]`, then `R[θ] = S` — no saturation
  hypothesis at all.  The pointwise step is `mem_adjoin_of_forall_maximal_exists_smul_mem`
  in `Mathlib.NumberTheory.NumberField.Monogenic.Base`.

* `Monogenic.mem_adjoin_of_forall_maximal_localizedAt` and
  `Monogenic.adjoin_eq_top_of_forall_maximal_localizedAt`: the localised criterion, at the
  concrete localisations `Localization 𝔭.primeCompl` and `LocalizedAt S 𝔭`.  If the localised
  question has a positive answer at every maximal ideal, then `R[θ] = S`.

  These are stated at the actual localisations rather than at an abstract family
  `R' S' : Ideal R → Type*`, because such a family cannot be instantiated at the intended
  example: `Ideal.primeCompl` takes an `IsPrime` instance, so `fun 𝔭 => Localization.AtPrime 𝔭`
  is not a well-formed function on all of `Ideal R`.

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

/-- **Monogenity is local.**  If, for every `β : S` and every maximal ideal `𝔭` of `R`, some
element outside `𝔭` clears `β` into `R[θ]`, then `R[θ] = S`.

The pointwise statement is `mem_adjoin_of_forall_maximal_exists_smul_mem`. -/
theorem adjoin_eq_top_of_forall_maximal_exists_notMem
    (h : ∀ β : S, ∀ 𝔭 : Ideal R, 𝔭.IsMaximal → ∃ t : R, t ∉ 𝔭 ∧
      algebraMap R S t * β ∈ Algebra.adjoin R {θ}) :
    Algebra.adjoin R {θ} = ⊤ :=
  Algebra.eq_top_iff.mpr fun β => mem_adjoin_of_forall_maximal_exists_smul_mem (h β)

section AtPrime

/-- The localisation of `S` at (the image of) the complement of `𝔭`. -/
abbrev LocalizedAt (S : Type*) [CommRing S] [Algebra R S] (𝔭 : Ideal R) [𝔭.IsPrime] : Type _ :=
  Localization (Algebra.algebraMapSubmonoid S 𝔭.primeCompl)

/-- **Monogenity may be checked at the localisations, concretely.**  If for every maximal
ideal `𝔭` the image of `β` lies in `R_𝔭[θ]`, then `β` already lies in `R[θ]`.

This is the form that can actually be applied: the localisations are the concrete
`Localization 𝔭.primeCompl` and `LocalizedAt S 𝔭`, so no data has to be supplied. -/
theorem mem_adjoin_of_forall_maximal_localizedAt {β : S}
    (hinj : ∀ (𝔭 : Ideal R) [𝔭.IsPrime],
      Function.Injective (algebraMap S (LocalizedAt S 𝔭)))
    (h : ∀ (𝔭 : Ideal R) (h𝔭 : 𝔭.IsMaximal),
      letI := h𝔭.isPrime
      algebraMap S (LocalizedAt S 𝔭) β ∈
        Algebra.adjoin (Localization 𝔭.primeCompl) {algebraMap S (LocalizedAt S 𝔭) θ}) :
    β ∈ Algebra.adjoin R {θ} := by
  refine mem_adjoin_of_forall_maximal_exists_smul_mem fun 𝔭 h𝔭 => ?_
  haveI := h𝔭.isPrime
  exact exists_smul_mem_adjoin_of_mem_localization_adjoin
    𝔭.primeCompl (Localization 𝔭.primeCompl) (LocalizedAt S 𝔭) (hinj 𝔭) (h 𝔭 h𝔭)

/-- **Monogenicity is detected by the localisations, concretely.**  If `R_𝔭[θ]` is everything
for every maximal ideal `𝔭` of `R`, then `R[θ] = S`.

This is the statement that removes the class number restriction in usable form: each
`Localization 𝔭.primeCompl` of a Dedekind domain is a discrete valuation ring, so its
maximal ideal is generated by a uniformiser, and a criterion stated at a prime *element*
applies there even when `𝔭` itself is not principal. -/
theorem adjoin_eq_top_of_forall_maximal_localizedAt
    (hinj : ∀ (𝔭 : Ideal R) [𝔭.IsPrime],
      Function.Injective (algebraMap S (LocalizedAt S 𝔭)))
    (h : ∀ (𝔭 : Ideal R) (h𝔭 : 𝔭.IsMaximal),
      letI := h𝔭.isPrime
      Algebra.adjoin (Localization 𝔭.primeCompl) {algebraMap S (LocalizedAt S 𝔭) θ} = ⊤) :
    Algebra.adjoin R {θ} = ⊤ :=
  Algebra.eq_top_iff.mpr fun _ =>
    mem_adjoin_of_forall_maximal_localizedAt hinj fun 𝔭 h𝔭 => by
      letI := h𝔭.isPrime
      rw [h 𝔭 h𝔭]; exact Algebra.mem_top

end AtPrime

end Monogenic
