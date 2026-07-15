/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.RingTheory.ClassGroup.ExtendedHom
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-!
# Class group map induced by the relative ideal norm

Let `S / R` be a finite, torsion-free extension of Dedekind domains. In this file we extend the
relative ideal norm `Ideal.relNorm R : Ideal S →*₀ Ideal R` to fractional ideals, and descend it
to the class groups.

## Main definitions

- `FractionalIdeal.relNorm R K : FractionalIdeal S⁰ L →*₀ FractionalIdeal R⁰ K`: the relative
  norm on fractional ideals, defined as `Ideal.relNorm R I.num / Ideal.relNorm R ⟨I.den⟩`.
- `ClassGroup.relNorm R : ClassGroup S →* ClassGroup R`: the group homomorphism on class groups
  induced by the relative ideal norm. This is the map "going down", complementing
  `ClassGroup.extendedHom` which goes up.

## Main results

- `FractionalIdeal.relNorm_coeIdeal`: compatibility with `Ideal.relNorm` on integral ideals.
- `ClassGroup.relNorm_mk0`: compatibility with representatives as nonzero integral ideals.
- `ClassGroup.relNorm_relNorm`: transitivity of the relative norm in a tower `S / T / R`.
- `ClassGroup.relNorm_extendedHom`: the composite `ClassGroup R → ClassGroup S → ClassGroup R`
  is raising to the power `[Frac(S) : Frac(R)]`.

## TODO

- `FractionalIdeal.relNorm_spanSingleton`: identify the norm of a principal fractional ideal
  with the span of the field norm of its generator.
-/

@[expose] public section

open Module
open scoped Pointwise nonZeroDivisors

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
  {S : Type*} [CommRing S] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  {L : Type*} [Field L] [Algebra S L] [IsFractionRing S L]

namespace FractionalIdeal

theorem relNorm_div_eq_relNorm_div {I : FractionalIdeal S⁰ L} (a : S⁰) (I₀ : Ideal S)
    (h : a • (I : Submodule S L) = Submodule.map (Algebra.linearMap S L) I₀) :
    (Ideal.relNorm R I.num : FractionalIdeal R⁰ K) /
        (Ideal.relNorm R (Ideal.span {(I.den : S)}) : FractionalIdeal R⁰ K) =
      (Ideal.relNorm R I₀ : FractionalIdeal R⁰ K) /
        (Ideal.relNorm R (Ideal.span {(a : S)}) : FractionalIdeal R⁰ K) := by
  rw [div_eq_div_iff]
  · replace h := congr_arg (I.den • ·) h
    have h' := congr_arg (a • ·) (den_mul_self_eq_num I)
    rw [smul_comm] at h
    rw [h, Submonoid.smul_def, Submonoid.smul_def, ← Submodule.ideal_span_singleton_smul,
      ← Submodule.ideal_span_singleton_smul, ← Submodule.map_smul'', ← Submodule.map_smul'',
      (LinearMap.map_injective ?_).eq_iff, smul_eq_mul, smul_eq_mul] at h'
    · rw [← coeIdeal_mul, ← coeIdeal_mul, ← map_mul, ← map_mul, coeIdeal_inj,
        mul_comm I.num, mul_comm I₀, ← h']
    · exact LinearMap.ker_eq_bot.mpr (IsFractionRing.injective S L)
  all_goals
    rw [ne_eq, coeIdeal_eq_zero, Ideal.relNorm_eq_bot_iff, Ideal.span_singleton_eq_bot]
    exact nonZeroDivisors.coe_ne_zero _

/-- The relative norm of the fractional ideal `I`, extending by multiplicativity the relative
norm `Ideal.relNorm` on (integral) ideals. -/
noncomputable def relNorm : FractionalIdeal S⁰ L →*₀ FractionalIdeal R⁰ K where
  toFun I := (Ideal.relNorm R I.num : FractionalIdeal R⁰ K) /
    (Ideal.relNorm R (Ideal.span {(I.den : S)}) : FractionalIdeal R⁰ K)
  map_zero' := by
    rw [num_zero_eq (IsFractionRing.injective S L), Submodule.zero_eq_bot, Ideal.relNorm_bot,
      coeIdeal_bot, zero_div]
  map_one' := by
    rw [relNorm_div_eq_relNorm_div R K 1 ⊤ (by simp [Submodule.one_eq_range]),
      Ideal.relNorm_top, coeIdeal_top, OneMemClass.coe_one, Ideal.span_singleton_one,
      Ideal.relNorm_top, coeIdeal_top, div_one]
  map_mul' I J := by
    rw [relNorm_div_eq_relNorm_div R K (I.den * J.den) (I.num * J.num) (by
        have : Algebra.linearMap S L = (IsScalarTower.toAlgHom S S L).toLinearMap := rfl
        rw [coe_mul, this, Submodule.map_mul, ← this, ← den_mul_self_eq_num,
          ← den_mul_self_eq_num]
        exact Submodule.mul_smul_mul_eq_smul_mul_smul _ _ _ _),
      Submonoid.coe_mul, ← Ideal.span_singleton_mul_span_singleton, map_mul, map_mul,
      coeIdeal_mul, coeIdeal_mul, div_mul_div_comm]

theorem relNorm_eq (I : FractionalIdeal S⁰ L) :
    relNorm R K I = (Ideal.relNorm R I.num : FractionalIdeal R⁰ K) /
      (Ideal.relNorm R (Ideal.span {(I.den : S)}) : FractionalIdeal R⁰ K) := rfl

theorem relNorm_eq' {I : FractionalIdeal S⁰ L} (a : S⁰) (I₀ : Ideal S)
    (h : a • (I : Submodule S L) = Submodule.map (Algebra.linearMap S L) I₀) :
    relNorm R K I = (Ideal.relNorm R I₀ : FractionalIdeal R⁰ K) /
      (Ideal.relNorm R (Ideal.span {(a : S)}) : FractionalIdeal R⁰ K) := by
  rw [relNorm_eq, relNorm_div_eq_relNorm_div R K a I₀ h]

@[simp]
theorem relNorm_coeIdeal (I₀ : Ideal S) :
    relNorm R K (I₀ : FractionalIdeal S⁰ L) = Ideal.relNorm R I₀ := by
  rw [relNorm_eq' R K 1 I₀ (by rw [one_smul]; rfl), OneMemClass.coe_one,
    Ideal.span_singleton_one, Ideal.relNorm_top, coeIdeal_top, div_one]

@[simp]
theorem relNorm_eq_zero_iff {I : FractionalIdeal S⁰ L} :
    relNorm R K I = 0 ↔ I = 0 := by
  rw [relNorm_eq, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · rw [coeIdeal_eq_zero, Ideal.relNorm_eq_bot_iff, ← Submodule.zero_eq_bot] at h
      exact num_eq_zero_iff.mp h
    · rw [coeIdeal_eq_zero, Ideal.relNorm_eq_bot_iff, Ideal.span_singleton_eq_bot] at h
      exact absurd h (nonZeroDivisors.coe_ne_zero I.den)
  · rintro rfl
    left
    rw [num_zero_eq (IsFractionRing.injective S L), Submodule.zero_eq_bot, Ideal.relNorm_bot,
      coeIdeal_bot]

theorem exists_relNorm_spanSingleton_eq (x : L) :
    ∃ y : K, relNorm R K (spanSingleton S⁰ x) = spanSingleton R⁰ y := by
  obtain ⟨d, r, hr⟩ := IsLocalization.exists_integer_multiple S⁰ x
  refine ⟨algebraMap R K (Algebra.intNorm R S r) / algebraMap R K (Algebra.intNorm R S (d : S)),
    ?_⟩
  rw [relNorm_eq' R K d (Ideal.span {r})]
  · rw [Ideal.relNorm_singleton, Ideal.relNorm_singleton, coeIdeal_span_singleton,
      coeIdeal_span_singleton, spanSingleton_div_spanSingleton]
  · simp only [Submonoid.smul_def, coe_spanSingleton, Submodule.smul_span,
      Set.smul_set_singleton, Ideal.span, Submodule.map_span, Set.image_singleton,
      Algebra.linearMap_apply, hr]

end FractionalIdeal

namespace ClassGroup

open FractionalIdeal

/-- The group homomorphism `ClassGroup S → ClassGroup R` induced by the relative ideal norm of
a finite, torsion-free extension `S / R` of Dedekind domains. -/
noncomputable def relNorm : ClassGroup S →* ClassGroup R :=
  QuotientGroup.map _ _
    (Units.map (FractionalIdeal.relNorm R (FractionRing R) (L := FractionRing S)).toMonoidHom)
    (by
      rintro _ ⟨α, rfl⟩
      obtain ⟨y, hy⟩ := exists_relNorm_spanSingleton_eq R (FractionRing R) (S := S)
        (α : FractionRing S)
      have hy0 : y ≠ 0 := by
        rintro rfl
        rw [spanSingleton_zero] at hy
        exact α.ne_zero (spanSingleton_eq_zero_iff.mp
          ((relNorm_eq_zero_iff R (FractionRing R)).mp hy))
      refine ⟨Units.mk0 y hy0, ?_⟩
      simpa [coe_toPrincipalIdeal, Units.coe_map, Units.val_mk0] using! hy.symm)

@[simp]
lemma relNorm_quotientMk (α : (FractionalIdeal S⁰ (FractionRing S))ˣ) :
    relNorm R (QuotientGroup.mk α) = QuotientGroup.mk
      (Units.map (FractionalIdeal.relNorm R (FractionRing R)
        (L := FractionRing S)).toMonoidHom α) := by
  rfl

/-- The relative norm of a nonzero integral ideal, as a nonzero integral ideal. -/
noncomputable abbrev relNormIdeal (I : (Ideal S)⁰) : (Ideal R)⁰ :=
  ⟨Ideal.relNorm R I.1, mem_nonZeroDivisors_iff_ne_zero.mpr <| by
    rw [ne_eq, Submodule.zero_eq_bot, Ideal.relNorm_eq_bot_iff, ← Submodule.zero_eq_bot, ← ne_eq]
    exact mem_nonZeroDivisors_iff_ne_zero.mp I.2⟩

@[simp]
theorem relNorm_mk0 (I : (Ideal S)⁰) :
    relNorm R (ClassGroup.mk0 I) = ClassGroup.mk0 (relNormIdeal R I) := by
  rw [mk0_eq_quotientMk, mk0_eq_quotientMk, relNorm_quotientMk]
  congr
  ext : 1
  exact FractionalIdeal.relNorm_coeIdeal R (FractionRing R) (L := FractionRing S) I.1

section Tower

variable (T : Type*) [CommRing T] [IsDedekindDomain T] [Algebra R T] [Algebra T S]
  [IsScalarTower R T S] [Module.Finite R T] [Module.Finite T S]
  [Module.IsTorsionFree R T] [Module.IsTorsionFree T S]

@[simp]
theorem relNorm_relNorm (x : ClassGroup S) : relNorm R (relNorm T x) = relNorm R x := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective x
  rw [relNorm_mk0, relNorm_mk0, relNorm_mk0]
  congr 1
  exact Subtype.ext (Ideal.relNorm_relNorm R T I.1)

end Tower

attribute [local instance] FractionRing.liftAlgebra

/-- Extending an ideal class from `R` to `S` and taking its norm back down to `R` amounts to
raising it to the power `[Frac(S) : Frac(R)]`. -/
theorem relNorm_extendedHom (x : ClassGroup R) :
    relNorm R (extendedHom R S x) =
      x ^ Module.finrank (FractionRing R) (FractionRing S) := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective x
  rw [extendedHom_mk0, relNorm_mk0, ← map_pow]
  congr 1
  exact Subtype.ext (Ideal.relNorm_algebraMap S I.1)

end ClassGroup
