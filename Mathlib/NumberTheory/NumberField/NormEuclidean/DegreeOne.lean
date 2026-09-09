/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Primes of residue degree one and integers that are exactly divisible by a norm

Let `K` be a number field and let `θ ∈ 𝓞 K` be a root of a polynomial `f ∈ ℤ[X]`.  If `q` is a
rational prime that divides the norm of some algebraic integer of `K` exactly once, then some
prime of `𝓞 K` above `q` has residue field `ZMod q`, and reducing `θ` there exhibits a root of
`f` modulo `q`.

Contrapositively, `NumberField.norm_ne_mul_of_forall_eval_ne_zero`: if `f` has no root modulo
`q`, then `u * q` is not the norm of an algebraic integer whenever `q ∤ u`.  This sign-free
statement is what is needed to feed Heilbronn's criterion, and it is strictly stronger than the
more familiar "`q` is not a norm".

## Main results

* `NumberField.exists_isMaximal_mem_of_dvd_norm`: if `q ∣ N α` then some maximal ideal contains
  both `α` and `q`.
* `NumberField.exists_eval_eq_zero_of_dvd_norm`: if `q ∣ N α` but `q ^ 2 ∤ N α` then `f` has a
  root modulo `q`.
* `NumberField.norm_ne_mul_of_forall_eval_ne_zero`: if `f` has no root modulo `q` and `q ∤ u`,
  then no algebraic integer has norm `u * q`.
-/

public section

open NumberField Polynomial

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- If a rational prime `q` divides the norm of `α ∈ 𝓞 K`, then some maximal ideal of `𝓞 K`
contains both `α` and `q`. -/
theorem exists_isMaximal_mem_of_dvd_norm {q : ℕ} (hq : q.Prime) {α : 𝓞 K} (hα : α ≠ 0)
    (h : (q : ℤ) ∣ Algebra.norm ℤ α) :
    ∃ 𝔮 : Ideal (𝓞 K), 𝔮.IsMaximal ∧ α ∈ 𝔮 ∧ (q : 𝓞 K) ∈ 𝔮 := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  set R := 𝓞 K ⧸ Ideal.span {α} with hR
  set J : Ideal (𝓞 K) := Ideal.span {α, (q : 𝓞 K)} with hJ
  have hnormne : Algebra.norm ℤ α ≠ 0 := fun h0 =>
    hα ((Algebra.norm_eq_zero_iff (S := 𝓞 K)).1 h0)
  have hcard : Ideal.absNorm (Ideal.span {α}) = (Algebra.norm ℤ α).natAbs :=
    Ideal.absNorm_span_singleton α
  have hne : Ideal.absNorm (Ideal.span {α}) ≠ 0 := by
    rw [hcard, Int.natAbs_ne_zero]; exact hnormne
  haveI hfin : Finite R := (Ideal.absNorm_ne_zero_iff _).1 hne
  haveI hfty : Fintype R := Fintype.ofFinite _
  have hNatCard : Ideal.absNorm (Ideal.span {α}) = Fintype.card R := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hJne : J ≠ ⊤ := by
    intro htop
    -- if `α` and `q` generate the unit ideal then `q` is invertible modulo `α`
    have h1 : (1 : 𝓞 K) ∈ J := htop ▸ Submodule.mem_top
    rw [hJ, Ideal.mem_span_pair] at h1
    obtain ⟨c, d, hcd⟩ := h1
    have hinv : (Ideal.Quotient.mk (Ideal.span {α}) d) * (q : R) = 1 := by
      have h2 : (Ideal.Quotient.mk (Ideal.span {α})) (c * α + d * (q : 𝓞 K)) = 1 := by
        rw [hcd]; simp
      rw [map_add, map_mul, map_mul] at h2
      simpa [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self α)] using h2
    -- but the residue ring has order divisible by `q`
    have hdvd : q ∣ Fintype.card R := by
      rw [← hNatCard, hcard, ← Int.natAbs_natCast (n := q)]
      exact Int.natAbs_dvd_natAbs.2 h
    obtain ⟨r, hr⟩ := exists_prime_addOrderOf_dvd_card (G := R) q hdvd
    have hr0 : r ≠ 0 := by
      intro h0
      rw [h0, addOrderOf_zero] at hr
      exact hq.one_lt.ne' hr.symm
    have hqr : (q : R) * r = 0 := by
      rw [← nsmul_eq_mul, ← hr]
      exact addOrderOf_nsmul_eq_zero r
    refine hr0 ?_
    calc r = ((Ideal.Quotient.mk (Ideal.span {α}) d) * (q : R)) * r := by rw [hinv, one_mul]
      _ = (Ideal.Quotient.mk (Ideal.span {α}) d) * ((q : R) * r) := by ring
      _ = 0 := by rw [hqr, mul_zero]
  obtain ⟨𝔮, h𝔮max, h𝔮le⟩ := Ideal.exists_le_maximal J hJne
  exact ⟨𝔮, h𝔮max, h𝔮le (Ideal.subset_span (by simp)),
    h𝔮le (Ideal.subset_span (by simp))⟩

/-- If a rational prime `q` divides the norm of some `α ∈ 𝓞 K` exactly once, then every
polynomial with integer coefficients having a root in `𝓞 K` has a root modulo `q`. -/
theorem exists_eval_eq_zero_of_dvd_norm {q : ℕ} (hq : q.Prime) {θ : 𝓞 K} {f : ℤ[X]}
    (hf : aeval θ f = 0) {α : 𝓞 K} (h1 : (q : ℤ) ∣ Algebra.norm ℤ α)
    (h2 : ¬ ((q : ℤ) ^ 2 ∣ Algebra.norm ℤ α)) :
    ∃ r : ZMod q, eval₂ (Int.castRingHom (ZMod q)) r f = 0 := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hα : α ≠ 0 := by
    rintro rfl
    exact h2 (by simp)
  obtain ⟨𝔮, h𝔮max, hα𝔮, hq𝔮⟩ := exists_isMaximal_mem_of_dvd_norm hq hα h1
  -- the residue field
  have hdvdN : (Ideal.absNorm 𝔮 : ℤ) ∣ Algebra.norm ℤ α := Ideal.absNorm_dvd_norm_of_mem hα𝔮
  have hNne : Ideal.absNorm 𝔮 ≠ 0 := by
    intro h0
    rw [h0] at hdvdN
    simp only [Nat.cast_zero, zero_dvd_iff] at hdvdN
    exact hα ((Algebra.norm_eq_zero_iff (S := 𝓞 K)).1 hdvdN)
  haveI hfin : Finite (𝓞 K ⧸ 𝔮) := (Ideal.absNorm_ne_zero_iff _).1 hNne
  haveI hfty : Fintype (𝓞 K ⧸ 𝔮) := Fintype.ofFinite _
  have hcardN : Fintype.card (𝓞 K ⧸ 𝔮) = Ideal.absNorm 𝔮 := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have h0 : ((q : ℕ) : 𝓞 K ⧸ 𝔮) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk 𝔮)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (by exact_mod_cast hq𝔮)
  -- `q` lies in `𝔮`, so the norm of `𝔮` divides a power of `q`, hence is a power of `q`
  have hspan : Ideal.span {(q : 𝓞 K)} ≤ 𝔮 := (Ideal.span_singleton_le_iff_mem _).2 hq𝔮
  have hdvdq : Ideal.absNorm 𝔮 ∣ q ^ Module.finrank ℤ (𝓞 K) := by
    have := Ideal.absNorm_dvd_absNorm_of_le hspan
    rwa [Ideal.absNorm_span_natCast] at this
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hq).1 hdvdq
  -- `k = 1`: it is at least one since `𝔮 ≠ ⊤`, and at most one since `q ^ 2 ∤ N α`
  have hntop : Ideal.absNorm 𝔮 ≠ 1 := fun h => h𝔮max.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have hk1 : k = 1 := by
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k
      · exact absurd (by simpa using hk) hntop
      · rfl
    · exfalso
      refine h2 (dvd_trans ?_ hdvdN)
      rw [hk]
      exact_mod_cast pow_dvd_pow (q : ℤ) h
  have hcardq : Fintype.card (𝓞 K ⧸ 𝔮) = q := by rw [hcardN, hk, hk1, pow_one]
  -- hence the residue field has `q` elements; it has characteristic `q`
  haveI hnt : Nontrivial (𝓞 K ⧸ 𝔮) := Ideal.Quotient.nontrivial_iff.2 h𝔮max.ne_top
  have hchar : ringChar (𝓞 K ⧸ 𝔮) = q := by
    rcases (Nat.Prime.eq_one_or_self_of_dvd hq _ (ringChar.dvd h0)) with h | h
    · exfalso
      haveI hc : CharP (𝓞 K ⧸ 𝔮) 1 := ringChar.of_eq h
      have h1 : ((1 : ℕ) : 𝓞 K ⧸ 𝔮) = 0 := (CharP.cast_eq_zero_iff _ 1 1).2 dvd_rfl
      simp only [Nat.cast_one] at h1
      exact one_ne_zero h1
    · exact h
  haveI hcp : CharP (𝓞 K ⧸ 𝔮) q := ringChar.of_eq hchar
  -- the residue field is `ZMod q`
  set c : ZMod q →+* 𝓞 K ⧸ 𝔮 := ZMod.castHom dvd_rfl _ with hc
  have hcinj : Function.Injective c := RingHom.injective c
  have hcsurj : Function.Surjective c := by
    have : Fintype.card (ZMod q) = Fintype.card (𝓞 K ⧸ 𝔮) := by rw [ZMod.card, hcardq]
    exact (Fintype.bijective_iff_injective_and_card c).2 ⟨hcinj, this⟩ |>.2
  obtain ⟨r, hr⟩ := hcsurj (Ideal.Quotient.mk 𝔮 θ)
  refine ⟨r, hcinj ?_⟩
  rw [map_zero, hom_eval₂, hr]
  have hcomp : c.comp (Int.castRingHom (ZMod q)) = Int.castRingHom (𝓞 K ⧸ 𝔮) :=
    RingHom.ext_int _ _
  rw [hcomp]
  have : (Int.castRingHom (𝓞 K ⧸ 𝔮)) =
      (Ideal.Quotient.mk 𝔮).comp (Int.castRingHom (𝓞 K)) := RingHom.ext_int _ _
  rw [this, ← hom_eval₂]
  have heq : eval₂ (Int.castRingHom (𝓞 K)) θ f = aeval θ f := by
    rw [aeval_def]
    congr 1
  rw [heq, hf, map_zero]

/-- **The form of Lemma 2.3 that Heilbronn's criterion needs.**  If `f ∈ ℤ[X]` has a root in
`𝓞 K` but no root modulo the prime `q`, then `u * q` is not the norm of an algebraic integer of
`K`, for any `u` not divisible by `q`.  (The statement is insensitive to signs, so it applies
equally to `a = u q₁` and to `-b = -v q₂`.) -/
theorem norm_ne_mul_of_forall_eval_ne_zero {q : ℕ} (hq : q.Prime) {θ : 𝓞 K} {f : ℤ[X]}
    (hf : aeval θ f = 0) (hroot : ∀ r : ZMod q, eval₂ (Int.castRingHom (ZMod q)) r f ≠ 0)
    {u : ℤ} (hu : ¬ (q : ℤ) ∣ u) (α : 𝓞 K) : Algebra.norm ℤ α ≠ u * q := by
  intro hN
  have h1 : (q : ℤ) ∣ Algebra.norm ℤ α := ⟨u, by rw [hN, mul_comm]⟩
  have h2 : ¬ ((q : ℤ) ^ 2 ∣ Algebra.norm ℤ α) := by
    rw [hN, sq]
    intro hdvd
    exact hu ((mul_dvd_mul_iff_right (by exact_mod_cast hq.ne_zero : (q : ℤ) ≠ 0)).1
      (by simpa [mul_comm] using hdvd))
  obtain ⟨r, hr⟩ := exists_eval_eq_zero_of_dvd_norm hq hf h1 h2
  exact hroot r hr

end NumberField
