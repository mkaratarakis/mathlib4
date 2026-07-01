/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.ArtinSchreier
import Mathlib.NumberTheory.Transcendental.Hilbert17RealClosureOrder
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Transcendental.ArtinTransfer

/-!
# Artin's theorem (scalar Hilbert's 17th), reduced to the Tarski transfer principle

This file states **Artin's theorem** — a polynomial `f ∈ ℝ[xᵢ]` that is nonnegative at every real
point is a sum of squares in the rational function field `ℝ(xᵢ)` — and reduces it to **one** hard
ingredient, isolated as `Artin.exists_neg_eval_of_real_closed`:

> if `f`, evaluated through a ring hom into a real closed field `C ⊇ ℝ` at some point of `Cⁿ`, is
> negative, then `f` is already negative at some *real* point.

That is the **Tarski–Seidenberg transfer principle** (model completeness of real closed fields),
the one genuinely deep, not-yet-in-Mathlib component. Everything else here is the elementary
Artin–Schreier reduction, reusing the ordering and real-closure machinery developed for Hilbert's
17th problem for matrices (`RingPreordering.isSumSq_of_forall_mem`,
`Hilbert17Blueprint.exists_realClosure`); the reality of `ℝ(xᵢ)` (`IsSemireal`) is proved here by
clearing denominators and `MvPolynomial.funext`.

The transfer principle is itself no longer opaque: it is reduced, in
`Mathlib.NumberTheory.Transcendental.ArtinTransfer`, to model completeness of real closed fields
plus an eval↔formula dictionary, in Mathlib's first-order model theory. So the whole development
bottoms out at exactly those two model-theoretic obligations.

## Main statements

* `Artin.exists_neg_eval_of_real_closed` — the transfer principle (proved in `ArtinTransfer` from
  model completeness of real closed fields).
* `Artin.artin` — Artin's theorem, proved modulo the transfer principle.

## Architecture of the reduction

To show `f` is a sum of squares in `F := ℝ(xᵢ)` it suffices (Artin–Schreier) to show `f ≥ 0` in
every ordering `O` of `F`. Given such an `O`, equip `F` with the induced order and pass to a real
closure `C ⊇ F ⊇ ℝ` (`exists_realClosure`). If `f <_O 0` then `f < 0` in `C`; but `f`'s image in
`C` is `f` evaluated at the images of the indeterminates, so the transfer principle yields a real
point where `f < 0`, contradicting nonnegativity. Hence `f ≥ 0` in every ordering, so `f ∈ ΣF²`.
-/

open MvPolynomial

namespace Artin

variable {σ : Type*}

/-- The rational function field `ℝ(xᵢ)` in the indeterminates `σ`. -/
abbrev RatField (σ : Type*) : Type _ := FractionRing (MvPolynomial σ ℝ)

/-- **The isolated hard core: the Tarski–Seidenberg transfer principle.**
If a polynomial `f` with real coefficients, evaluated via a ring homomorphism `ψ : ℝ →+* C` into a
real closed field `C` at a point `ξ : σ → C`, takes a negative value, then `f` already takes a
negative value at some *real* point.

This is the model completeness of the theory of real closed fields (every real closed field is an
elementary extension of `ℝ`); it is the single genuinely deep, not-yet-in-Mathlib ingredient of
Artin's theorem. It is **reduced**, in `Mathlib.NumberTheory.Transcendental.ArtinTransfer`, to model
completeness of real closed fields (`Artin.ModelTheory.realClosed_elementaryEmbedding`) together
with the eval↔formula dictionary (`Artin.ModelTheory.elementaryEmbedding_reflect_exists_neg`). -/
theorem exists_neg_eval_of_real_closed
    (C : Type*) [Field C] [LinearOrder C] [IsStrictOrderedRing C] [IsRealClosed C]
    (ψ : ℝ →+* C) (ξ : σ → C) (f : MvPolynomial σ ℝ)
    (h : eval₂ ψ ξ f < 0) :
    ∃ a : σ → ℝ, eval a f < 0 :=
  ModelTheory.exists_neg_eval_of_real_closed C ψ ξ f h

/-- Evaluating a sum of squares of polynomials at a real point gives a sum of squares in `ℝ`. -/
private theorem isSumSq_eval {p : MvPolynomial σ ℝ} (hp : IsSumSq p) (pt : σ → ℝ) :
    IsSumSq (eval pt p) := by
  induction hp with
  | zero => rw [map_zero]; exact IsSumSq.zero
  | sq_add a _ ih => rw [map_add, map_mul]; exact ih.sq_add _

/-- Every sum of squares in `ℝ(xᵢ)` clears denominators: `x · q² = p` for a nonzero polynomial `q`
and a polynomial sum of squares `p`. -/
private theorem sumSq_clear {x : RatField σ} (hx : IsSumSq x) :
    ∃ p q : MvPolynomial σ ℝ, q ≠ 0 ∧ IsSumSq p ∧
      x * (algebraMap (MvPolynomial σ ℝ) (RatField σ) q) ^ 2
        = algebraMap (MvPolynomial σ ℝ) (RatField σ) p := by
  induction hx with
  | zero => exact ⟨0, 1, one_ne_zero, IsSumSq.zero, by simp⟩
  | @sq_add a S _ ih =>
    obtain ⟨p, q, hq, hp, hSeq⟩ := ih
    obtain ⟨na, da, hda, hna⟩ := IsFractionRing.div_surjective (A := MvPolynomial σ ℝ) a
    have hda0 : da ≠ 0 := nonZeroDivisors.ne_zero hda
    have hφda : algebraMap (MvPolynomial σ ℝ) (RatField σ) da ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hda0
    have hna' : algebraMap (MvPolynomial σ ℝ) (RatField σ) na
        = a * algebraMap (MvPolynomial σ ℝ) (RatField σ) da := (div_eq_iff hφda).1 hna
    refine ⟨(na * q) * (na * q) + p * (da * da), da * q, mul_ne_zero hda0 hq,
      (IsSumSq.mul_self _).add (hp.mul (IsSumSq.mul_self da)), ?_⟩
    simp only [map_add, map_mul]
    rw [hna', ← hSeq]; ring

instance : IsSemireal (RatField σ) where
  one_add_ne_zero {s} hs hc := by
    have hsq : IsSumSq (-1 : RatField σ) := eq_neg_of_add_eq_zero_right hc ▸ hs
    obtain ⟨p, q, hq, hp, heq⟩ := sumSq_clear hsq
    have hpq : p = -q ^ 2 := by
      apply IsFractionRing.injective (MvPolynomial σ ℝ) (RatField σ)
      rw [map_neg, map_pow, ← heq]; ring
    refine hq (MvPolynomial.funext fun pt => ?_)
    have h1 : (0 : ℝ) ≤ eval pt p := (isSumSq_eval hp pt).nonneg
    rw [hpq, map_neg, map_pow] at h1
    have h3 : eval pt q ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
    rw [map_zero]
    exact pow_eq_zero_iff (by norm_num) |>.1 h3

/-- **Artin's theorem (scalar Hilbert's 17th problem).** A polynomial `f ∈ ℝ[xᵢ]` that is
nonnegative at every real point is a sum of squares in the rational function field `ℝ(xᵢ)`.

Proved by the Artin–Schreier reduction modulo `exists_neg_eval_of_real_closed` (the transfer
principle). -/
theorem artin (f : MvPolynomial σ ℝ) (hf : ∀ a : σ → ℝ, 0 ≤ eval a f) :
    IsSumSq (algebraMap (MvPolynomial σ ℝ) (RatField σ) f) := by
  apply RingPreordering.isSumSq_of_forall_mem
  intro O hO
  haveI := hO
  letI : LinearOrder (RatField σ) := RingPreordering.toLinearOrder O
  letI : IsStrictOrderedRing (RatField σ) := RingPreordering.toIsStrictOrderedRing O
  rw [← RingPreordering.toLinearOrder_nonneg_iff (O := O)]
  by_contra hlt
  push Not at hlt
  obtain ⟨C, emb, hmono⟩ := (Hilbert17Blueprint.exists_realClosure (RatField σ)).some
  -- `f` maps to a negative element of the real closure `C`.
  have hemblt : emb (algebraMap (MvPolynomial σ ℝ) (RatField σ) f) < 0 := by
    have hle : emb (algebraMap (MvPolynomial σ ℝ) (RatField σ) f) ≤ 0 := by
      have := hmono hlt.le; rwa [map_zero] at this
    refine lt_of_le_of_ne hle (fun heq => ?_)
    exact absurd (emb.injective (heq.trans (map_zero emb).symm)) (ne_of_lt hlt)
  -- Express that image as `f` evaluated at the images of the indeterminates.
  set Φ : MvPolynomial σ ℝ →+* C :=
    emb.comp (algebraMap (MvPolynomial σ ℝ) (RatField σ)) with hΦ
  have hΦeq : Φ = eval₂Hom (Φ.comp MvPolynomial.C) (fun i => Φ (X i)) := by
    apply MvPolynomial.ringHom_ext <;> intro <;> simp
  have key : eval₂ (Φ.comp MvPolynomial.C) (fun i => Φ (X i)) f = Φ f := by
    simpa using (RingHom.congr_fun hΦeq.symm f)
  have hlt2 : eval₂ (Φ.comp MvPolynomial.C) (fun i => Φ (X i)) f < 0 := by
    rw [key]; exact hemblt
  -- Transfer the negativity to a real point and contradict nonnegativity.
  obtain ⟨a, ha⟩ := exists_neg_eval_of_real_closed C (Φ.comp MvPolynomial.C)
    (fun i => Φ (X i)) f hlt2
  exact absurd (hf a) (not_le.2 ha)

end Artin
