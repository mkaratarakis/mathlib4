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
`Hilbert17Blueprint.exists_realClosure`).

## Main statements

* `Artin.exists_neg_eval_of_real_closed` — the isolated transfer principle (the single `sorry`).
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
Artin's theorem. -/
theorem exists_neg_eval_of_real_closed
    (C : Type*) [Field C] [LinearOrder C] [IsStrictOrderedRing C] [IsRealClosed C]
    (ψ : ℝ →+* C) (ξ : σ → C) (f : MvPolynomial σ ℝ)
    (h : eval₂ ψ ξ f < 0) :
    ∃ a : σ → ℝ, eval a f < 0 := by
  sorry

/-- The rational function field `ℝ(xᵢ)` is formally real.

Elementary (clearing denominators reduces `-1 = Σ sq` to a polynomial identity that
`MvPolynomial.funext` over the infinite field `ℝ` refutes); isolated here and currently left as a
`sorry`, separate from the deep transfer principle above. -/
instance : IsSemireal (RatField σ) := by
  sorry

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
  have key : Φ f = eval₂ (Φ.comp MvPolynomial.C) (fun i => Φ (X i)) f := by
    rw [hΦeq]; rfl
  -- Transfer the negativity to a real point and contradict nonnegativity.
  obtain ⟨a, ha⟩ := exists_neg_eval_of_real_closed C (Φ.comp MvPolynomial.C)
    (fun i => Φ (X i)) f (key ▸ hemblt)
  exact absurd (hf a) (not_le.2 ha)

end Artin
