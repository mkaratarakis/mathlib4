/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.Baker.Basic

/-!
# Baker's theorem: reduction to the normalized form

This file carries out §3 ("Notation") of Chapter 2 of [baker1975]: the reduction of
Baker's theorem (`Transcendental.baker`) to the derivation of a contradiction from a
*normalized* counterexample, in which the coefficient of one distinguished logarithm
is `-1`.  In the book's notation, assuming the theorem false one may suppose
`β₀ + β₁ log α₁ + ⋯ + β_{n-1} log α_{n-1} = log αₙ`, that is,
`e^{β₀} α₁^{β₁} ⋯ α_{n-1}^{β_{n-1}} = αₙ`  (equation (1) of Chapter 2).

## Main declarations

* `Transcendental.BakerData`: the data of a normalized counterexample to Baker's theorem:
  a finite family of `ℚ`-linearly independent logarithms `l i` of algebraic numbers, a
  distinguished index `r`, algebraic coefficients `β₀` and `β i` with `β r = -1`, and the
  relation `β₀ + ∑ i, β i * l i = 0`.
* `Transcendental.BakerData.rel_erase`: the relation in the book's form (1),
  `β₀ + ∑_{i ≠ r} β i * l i = l r`.
* `Transcendental.exists_bakerData_of_baker_counterexample`: any counterexample to
  Baker's theorem yields a `BakerData`.
* `Transcendental.baker_of_isEmpty_bakerData`: consequently, to prove Baker's theorem
  it suffices to show `IsEmpty BakerData`.  This is what the remainder of the
  formalization of Chapter 2 of [baker1975] (Lemmas 1–8, in subsequent files) will do.

## References

* [A. Baker, *Transcendental Number Theory*][baker1975], Chapter 2, §3
-/

open Complex Finset

namespace Transcendental

/-- The data of a *normalized counterexample* to Baker's theorem, as in §3 of Chapter 2
of [baker1975]: `ℚ`-linearly independent logarithms `l i` of algebraic numbers indexed by
a finite type, algebraic coefficients `β₀`, `β i` satisfying
`β₀ + ∑ i, β i * l i = 0`, normalized so that the coefficient of a distinguished
logarithm `l r` is `-1`.

Baker's theorem is equivalent to `IsEmpty BakerData`
(see `Transcendental.baker_of_isEmpty_bakerData`). -/
structure BakerData where
  /-- The index type (the book has `Fin (n+1)`, indexing `log α₁, ..., log α_{n+1}`). -/
  ι : Type
  /-- The index type is finite. -/
  [fintype_ι : Fintype ι]
  /-- The distinguished index (the book's `n`, for the term `log αₙ`). -/
  r : ι
  /-- The fixed determinations of the logarithms of the algebraic numbers `αᵢ`. -/
  l : ι → ℂ
  /-- The coefficients `β₁, ..., βₙ`. -/
  β : ι → ℂ
  /-- The constant coefficient `β₀`. -/
  β₀ : ℂ
  /-- The normalization `βₙ = -1`. -/
  hβr : β r = -1
  /-- The coefficients are algebraic. -/
  hβ : ∀ i, IsAlgebraic ℚ (β i)
  /-- The constant coefficient is algebraic. -/
  hβ₀ : IsAlgebraic ℚ β₀
  /-- Each `l i` is a logarithm of an algebraic number. -/
  halg : ∀ i, IsAlgebraic ℚ (exp (l i))
  /-- The logarithms are linearly independent over `ℚ`. -/
  hli : LinearIndependent ℚ l
  /-- The nontrivial linear relation with algebraic coefficients. -/
  hrel : β₀ + ∑ i, β i * l i = 0

attribute [instance] BakerData.fintype_ι

namespace BakerData

variable (d : BakerData)

open scoped Classical in
/-- The relation of a `BakerData` in the form of equation (1) of Chapter 2 of
[baker1975] (in additive form): `β₀ + ∑_{i ≠ r} β i * l i = l r`; exponentiating gives
`e^{β₀} α₁^{β₁} ⋯ α_{n-1}^{β_{n-1}} = αₙ`. -/
theorem rel_erase : d.β₀ + ∑ i ∈ Finset.univ.erase d.r, d.β i * d.l i = d.l d.r := by
  have hsplit : ∑ i, d.β i * d.l i
      = d.β d.r * d.l d.r + ∑ i ∈ Finset.univ.erase d.r, d.β i * d.l i := by
    conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ d.r)]
    rw [Finset.sum_insert (Finset.notMem_erase d.r Finset.univ)]
  have h := d.hrel
  rw [hsplit, d.hβr] at h
  linear_combination h

/-- No logarithm in a `BakerData` vanishes; in particular the `αᵢ` differ from `1`,
so that a normalized counterexample has "genuine" logarithms. -/
theorem l_ne_zero (i : d.ι) : d.l i ≠ 0 := by
  intro h
  exact d.hli.ne_zero i h

end BakerData

variable {ι : Type*} [Fintype ι]

/-- §3 of Chapter 2 of [baker1975]: a counterexample to Baker's theorem
`Transcendental.baker` can be normalized so that the coefficient of one of the
logarithms is `-1`, yielding a `BakerData`. -/
theorem exists_bakerData_of_baker_counterexample {l : ι → ℂ}
    (hl : ∀ i, IsAlgebraic ℚ (exp (l i))) (hli : LinearIndependent ℚ l)
    {β₀ : ℂ} {β : ι → ℂ} (hβ₀ : IsAlgebraic ℚ β₀) (hβ : ∀ i, IsAlgebraic ℚ (β i))
    (hrel : β₀ + ∑ i, β i * l i = 0) (hne : ¬(β₀ = 0 ∧ ∀ i, β i = 0)) :
    Nonempty BakerData := by
  -- Some coefficient `β r` is nonzero (else the relation forces `β₀ = 0` as well).
  have hr : ∃ r, β r ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne ⟨by simpa [h] using hrel, h⟩
  obtain ⟨r, hr⟩ := hr
  -- Transport along `Fin (card ι) ≃ ι` and divide the relation by `-β r`.
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hdiv : ∀ x : ℂ, IsAlgebraic ℚ x → IsAlgebraic ℚ (-x / β r) := by
    intro x hx
    rw [div_eq_mul_inv]
    exact _root_.IsAlgebraic.mul (_root_.IsAlgebraic.neg hx) (_root_.IsAlgebraic.inv (hβ r))
  refine ⟨⟨Fin (Fintype.card ι), Fintype.equivFin ι r, fun j => l (e j),
    fun j => -β (e j) / β r, -β₀ / β r, ?_, fun j => hdiv _ (hβ (e j)), hdiv _ hβ₀,
    fun j => hl (e j), ?_, ?_⟩⟩
  · show -β ((Fintype.equivFin ι).symm (Fintype.equivFin ι r)) / β r = -1
    rw [Equiv.symm_apply_apply, neg_div, div_self hr]
  · exact (linearIndependent_equiv e).mpr hli
  · show -β₀ / β r + ∑ j, -β (e j) / β r * l (e j) = 0
    have hsum : ∑ j, -β (e j) / β r * l (e j) = ∑ i, -β i / β r * l i :=
      Equiv.sum_comp e fun i => -β i / β r * l i
    have hexpand : ∑ i, -β i / β r * l i = (∑ i, β i * l i) * (-1 / β r) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hs : ∑ i, β i * l i = -β₀ := by linear_combination hrel
    rw [hsum, hexpand, hs]
    ring

/-- To prove Baker's theorem, it suffices to derive a contradiction from a normalized
counterexample: this is the goal of the formalization of Lemmas 1–8 of Chapter 2 of
[baker1975].  Once `IsEmpty BakerData` is established, this theorem will discharge the
`sorry` in `Transcendental.baker`. -/
theorem baker_of_isEmpty_bakerData (h : IsEmpty BakerData) {l : ι → ℂ}
    (hl : ∀ i, IsAlgebraic ℚ (exp (l i))) (hli : LinearIndependent ℚ l)
    {β₀ : ℂ} {β : ι → ℂ} (hβ₀ : IsAlgebraic ℚ β₀) (hβ : ∀ i, IsAlgebraic ℚ (β i))
    (hrel : β₀ + ∑ i, β i * l i = 0) : β₀ = 0 ∧ ∀ i, β i = 0 := by
  by_contra hne
  exact h.false
    (exists_bakerData_of_baker_counterexample hl hli hβ₀ hβ hrel hne).some

end Transcendental
