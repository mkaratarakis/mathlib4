/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.NumberTheory.Transcendental.Baker.SchneiderLang
public import Mathlib.RingTheory.Algebraic.Integral

/-!
# Baker's theorem from the criterion of Schneider–Lang

This file carries out §4.2 of [waldschmidt2000]: the deduction of Baker's theorem on
linear forms in logarithms from the criterion of Schneider–Lang, following the argument of
D. Bertrand and D. W. Masser.

The set `L` of logarithms of algebraic numbers, written here as
`IsAlgebraic ℚ (Complex.exp x)`, is first shown to be a `ℚ`-vector subspace of `ℂ`.
The main intermediate statement is Theorem 4.5 of [waldschmidt2000]: if `β₁, …, β_d` is a
`ℚ`-basis of a number field `K` of degree `d` and `ℓ₁, …, ℓ_d` lie in `L` with
`β₁ℓ₁ + ⋯ + β_dℓ_d` algebraic, then all the `ℓ i` vanish.

## Main statements

* `Transcendental.isAlgebraic_exp_ratCast_mul`, `Transcendental.isAlgebraic_exp_sum`:
  `L` is a `ℚ`-subspace of `ℂ`.
* `Transcendental.theorem45`: **Theorem 4.5** of [waldschmidt2000].
* `Transcendental.baker_of_theorem45`: **Theorem 1.6** of [waldschmidt2000], the
  nonhomogeneous case of Baker's theorem; this is §4.2.5 of the book and is what
  discharges the statement `Transcendental.baker`.

## References

* [M. Waldschmidt, *Diophantine Approximation on Linear Algebraic
  Groups*][waldschmidt2000], Chapter 4, §4.2
-/

@[expose] public section

open Complex Finset

namespace Transcendental

/-- A rational multiple of a logarithm of an algebraic number is again one: together with
`isAlgebraic_exp_sum` this says that the set `L` of [waldschmidt2000] is a `ℚ`-vector
subspace of `ℂ`. -/
theorem isAlgebraic_exp_ratCast_mul {l : ℂ} (hl : IsAlgebraic ℚ (exp l)) (q : ℚ) :
    IsAlgebraic ℚ (exp ((q : ℂ) * l)) := by
  refine IsAlgebraic.of_pow (n := q.den) q.pos ?_
  rw [← Complex.exp_nat_mul]
  have hden : (q.den : ℂ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hq : (q.den : ℂ) * ((q : ℂ) * l) = (q.num : ℂ) * l := by
    rw [Rat.cast_def]; field_simp
  rw [hq, Complex.exp_int_mul]
  rcases q.num with m | m
  · simpa using hl.pow m
  · simpa [zpow_negSucc] using (hl.pow (m + 1)).inv

/-- A sum of logarithms of algebraic numbers is a logarithm of an algebraic number. -/
theorem isAlgebraic_exp_sum {ι : Type*} (s : Finset ι) (l : ι → ℂ)
    (hl : ∀ i ∈ s, IsAlgebraic ℚ (exp (l i))) : IsAlgebraic ℚ (exp (∑ i ∈ s, l i)) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using isAlgebraic_one
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Complex.exp_add]
    exact (hl a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => hl i (Finset.mem_insert_of_mem hi))

/-- A `ℚ`-linear combination of logarithms of algebraic numbers is one. -/
theorem isAlgebraic_exp_ratCast_combo {ι : Type*} [Fintype ι] (c : ι → ℚ) (l : ι → ℂ)
    (hl : ∀ i, IsAlgebraic ℚ (exp (l i))) :
    IsAlgebraic ℚ (exp (∑ i, (c i : ℂ) * l i)) :=
  isAlgebraic_exp_sum _ _ fun i _ => isAlgebraic_exp_ratCast_mul (hl i) (c i)

/-- **Theorem 4.5** of [waldschmidt2000].

Let `K` be a number field of degree `d`, let `β` be a `ℚ`-basis of `K`, and let
`ℓ₁, …, ℓ_d` be logarithms of algebraic numbers.  If `β₁ℓ₁ + ⋯ + β_dℓ_d` is algebraic,
then `ℓ₁ = ⋯ = ℓ_d = 0`.

The proof (§4.2.4 of [waldschmidt2000]) splits into three cases according to how many of
the numbers `Aᵢ = ∑ₖ βₖ^{σᵢ} ℓₖ` vanish, and applies `schneiderLang_zero` in the first
case and `schneiderLang_one` in the second. -/
theorem theorem45 (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] {d : ℕ}
    (hd : Module.finrank ℚ K = d) (β : Fin d → K) (hβ : LinearIndependent ℚ β)
    (l : Fin d → ℂ) (hl : ∀ i, IsAlgebraic ℚ (exp (l i)))
    (hsum : IsAlgebraic ℚ (∑ i, (β i : ℂ) * l i)) :
    ∀ i, l i = 0 := by
  sorry


/-- **Theorem 1.6** of [waldschmidt2000], the nonhomogeneous case of Baker's theorem,
deduced from `theorem45` as in §4.2.5 of the book.

If `ℓ₁, …, ℓ_m` are `ℚ`-linearly independent logarithms of algebraic numbers and
`γ₀ + γ₁ℓ₁ + ⋯ + γ_mℓ_m = 0` with all `γ` algebraic, then every coefficient vanishes. -/
theorem baker_of_theorem45 {m : ℕ} (l : Fin m → ℂ) (hl : ∀ j, IsAlgebraic ℚ (exp (l j)))
    (hli : LinearIndependent ℚ l) {γ₀ : ℂ} {γ : Fin m → ℂ}
    (hγ₀ : IsAlgebraic ℚ γ₀) (hγ : ∀ j, IsAlgebraic ℚ (γ j)) (hrel : γ₀ + ∑ j, γ j * l j = 0) :
    γ₀ = 0 ∧ ∀ j, γ j = 0 := by
  classical
  -- The number field `K = ℚ(γ₁, …, γ_m)` and a `ℚ`-basis `B` of it.
  set K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (Set.range γ) with hK
  haveI : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin fun x hx => by
      obtain ⟨j, rfl⟩ := hx; exact (hγ j).isIntegral
  set d : ℕ := Module.finrank ℚ K with hdK
  set B : Module.Basis (Fin d) ℚ K := Module.finBasis ℚ K with hB
  have hγK : ∀ j, γ j ∈ K := fun j =>
    IntermediateField.subset_adjoin ℚ (Set.range γ) ⟨j, rfl⟩
  -- Coordinates of the `γ j` in the basis `B`.
  set c : Fin m → Fin d → ℚ := fun j i => B.repr ⟨γ j, hγK j⟩ i with hc
  have hγc : ∀ j, γ j = ∑ i, (c j i : ℂ) * (B i : ℂ) := by
    intro j
    have h := B.sum_repr ⟨γ j, hγK j⟩
    have := congrArg (fun z : K => (z : ℂ)) h
    simpa [IntermediateField.coe_sum, Algebra.smul_def, mul_comm] using this.symm
  -- The new logarithms `ℓ'ᵢ = ∑ⱼ c j i ℓⱼ` still lie in `L`.
  set l' : Fin d → ℂ := fun i => ∑ j, (c j i : ℂ) * l j with hl'def
  have hl' : ∀ i, IsAlgebraic ℚ (exp (l' i)) := fun i =>
    isAlgebraic_exp_ratCast_combo (fun j => c j i) l hl
  -- Rearranging the double sum turns the given relation into the one Theorem 4.5 needs.
  have key : ∑ i, (B i : ℂ) * l' i = ∑ j, γ j * l j := by
    simp only [hl'def, Finset.mul_sum, Finset.sum_comm (s := Finset.univ (α := Fin d))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hγc j, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsum : IsAlgebraic ℚ (∑ i, (B i : ℂ) * l' i) := by
    rw [key, show ∑ j, γ j * l j = -γ₀ by linear_combination hrel]
    exact hγ₀.neg
  -- Theorem 4.5 kills the `ℓ'ᵢ`, and independence of the `ℓⱼ` then kills the coordinates.
  have hzero := theorem45 K rfl B B.linearIndependent l' hl' hsum
  have hc0 : ∀ j i, c j i = 0 := by
    intro j i
    have h : ∑ j, c j i • l j = 0 := by
      have := hzero i
      rw [hl'def] at this
      simpa [Rat.smul_def] using this
    exact Fintype.linearIndependent_iff.mp hli (fun j => c j i) h j
  have hγ0 : ∀ j, γ j = 0 := by
    intro j
    rw [hγc j]
    simp [hc0 j]
  exact ⟨by simpa [hγ0] using hrel, hγ0⟩


end Transcendental
