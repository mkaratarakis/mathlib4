/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.ArtinRCF
import Mathlib.NumberTheory.Transcendental.ArtinRCFModel
import Mathlib.NumberTheory.Transcendental.ArtinQECriterion
import Mathlib.NumberTheory.Transcendental.ArtinQETransfer
import Mathlib.ModelTheory.QuantifierElimination

/-!
# Toward quantifier elimination for the theory of real closed fields

The entire Artin (scalar Hilbert 17) development is machine-checked and `sorry`-free modulo the
single
hypothesis `Artin.ModelTheory.Theory.RCF.HasQuantifierElimination` (see `ArtinTransfer`, `Artin`).
This file makes that obligation *concrete*: it reduces it, `sorry`-free, to the **one-existential-
quantifier elimination step** for `Theory.RCF`, which is the classical Tarski–Seidenberg core.

## The reduction (Marker, *Model Theory*, Theorem 3.1.5)

`FirstOrder.Language.Theory.hasQuantifierElimination_iff_ex_isQFEquivalent_of_isQF` says a theory
has
quantifier elimination as soon as, for every quantifier-free `θ` with a single bound variable, the
existential closure `θ.ex` is `T`-equivalent to a quantifier-free formula. So:

  `Theory.RCF.HasQuantifierElimination  ⟸  RCF_ex_isQFEquivalent`

is proved here with no `sorry`; the remaining content is exactly `RCF_ex_isQFEquivalent`.

## What `RCF_ex_isQFEquivalent` requires (the Sturm frontier)

A quantifier-free `θ(x, ā)` in one bound variable `x` (parameters `ā`) is a Boolean combination of
atomic `orderedRing`-formulas `t₁ = t₂`, `t₁ ≤ t₂`. In an ordered field each side realizes as a
**polynomial in `x`** whose coefficients are ring expressions in `ā`. Hence `θ(x, ā)` is equivalent
to a Boolean combination of sign conditions `pⱼ(x) = 0`, `pⱼ(x) ≥ 0`, and

  `∃ x, θ(x, ā)  ⟺  the sign-condition system on {pⱼ} is realizable`,

which, over a real closed field, is a **quantifier-free** condition on the coefficients `ā`. That
last step is the Tarski–Seidenberg content: the realizable sign conditions of a finite family of
univariate polynomials are determined by the coefficients via root counting — **Sturm's theorem**
(number of real roots in an interval = sign variations of the Sturm sequence at the endpoints).

Sturm's theorem is *not* in Mathlib, but it is fully formalized (`sorry`-free) in the companion
real-closed-field project (`SturmTarski/Theorem.lean`: `sturm_interval`, `sturm_R`,
`sturm_tarski_interval`). Completing `RCF_ex_isQFEquivalent` is therefore a matter of porting that
root-counting engine and threading it through the sign-condition decomposition — the natural next
step, isolated below.
-/

open FirstOrder Language

namespace Artin.ModelTheory

/-- **The one-existential-quantifier elimination step for `Theory.RCF`.**
For a quantifier-free formula `θ` in a single bound variable over the language of ordered rings,
its existential closure `θ.ex` is `Theory.RCF`-equivalent to a quantifier-free formula.

The proof combines the semantic compactness criterion `isQFEquivalent_of_qf_transfer` with the
quantifier-free-type transfer for real closed fields `realize_ex_transfer`: models of
`Theory.RCF` are real closed ordered fields (`rcfModelData`), and parameter tuples with the same
quantifier-free type in two such fields satisfy the same one-existential formulas — by Sturm-
theoretic root counting through a common real closure of the field their terms generate. -/
theorem RCF_ex_isQFEquivalent {α : Type} [Finite α]
    (θ : orderedRing.BoundedFormula α 1) (hθ : θ.IsQF) :
    Theory.RCF.IsQFEquivalent θ.ex := by
  apply isQFEquivalent_of_qf_transfer
  intro M N va vb htype
  obtain ⟨fM, loM, isoM, ircM, hagreeM⟩ := rcfModelData M
  obtain ⟨fN, loN, isoN, ircN, hagreeN⟩ := rcfModelData N
  letI := fM; letI := loM; haveI := isoM; haveI := ircM
  letI := fN; letI := loN; haveI := isoN; haveI := ircN
  -- the same-quantifier-free-type hypothesis, over the canonical structures
  have htypeC : ∀ δ : orderedRing.Formula α, δ.IsQF →
      (@Formula.Realize orderedRing M (canonicalOrderedRingStructure M) α δ va ↔
        @Formula.Realize orderedRing N (canonicalOrderedRingStructure N) α δ vb) :=
    fun δ hδ => (hagreeM δ va).symm.trans ((htype δ hδ).trans (hagreeN δ vb))
  have hMN : ∀ hva : @Formula.Realize orderedRing M
      (canonicalOrderedRingStructure M) α θ.ex va,
      @Formula.Realize orderedRing N (canonicalOrderedRingStructure N) α θ.ex vb := by
    intro hva
    have h1 : @BoundedFormula.Realize orderedRing M
        (canonicalOrderedRingStructure M) α 0 θ.ex va Fin.elim0 := by
      rw [show (Fin.elim0 : Fin 0 → M) = default from Subsingleton.elim _ _]
      exact hva
    have h2 := realize_ex_transfer va vb htypeC hθ h1
    show @BoundedFormula.Realize orderedRing N
      (canonicalOrderedRingStructure N) α 0 θ.ex vb default
    rw [show (default : Fin 0 → N) = Fin.elim0 from Subsingleton.elim _ _]
    exact h2
  have hNM : ∀ hvb : @Formula.Realize orderedRing N
      (canonicalOrderedRingStructure N) α θ.ex vb,
      @Formula.Realize orderedRing M (canonicalOrderedRingStructure M) α θ.ex va := by
    intro hvb
    have h1 : @BoundedFormula.Realize orderedRing N
        (canonicalOrderedRingStructure N) α 0 θ.ex vb Fin.elim0 := by
      rw [show (Fin.elim0 : Fin 0 → N) = default from Subsingleton.elim _ _]
      exact hvb
    have h2 := realize_ex_transfer vb va (fun δ hδ => (htypeC δ hδ).symm) hθ h1
    show @BoundedFormula.Realize orderedRing M
      (canonicalOrderedRingStructure M) α 0 θ.ex va default
    rw [show (default : Fin 0 → M) = Fin.elim0 from Subsingleton.elim _ _]
    exact h2
  exact ⟨fun hva => (hagreeN θ.ex vb).mpr (hMN ((hagreeM θ.ex va).mp hva)),
    fun hvb => (hagreeM θ.ex va).mpr (hNM ((hagreeN θ.ex vb).mp hvb))⟩

/-- **Quantifier elimination for `Theory.RCF`**, reduced (Marker 3.1.5,
`hasQuantifierElimination_iff_ex_isQFEquivalent_of_isQF`) to the one-quantifier step
`RCF_ex_isQFEquivalent`. This is `sorry`-free *given* that step; discharging it would make
`Artin.artin` unconditional. -/
theorem Theory.RCF_hasQuantifierElimination : Theory.RCF.HasQuantifierElimination :=
  FirstOrder.Language.Theory.hasQuantifierElimination_iff_ex_isQFEquivalent_of_isQF.mpr
    fun θ hθ => RCF_ex_isQFEquivalent θ hθ

end Artin.ModelTheory
