/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Baker's theorem on linear forms in logarithms

This file contains the statement of **Baker's theorem** on linear forms in logarithms
(Theorem 2.1 of [baker1975]) together with complete derivations of its classical
corollaries (Theorems 2.2–2.4 of [baker1975]), including the transcendence of `π`
and the Gelfond–Schneider theorem.

Throughout, "`l` is a logarithm of an algebraic number" is encoded as
`IsAlgebraic ℚ (Complex.exp l)`; this captures the book's convention that the logarithms
`log α₁, ..., log αₙ` may take *any* fixed determinations.

## Main statements

* `Transcendental.baker`: **Baker's theorem** (Theorem 2.1 of [baker1975]).
  If `l i` are `ℚ`-linearly independent logarithms of algebraic numbers, then
  `1` and the `l i` are linearly independent over the algebraic numbers: a relation
  `β₀ + ∑ i, β i * l i = 0` with all coefficients algebraic forces every coefficient
  to vanish.  **The proof is under development**; this is the single `sorry` of this
  file, and the remainder of the directory `Mathlib/NumberTheory/Transcendental/Baker/`
  will be devoted to its proof, following Chapter 2 of [baker1975].
* `Transcendental.baker_add_sum_ne_zero`: Theorem 2.2 of [baker1975], in the form
  "`β₀ + β₁ log α₁ + ⋯ + βₙ log αₙ ≠ 0` whenever `β₀ ≠ 0`".
* `Transcendental.baker_transcendental_sum`: Theorem 2.2 of [baker1975]: any nonvanishing
  linear combination of logarithms of algebraic numbers with algebraic coefficients is
  transcendental.
* `Transcendental.baker_transcendental_exp`: Theorem 2.3 of [baker1975]:
  `e^{β₀} α₁^{β₁} ⋯ αₙ^{βₙ}` is transcendental for algebraic `β₀ ≠ 0` and algebraic `βᵢ`.
* `Transcendental.baker_transcendental_exp_sum`: Theorem 2.4 of [baker1975]:
  `α₁^{β₁} ⋯ αₙ^{βₙ}` is transcendental when `1, β₁, ..., βₙ` are `ℚ`-linearly independent
  algebraic numbers and the `αᵢ` have nonzero logarithms.
* `Transcendental.transcendental_pi`: `π` is transcendental (a special case of the above;
  of course it is also a consequence of the Lindemann–Weierstrass theorem).
* `Transcendental.gelfond_schneider`: the **Gelfond–Schneider theorem**: `a ^ b` is
  transcendental for algebraic `a ≠ 0, 1` and algebraic irrational `b`.

## Proof strategy for `Transcendental.baker`

The proof in Chapter 2 of [baker1975] is by contradiction, via the auxiliary function
`Φ(z₀, ..., z_{n-1}) = ∑ p(λ₀, ..., λₙ) z₀^{λ₀} e^{λₙ β₀ z₀} α₁^{γ₁ z₁} ⋯ α_{n-1}^{γ_{n-1} z_{n-1}}`
constructed by the pigeonhole principle (Siegel's lemma, already in Mathlib as
`Int.Matrix.exists_ne_zero_int_vec_norm_le`), an extrapolation argument that trades
derivative order for interpolation range (Lemmas 3–5 of [baker1975]), a Liouville-type
lower bound (Lemma 6), and a special interpolation polynomial (Lemma 7).
These will be formalized in subsequent files in this directory.

## References

* [A. Baker, *Transcendental Number Theory*][baker1975]
-/

open Complex Finset

namespace Transcendental

variable {ι : Type*}

/-- **Baker's theorem** on linear forms in logarithms (Theorem 2.1 of [baker1975]).

If the complex numbers `l i` are linearly independent over `ℚ` and each is the logarithm
of an algebraic number (in the sense that `exp (l i)` is algebraic over `ℚ`, the branch
being arbitrary), then `1` together with the `l i` is linearly independent over the field
of all algebraic numbers: any relation `β₀ + ∑ i, β i * l i = 0` with algebraic
coefficients is trivial.

The proof, following Chapter 2 of [baker1975], is under development in
`Mathlib/NumberTheory/Transcendental/Baker/`. -/
theorem baker [Fintype ι] {l : ι → ℂ} (hl : ∀ i, IsAlgebraic ℚ (exp (l i)))
    (hli : LinearIndependent ℚ l) {β₀ : ℂ} {β : ι → ℂ}
    (hβ₀ : IsAlgebraic ℚ β₀) (hβ : ∀ i, IsAlgebraic ℚ (β i))
    (hrel : β₀ + ∑ i, β i * l i = 0) : β₀ = 0 ∧ ∀ i, β i = 0 := by
  sorry

/-- Every rational number, coerced into `ℂ`, is algebraic over `ℚ`. -/
private theorem isAlgebraic_ratCast (q : ℚ) : IsAlgebraic ℚ (q : ℂ) := by
  simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℂ) q

/-- `Finset` version of Baker's theorem `Transcendental.baker`, with the linear
independence hypothesis phrased via `LinearIndepOn`. -/
theorem baker_linearIndepOn {s : Finset ι} {l : ι → ℂ}
    (hl : ∀ i ∈ s, IsAlgebraic ℚ (exp (l i))) (hli : LinearIndepOn ℚ l s)
    {β₀ : ℂ} {β : ι → ℂ} (hβ₀ : IsAlgebraic ℚ β₀) (hβ : ∀ i ∈ s, IsAlgebraic ℚ (β i))
    (hrel : β₀ + ∑ i ∈ s, β i * l i = 0) : β₀ = 0 ∧ ∀ i ∈ s, β i = 0 := by
  have key : β₀ = 0 ∧ ∀ i : {x // x ∈ s}, β i = 0 := by
    refine baker (l := fun i : {x // x ∈ s} => l i) (β := fun i : {x // x ∈ s} => β i)
      (fun i => hl i i.2) hli hβ₀ (fun i => hβ i i.2) ?_
    rwa [Finset.sum_coe_sort s fun i => β i * l i]
  exact ⟨key.1, fun i hi => key.2 ⟨i, hi⟩⟩

section Theorem22

/-- Auxiliary induction for Theorem 2.2 of [baker1975], performed over a `Finset`.
If each `l i`, `i ∈ s`, is a logarithm of an algebraic number, and `β₀` and the `β i`
are algebraic with `β₀ ≠ 0`, then `β₀ + ∑ i ∈ s, β i * l i ≠ 0`.

The induction (on `s`) removes an index participating in a rational linear relation
among the `l i` until the remaining logarithms are `ℚ`-linearly independent, at which
point Baker's theorem applies. -/
private theorem baker_aux_theorem22 (s : Finset ι) :
    ∀ (l β : ι → ℂ) (β₀ : ℂ), (∀ i ∈ s, IsAlgebraic ℚ (exp (l i))) →
      IsAlgebraic ℚ β₀ → (∀ i ∈ s, IsAlgebraic ℚ (β i)) → β₀ ≠ 0 →
      β₀ + ∑ i ∈ s, β i * l i ≠ 0 := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s IH =>
    intro l β β₀ hl hβ₀ hβ hβ₀0 hrel
    by_cases hli : LinearIndepOn ℚ l s
    · exact hβ₀0 (baker_linearIndepOn hl hli hβ₀ hβ hrel).1
    · -- Extract a nontrivial rational relation `∑ i ∈ s, ρ i • l i = 0`, `ρ r ≠ 0`.
      rw [linearIndepOn_finset_iff] at hli
      push_neg at hli
      obtain ⟨ρ, hρ0, r, hrs, hρr⟩ := hli
      have hρ0' : ∑ i ∈ s, (ρ i : ℂ) * l i = 0 := by
        simpa only [Rat.smul_def] using hρ0
      have hsplit : ∀ f : ι → ℂ, ∑ i ∈ s, f i = f r + ∑ i ∈ s.erase r, f i := fun f => by
        conv_lhs => rw [← Finset.insert_erase hrs]
        rw [Finset.sum_insert (Finset.notMem_erase r s)]
      -- Pass to `s.erase r` with the modified coefficients `ρ r • β i - ρ i • β r`.
      have h1 : ∑ i ∈ s.erase r, β i * l i = (∑ i ∈ s, β i * l i) - β r * l r := by
        rw [hsplit fun i => β i * l i]; ring
      have h2 : ∑ i ∈ s.erase r, (ρ i : ℂ) * l i = -((ρ r : ℂ) * l r) := by
        rw [hsplit fun i => (ρ i : ℂ) * l i] at hρ0'
        linear_combination hρ0'
      have hexpand : ∑ i ∈ s.erase r, ((ρ r : ℂ) * β i - (ρ i : ℂ) * β r) * l i
          = (ρ r : ℂ) * ∑ i ∈ s.erase r, β i * l i
            - β r * ∑ i ∈ s.erase r, (ρ i : ℂ) * l i := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      refine IH (s.erase r) (Finset.erase_ssubset hrs) l
        (fun i => (ρ r : ℂ) * β i - (ρ i : ℂ) * β r) ((ρ r : ℂ) * β₀)
        (fun i hi => hl i (Finset.mem_of_mem_erase hi))
        ((isAlgebraic_ratCast (ρ r)).mul hβ₀)
        (fun i hi => ((isAlgebraic_ratCast (ρ r)).mul (hβ i (Finset.mem_of_mem_erase hi))).sub
          ((isAlgebraic_ratCast (ρ i)).mul (hβ r hrs)))
        (mul_ne_zero (by exact_mod_cast hρr) hβ₀0) ?_
      rw [hexpand, h1, h2]
      linear_combination (ρ r : ℂ) * hrel

variable [Fintype ι]

/-- **Theorem 2.2** of [baker1975], nonvanishing form: if each `l i` is a logarithm of
an algebraic number, and `β₀` and the `β i` are algebraic with `β₀ ≠ 0`, then
`β₀ + β₁ l₁ + ⋯ + βₙ lₙ ≠ 0`. -/
theorem baker_add_sum_ne_zero {l : ι → ℂ} (hl : ∀ i, IsAlgebraic ℚ (exp (l i)))
    {β₀ : ℂ} {β : ι → ℂ} (hβ₀ : IsAlgebraic ℚ β₀) (hβ : ∀ i, IsAlgebraic ℚ (β i))
    (hβ₀0 : β₀ ≠ 0) : β₀ + ∑ i, β i * l i ≠ 0 :=
  baker_aux_theorem22 Finset.univ l β β₀ (fun i _ => hl i) hβ₀ (fun i _ => hβ i) hβ₀0

/-- **Theorem 2.2** of [baker1975]: any nonvanishing linear combination of logarithms of
algebraic numbers with algebraic coefficients is transcendental. -/
theorem baker_transcendental_sum {l : ι → ℂ} (hl : ∀ i, IsAlgebraic ℚ (exp (l i)))
    {β : ι → ℂ} (hβ : ∀ i, IsAlgebraic ℚ (β i)) (hΛ : ∑ i, β i * l i ≠ 0) :
    Transcendental ℚ (∑ i, β i * l i) := fun halg =>
  baker_add_sum_ne_zero hl halg.neg hβ (neg_ne_zero.mpr hΛ) (neg_add_cancel _)

/-- **Theorem 2.3** of [baker1975]: `e^{β₀} α₁^{β₁} ⋯ αₙ^{βₙ}` is transcendental for
algebraic numbers `β₀ ≠ 0` and `β i`, where `αᵢ = exp (l i)` are algebraic.
(The case of an empty index type is the Hermite–Lindemann theorem: `e^{β₀}` is
transcendental for algebraic `β₀ ≠ 0`.) -/
theorem baker_transcendental_exp {l : ι → ℂ} (hl : ∀ i, IsAlgebraic ℚ (exp (l i)))
    {β₀ : ℂ} {β : ι → ℂ} (hβ₀ : IsAlgebraic ℚ β₀) (hβ : ∀ i, IsAlgebraic ℚ (β i))
    (hβ₀0 : β₀ ≠ 0) : Transcendental ℚ (exp (β₀ + ∑ i, β i * l i)) := by
  intro halg
  refine baker_add_sum_ne_zero (ι := Option ι)
    (l := fun o => o.elim (β₀ + ∑ i, β i * l i) l) (β := fun o => o.elim (-1) β)
    (fun o => ?_) hβ₀ (fun o => ?_) hβ₀0 ?_
  · cases o with
    | none => exact halg
    | some i => exact hl i
  · cases o with
    | none => exact isAlgebraic_one.neg
    | some i => exact hβ i
  · rw [Fintype.sum_option]
    show β₀ + ((-1) * (β₀ + ∑ i, β i * l i) + ∑ i, β i * l i) = 0
    ring

end Theorem22

section Theorem24

/-- Auxiliary induction for Theorem 2.4 of [baker1975]: if the logarithms `l i`, `i ∈ s`,
of algebraic numbers are all nonzero and the algebraic coefficients `β i` are linearly
independent over `ℚ`, then `∑ i ∈ s, β i * l i ≠ 0` (for nonempty `s`). -/
private theorem baker_aux_theorem24 (s : Finset ι) :
    ∀ (l β : ι → ℂ), (∀ i ∈ s, IsAlgebraic ℚ (exp (l i))) → (∀ i ∈ s, l i ≠ 0) →
      (∀ i ∈ s, IsAlgebraic ℚ (β i)) → LinearIndepOn ℚ β s → s.Nonempty →
      ∑ i ∈ s, β i * l i ≠ 0 := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s IH =>
    intro l β hl hl0 hβ hβli hne hrel
    by_cases hli : LinearIndepOn ℚ l s
    · -- If the logarithms are independent, Baker's theorem with `β₀ = 0` forces all
      -- coefficients to vanish, contradicting their linear independence.
      obtain ⟨i₀, hi₀⟩ := hne
      have key := baker_linearIndepOn hl hli isAlgebraic_zero hβ (by rw [zero_add]; exact hrel)
      exact hβli.ne_zero (Finset.mem_coe.mpr hi₀) (key.2 i₀ hi₀)
    · -- Otherwise remove an index participating in a rational relation among the `l i`.
      rw [linearIndepOn_finset_iff] at hli
      push_neg at hli
      obtain ⟨ρ, hρ0, r, hrs, hρr⟩ := hli
      have hρ0' : ∑ i ∈ s, (ρ i : ℂ) * l i = 0 := by
        simpa only [Rat.smul_def] using hρ0
      have hsplit : ∀ f : ι → ℂ, ∑ i ∈ s, f i = f r + ∑ i ∈ s.erase r, f i := fun f => by
        conv_lhs => rw [← Finset.insert_erase hrs]
        rw [Finset.sum_insert (Finset.notMem_erase r s)]
      rcases (s.erase r).eq_empty_or_nonempty with he | hne'
      · -- If `s = {r}`, the relation reads `ρ r • l r = 0`, contradicting `l r ≠ 0`.
        have hs : s = {r} := by
          rcases (Finset.erase_eq_empty_iff s r).mp he with h | h
          · exact absurd (h ▸ hrs) (Finset.notMem_empty r)
          · exact h
        rw [hs, Finset.sum_singleton] at hρ0'
        exact hl0 r hrs ((mul_eq_zero.mp hρ0').resolve_left (by exact_mod_cast hρr))
      · -- Otherwise pass to `s.erase r` with coefficients `β' i = ρ r • β i - ρ i • β r`.
        set t := s.erase r with ht
        set β' : ι → ℂ := fun i => (ρ r : ℂ) * β i - (ρ i : ℂ) * β r with hβ'def
        have h1 : ∑ i ∈ t, β i * l i = (∑ i ∈ s, β i * l i) - β r * l r := by
          rw [hsplit fun i => β i * l i]; ring
        have h2 : ∑ i ∈ t, (ρ i : ℂ) * l i = -((ρ r : ℂ) * l r) := by
          rw [hsplit fun i => (ρ i : ℂ) * l i] at hρ0'
          linear_combination hρ0'
        have hexpand : ∑ i ∈ t, β' i * l i
            = (ρ r : ℂ) * ∑ i ∈ t, β i * l i - β r * ∑ i ∈ t, (ρ i : ℂ) * l i := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun i _ => by rw [hβ'def]; ring
        -- Linear independence of the new coefficients over `ℚ`.
        have hβ'li : LinearIndepOn ℚ β' t := by
          rw [linearIndepOn_finset_iff]
          intro q hq j hj
          have hq' : ∑ i ∈ t, (q i : ℂ) * β' i = 0 := by
            simpa only [Rat.smul_def] using hq
          have hqe : (ρ r : ℂ) * (∑ i ∈ t, (q i : ℂ) * β i)
              - (∑ i ∈ t, (q i : ℂ) * (ρ i : ℂ)) * β r = 0 := by
            rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← hq']
            exact Finset.sum_congr rfl fun i _ => by rw [hβ'def]; ring
          -- Assemble coefficients for the original family `β` over `s`.
          set c : ι → ℚ := fun i => if i = r then -(∑ k ∈ t, q k * ρ k) else q i * ρ r
            with hcdef
          have hcrel : ∑ i ∈ s, c i • β i = 0 := by
            rw [hsplit fun i => c i • β i]
            have hcr : c r = -(∑ k ∈ t, q k * ρ k) := if_pos rfl
            have hct : ∑ i ∈ t, c i • β i = ∑ i ∈ t, (q i * ρ r) • β i :=
              Finset.sum_congr rfl fun i hi => by
                rw [hcdef]
                simp only [if_neg (Finset.ne_of_mem_erase hi)]
            rw [hcr, hct]
            simp only [Rat.smul_def]
            push_cast
            have g1 : ∑ i ∈ t, ((q i : ℂ) * (ρ r : ℂ)) * β i
                = (ρ r : ℂ) * ∑ i ∈ t, (q i : ℂ) * β i := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun i _ => by ring
            rw [g1]
            linear_combination hqe
          rw [linearIndepOn_finset_iff] at hβli
          have hcj := hβli c hcrel j (Finset.mem_of_mem_erase hj)
          rw [hcdef] at hcj
          simp only [if_neg (Finset.ne_of_mem_erase hj)] at hcj
          exact (mul_eq_zero.mp hcj).resolve_right hρr
        refine IH t (Finset.erase_ssubset hrs) l β'
          (fun i hi => hl i (Finset.mem_of_mem_erase hi))
          (fun i hi => hl0 i (Finset.mem_of_mem_erase hi))
          (fun i hi => ((isAlgebraic_ratCast (ρ r)).mul (hβ i (Finset.mem_of_mem_erase hi))).sub
            ((isAlgebraic_ratCast (ρ i)).mul (hβ r hrs)))
          hβ'li hne' ?_
        rw [hexpand, h1, h2, hrel]
        ring

variable [Fintype ι]

/-- The key step towards Theorem 2.4 of [baker1975]: if the `l i` are nonzero logarithms
of algebraic numbers and the algebraic numbers `β i` are linearly independent over `ℚ`,
then `β₁ l₁ + ⋯ + βₙ lₙ ≠ 0` (for a nonempty index type). -/
theorem baker_sum_ne_zero [Nonempty ι] {l : ι → ℂ} (hl : ∀ i, IsAlgebraic ℚ (exp (l i)))
    (hl0 : ∀ i, l i ≠ 0) {β : ι → ℂ} (hβ : ∀ i, IsAlgebraic ℚ (β i))
    (hβli : LinearIndependent ℚ β) : ∑ i, β i * l i ≠ 0 :=
  baker_aux_theorem24 Finset.univ l β (fun i _ => hl i) (fun i _ => hl0 i) (fun i _ => hβ i)
    (by rwa [Finset.coe_univ, linearIndepOn_univ]) Finset.univ_nonempty

/-- **Theorem 2.4** of [baker1975]: `α₁^{β₁} ⋯ αₙ^{βₙ} = exp (∑ i, β i * l i)` is
transcendental, where the `l i` are nonzero logarithms of the algebraic numbers `αᵢ`
and `1, β₁, ..., βₙ` are algebraic numbers linearly independent over `ℚ`.
(The hypothesis on the family `1, β₁, ..., βₙ` is encoded by extending `β` over
`Option ι`, with `none` carrying the coefficient `1`.) -/
theorem baker_transcendental_exp_sum [Nonempty ι] {l : ι → ℂ}
    (hl : ∀ i, IsAlgebraic ℚ (exp (l i))) (hl0 : ∀ i, l i ≠ 0)
    {β : ι → ℂ} (hβ : ∀ i, IsAlgebraic ℚ (β i))
    (hβli : LinearIndependent ℚ (fun o : Option ι => o.elim 1 β)) :
    Transcendental ℚ (exp (∑ i, β i * l i)) := by
  intro halg
  have hβli' : LinearIndependent ℚ β :=
    hβli.comp some (Option.some_injective ι)
  have hS0 : (∑ i, β i * l i) ≠ 0 := baker_sum_ne_zero hl hl0 hβ hβli'
  -- Extend the family by the new logarithm `∑ i, β i * l i` of the algebraic number
  -- `exp (∑ i, β i * l i)`, with coefficient `-1`.
  have hβ'li : LinearIndependent ℚ (fun o : Option ι => o.elim (-1) β) := by
    have := hβli.units_smul fun o : Option ι => o.elim (-1) 1
    convert this using 1
    funext o
    cases o with
    | none => simp
    | some i => simp
  refine baker_aux_theorem24 (Finset.univ : Finset (Option ι))
    (fun o => o.elim (∑ i, β i * l i) l) (fun o => o.elim (-1) β)
    (fun o _ => ?_) (fun o _ => ?_) (fun o _ => ?_)
    (by rwa [Finset.coe_univ, linearIndepOn_univ]) Finset.univ_nonempty ?_
  · cases o with
    | none => exact halg
    | some i => exact hl i
  · cases o with
    | none => exact hS0
    | some i => exact hl0 i
  · cases o with
    | none => exact isAlgebraic_one.neg
    | some i => exact hβ i
  · rw [Fintype.sum_option]
    show (-1) * (∑ i, β i * l i) + ∑ i, β i * l i = 0
    ring

end Theorem24

section Applications

/-- `I` is algebraic over `ℚ` (it is a root of `X² + 1`). -/
private theorem isAlgebraic_I : IsAlgebraic ℚ (I : ℂ) :=
  ⟨Polynomial.X ^ 2 + Polynomial.C 1, (Polynomial.monic_X_pow_add_C 1 two_ne_zero).ne_zero,
    by simp [Complex.I_sq]⟩

/-- **The transcendence of `π`**, as a consequence of (the statement of) Baker's theorem:
`π * I` is a nonzero logarithm of the algebraic number `-1`, hence transcendental by
Theorem 2.2 of [baker1975]. -/
theorem transcendental_pi : Transcendental ℚ (Real.pi : ℝ) := by
  intro halg
  have hπC : IsAlgebraic ℚ ((Real.pi : ℂ)) := by
    have : (Real.pi : ℂ) = algebraMap ℝ ℂ Real.pi := rfl
    rw [this, isAlgebraic_algebraMap_iff (algebraMap ℝ ℂ).injective]
    exact halg
  have hπI : Transcendental ℚ ((Real.pi : ℂ) * I) := by
    have h := baker_transcendental_sum (ι := Unit) (l := fun _ => (Real.pi : ℂ) * I)
      (fun _ => by rw [Complex.exp_pi_mul_I]; exact isAlgebraic_one.neg)
      (β := fun _ => 1) (fun _ => isAlgebraic_one) ?_
    · simpa using h
    · simp only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_smul]
      exact mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) I_ne_zero
  exact hπI (hπC.mul isAlgebraic_I)

/-- **The Gelfond–Schneider theorem** (a special case of Theorem 2.4 of [baker1975]):
if `a` is algebraic with `a ≠ 0, 1`, and `b` is algebraic irrational, then `a ^ b` is
transcendental.  Here `a ^ b = exp (b * log a)` is the principal determination. -/
theorem gelfond_schneider {a b : ℂ} (ha : IsAlgebraic ℚ a) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (hb : IsAlgebraic ℚ b) (hb' : ∀ q : ℚ, b ≠ (q : ℂ)) :
    Transcendental ℚ (a ^ b) := by
  have hlog0 : Complex.log a ≠ 0 := fun h =>
    ha1 (by rw [← Complex.exp_log ha0, h, Complex.exp_zero])
  have hind : LinearIndependent ℚ (fun o : Option Unit => o.elim 1 fun _ => b) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg o
    have hsum : (g none : ℂ) + (g (some ()) : ℂ) * b = 0 := by
      have := hg
      rw [Fintype.sum_option] at this
      simpa [Rat.smul_def] using this
    have hg1 : g (some ()) = 0 := by
      by_contra hne
      have hgC : (g (some ()) : ℂ) ≠ 0 := by exact_mod_cast hne
      have hbq : b = -(g none : ℂ) / (g (some ()) : ℂ) := by
        rw [eq_div_iff hgC]
        linear_combination hsum
      exact hb' (-(g none) / g (some ())) (hbq.trans (by push_cast; ring))
    have hg0 : g none = 0 := by
      rw [hg1] at hsum
      exact_mod_cast by simpa using hsum
    cases o with
    | none => exact hg0
    | some u => cases u; exact hg1
  have h := baker_transcendental_exp_sum (ι := Unit) (l := fun _ => Complex.log a)
    (fun _ => by rwa [Complex.exp_log ha0]) (fun _ => hlog0)
    (β := fun _ => b) (fun _ => hb) hind
  rw [cpow_def_of_ne_zero ha0]
  simpa [mul_comm] using h

end Applications

end Transcendental
