/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.ModelTheory.QuantifierElimination
import Mathlib.ModelTheory.Satisfiability

/-!
# A semantic criterion for quantifier-free equivalence

The classical compactness criterion (Marker, *Model Theory*, Thm. 3.1.4), in a
**quantifier-free-type** formulation that avoids substructures and diagrams: if the truth of a
formula `φ` transfers between any two models of `T` at parameter tuples with the same
quantifier-free type, then `φ` is `T`-equivalent to a quantifier-free formula
(`isQFEquivalent_of_qf_transfer`).

The proof is the standard double application of compactness:
* `Γ` is the set of quantifier-free consequences of `φ` over `T`. To see `T ∪ Γ ⊨ φ`, take a
  model-with-assignment `(M, v)` of `T ∪ Γ` and consider `Σ = T ∪ qftp(v) ∪ {φ}` (over the
  language with constants for the parameters, `satisfiable_union_iff`). If `Σ` has a model
  `(N, w)`, then `v` and `w` have the same quantifier-free type (quantifier-free formulas are
  closed under negation), so truth of `φ` transfers to `(M, v)`. If not, compactness produces a
  finite `Δ₀ ⊆ qftp(v)` with `T ⊨ φ → ¬⋀Δ₀`; then `¬⋀Δ₀ ∈ Γ` is realized by `v`,
  contradicting `Δ₀ ⊆ qftp(v)`.
* Compactness again extracts a finite `Γ₀ ⊆ Γ` with `T ∪ Γ₀ ⊨ φ`, and `ψ = ⋀Γ₀` is the
  quantifier-free equivalent.

Everything is stated for languages and variable types in `Type 0`, which is what the application
to `Theory.RCF` (`RCF_ex_isQFEquivalent`) requires.
-/

open FirstOrder Language BoundedFormula

namespace Artin.ModelTheory

variable {L : Language.{0, 0}} {T : L.Theory} {α : Type}

/-! ### Finite conjunctions of formulas -/

/-- The conjunction of a list of formulas. -/
def conjList : List (L.Formula α) → L.Formula α
  | [] => ⊤
  | δ :: l => δ ⊓ conjList l

theorem isQF_conjList : ∀ l : List (L.Formula α), (∀ δ ∈ l, δ.IsQF) → (conjList l).IsQF
  | [], _ => IsQF.top
  | δ :: l, h => ((h δ (by simp)).imp (isQF_conjList l fun δ' hδ' =>
      h δ' (by simp [hδ'])).not).not

theorem realize_conjList {M : Type*} [L.Structure M] {v : α → M} :
    ∀ l : List (L.Formula α), (conjList l).Realize v ↔ ∀ δ ∈ l, δ.Realize v
  | [] => by simp [conjList, Formula.Realize]
  | δ :: l => by
    have ih := realize_conjList (M := M) (v := v) l
    simp only [conjList, List.mem_cons]
    constructor
    · intro h δ' hδ'
      have h' := BoundedFormula.realize_inf.mp h
      rcases hδ' with rfl | hδ'
      · exact h'.1
      · exact ih.mp h'.2 δ' hδ'
    · intro h
      exact BoundedFormula.realize_inf.mpr ⟨h δ (Or.inl rfl), ih.mpr fun δ' hδ' => h δ' (.inr hδ')⟩

/-! ### The satisfiability bridge -/

/-- **The satisfiability bridge**: the theory `T`, a set `S` of formulas, and one more formula
`χ`, all with free variables `α` read as fresh constants, are jointly satisfiable if and only if
some model of `T` realizes all of `S ∪ {χ}` at some assignment. -/
theorem satisfiable_union_iff {S : Set (L.Formula α)} {χ : L.Formula α} :
    ((L.lhomWithConstants α).onTheory T
        ∪ Formula.equivSentence '' (S ∪ {χ})).IsSatisfiable ↔
      ∃ (M : Theory.ModelType.{0, 0, 0} T) (v : α → M), (∀ δ ∈ S, δ.Realize v) ∧ χ.Realize v := by
  constructor
  · rintro ⟨M'⟩
    letI := (L.lhomWithConstants α).reduct M'
    have hT : M' ⊨ T := (LHom.onTheory_model _ _).1
      (M'.is_model.mono Set.subset_union_left)
    haveI : Nonempty M' := M'.nonempty'
    have hreal : ∀ ρ ∈ S ∪ {χ}, Formula.Realize (M := ↥M') ρ (fun a => (L.con a : M')) := by
      intro ρ hρ
      have := Theory.realize_sentence_of_mem
        ((L.lhomWithConstants α).onTheory T ∪ Formula.equivSentence '' (S ∪ {χ}))
        (Set.mem_union_right _ ⟨ρ, hρ, rfl⟩) (M := M')
      exact (Formula.realize_equivSentence _ _).1 this
    exact ⟨Theory.ModelType.of T (↥M'), fun a => (L.con a : M'),
      fun δ hδ => hreal δ (Set.mem_union_left _ hδ), hreal χ (Set.mem_union_right _ rfl)⟩
  · rintro ⟨M, v, hS, hχ⟩
    letI : (constantsOn α).Structure M := constantsOn.structure v
    haveI : ↥M ⊨ (L.lhomWithConstants α).onTheory T := (LHom.onTheory_model _ _).2 inferInstance
    refine ⟨{ Carrier := ↥M
              is_model := ⟨fun ψ hψ => ?_⟩ }⟩
    rcases hψ with hψ | ⟨δ, hδ, rfl⟩
    · exact Theory.realize_sentence_of_mem _ hψ
    · rw [Formula.realize_equivSentence]
      rcases hδ with hδ | rfl
      · exact hS δ hδ
      · exact hχ

/-- Negated form of the bridge: joint unsatisfiability says exactly that in every model of `T`,
any assignment realizing all of `S` refutes `χ`. -/
theorem not_satisfiable_union_iff {S : Set (L.Formula α)} {χ : L.Formula α} :
    ¬((L.lhomWithConstants α).onTheory T
        ∪ Formula.equivSentence '' (S ∪ {χ})).IsSatisfiable ↔
      ∀ (M : Theory.ModelType.{0, 0, 0} T) (v : α → M), (∀ δ ∈ S, δ.Realize v) → ¬χ.Realize v := by
  rw [satisfiable_union_iff]
  push Not
  exact Iff.rfl

/-- From joint unsatisfiability, compactness extracts a *finite* subset of `S` that already
suffices for the refutation. -/
theorem exists_finset_of_not_satisfiable {S : Set (L.Formula α)} {χ : L.Formula α}
    (h : ¬((L.lhomWithConstants α).onTheory T
        ∪ Formula.equivSentence '' (S ∪ {χ})).IsSatisfiable) :
    ∃ S₀ : Finset (L.Formula α), ↑S₀ ⊆ S ∧
      ∀ (M : Theory.ModelType.{0, 0, 0} T) (v : α → M), (∀ δ ∈ S₀, δ.Realize v) → ¬χ.Realize v := by
  classical
  rw [Theory.isSatisfiable_iff_isFinitelySatisfiable] at h
  simp only [Theory.IsFinitelySatisfiable, not_forall] at h
  obtain ⟨T0, hT0sub, hT0⟩ := h
  set S₀ : Finset (L.Formula α) := (T0.image Formula.equivSentence.symm).filter (· ∈ S) with hS₀
  have hns : ¬((L.lhomWithConstants α).onTheory T
      ∪ Formula.equivSentence '' ((S₀ : Set (L.Formula α)) ∪ {χ})).IsSatisfiable := by
    intro hsat
    refine hT0 (hsat.mono fun s hs => ?_)
    rcases hT0sub hs with hs' | ⟨δ, hδ, rfl⟩
    · exact Set.mem_union_left _ hs'
    · refine Set.mem_union_right _ ⟨δ, ?_, rfl⟩
      rcases hδ with hδ | rfl
      · refine Set.mem_union_left _ (Finset.mem_coe.mpr ?_)
        rw [hS₀, Finset.mem_filter]
        exact ⟨Finset.mem_image.mpr ⟨Formula.equivSentence δ, hs, by simp⟩, hδ⟩
      · exact Set.mem_union_right _ rfl
  exact ⟨S₀, fun δ hδ => (Finset.mem_filter.mp hδ).2, fun M v hv =>
    not_satisfiable_union_iff.mp hns M v fun δ hδ => hv δ (Finset.mem_coe.mp hδ)⟩

/-! ### The criterion -/

/-- **The semantic criterion for quantifier-free equivalence** (Marker, Thm. 3.1.4, in
quantifier-free-type form): if the truth of `φ` transfers between models of `T` at parameter
assignments realizing the same quantifier-free formulas, then `φ` is `T`-equivalent to a
quantifier-free formula. -/
theorem isQFEquivalent_of_qf_transfer (φ : L.Formula α)
    (htrans : ∀ (M N : Theory.ModelType.{0, 0, 0} T) (va : α → M) (vb : α → N),
      (∀ δ : L.Formula α, δ.IsQF → (δ.Realize va ↔ δ.Realize vb)) →
      (φ.Realize va ↔ φ.Realize vb)) :
    T.IsQFEquivalent φ := by
  classical
  -- `Γ`: the quantifier-free consequences of `φ` over `T`
  set Γ : Set (L.Formula α) :=
    {δ | δ.IsQF ∧ ∀ (M : Theory.ModelType.{0, 0, 0} T) (v : α → M), φ.Realize v → δ.Realize v} with hΓdef
  -- STEP 1: `T ∪ Γ ⊨ φ`
  have step1 : ∀ (M : Theory.ModelType.{0, 0, 0} T) (v : α → M), (∀ δ ∈ Γ, δ.Realize v) → φ.Realize v := by
    intro M v hΓv
    by_contra hnφ
    -- the quantifier-free type of `v`
    set Δ : Set (L.Formula α) := {δ | δ.IsQF ∧ δ.Realize v} with hΔdef
    by_cases hsat : ((L.lhomWithConstants α).onTheory T
        ∪ Formula.equivSentence '' (Δ ∪ {φ})).IsSatisfiable
    · -- a model of `T ∪ qftp(v) ∪ {φ}` transfers `φ` back to `(M, v)`
      obtain ⟨N, w, hΔw, hφw⟩ := satisfiable_union_iff.mp hsat
      refine hnφ ((htrans M N v w fun δ hδ => ⟨fun h => hΔw δ ⟨hδ, h⟩, fun h => ?_⟩).mpr hφw)
      by_contra hnot
      have hmem : δ.not ∈ Δ := ⟨hδ.not, by rwa [Formula.realize_not]⟩
      have := hΔw δ.not hmem
      rw [Formula.realize_not] at this
      exact this h
    · -- unsatisfiable: compactness yields a finite piece of the type refuting `φ`,
      -- whose negated conjunction is then a quantifier-free consequence realized by `v`
      obtain ⟨Δ₀, hΔ₀sub, hΔ₀⟩ := exists_finset_of_not_satisfiable hsat
      have hδstar : (conjList Δ₀.toList).not ∈ Γ := by
        refine ⟨(isQF_conjList _ fun δ hδ => (hΔ₀sub (by simpa using hδ)).1).not, ?_⟩
        intro N w hφw
        rw [Formula.realize_not]
        intro hconj
        exact hΔ₀ N w (fun δ hδ => (realize_conjList _).mp hconj δ (by simpa using hδ)) hφw
      have hstar := hΓv _ hδstar
      rw [Formula.realize_not] at hstar
      exact hstar ((realize_conjList _).mpr fun δ hδ =>
        (hΔ₀sub (by simpa using hδ)).2)
  -- STEP 2: compactness extracts a finite `Γ₀ ⊆ Γ` with `T ∪ Γ₀ ⊨ φ`
  have hnotsat : ¬((L.lhomWithConstants α).onTheory T
      ∪ Formula.equivSentence '' (Γ ∪ {φ.not})).IsSatisfiable := by
    rw [not_satisfiable_union_iff]
    intro M v hΓv
    rw [Formula.realize_not, not_not]
    exact step1 M v hΓv
  obtain ⟨Γ₀, hΓ₀sub, hΓ₀⟩ := exists_finset_of_not_satisfiable hnotsat
  -- the quantifier-free equivalent is the conjunction of `Γ₀`
  refine ⟨conjList Γ₀.toList, isQF_conjList _ fun δ hδ =>
    (hΓ₀sub (by simpa using hδ)).1, Theory.iff_iff_imp_and_imp.mpr ⟨?_, ?_⟩⟩
  · -- `φ ⟹ ⋀Γ₀`: each element of `Γ₀` is a consequence of `φ`
    apply Theory.models_formula_iff.mpr
    intro M v
    rw [Formula.realize_imp]
    intro hφv
    exact (realize_conjList _).mpr fun δ hδ => (hΓ₀sub (by simpa using hδ)).2 M v hφv
  · -- `⋀Γ₀ ⟹ φ`: this is `T ∪ Γ₀ ⊨ φ`
    apply Theory.models_formula_iff.mpr
    intro M v
    rw [Formula.realize_imp]
    intro hconj
    have := hΓ₀ M v fun δ hδ => (realize_conjList _).mp hconj δ (by simpa using hδ)
    rw [Formula.realize_not, not_not] at this
    exact this

end Artin.ModelTheory
