/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.ArtinRCF

/-!
# Models of `Theory.RCF` are real closed ordered fields

The reverse dictionary to `modelRCF`: an abstract `orderedRing.Structure` modelling `Theory.RCF`
carries a field structure (`fieldOfModelField`, from the field axioms) and a linear order
(`linearOrderOfModels`, from the linear-order axioms), which together satisfy
`IsStrictOrderedRing` (from the two order-compatibility axioms) and `IsRealClosed` (from the
square/odd-root axioms and semireality of ordered fields).

The main entry point is `rcfModelData M : RCFModelData M`, packaging the instances as data to be
introduced with `letI`/`haveI` at use sites. This is one half of the glue between the semantic
quantifier-elimination criterion (`isQFEquivalent_of_qf_transfer`) and the field-theoretic
transfer machinery (`realize_ex_map_iff`, `realClosureAlgEquiv`).
-/

open FirstOrder Language

namespace Artin.ModelTheory

/-- The canonical `orderedRing`-structure on an ordered field (the global instance path through
`compatibleRingOfOrderedField` and `orderStructureOfOrderedField`), named so that realization
with respect to it can be written explicitly alongside an abstract structure. -/
noncomputable abbrev canonicalOrderedRingStructure (M : Type*) [Field M] [LinearOrder M]
    [IsStrictOrderedRing M] : orderedRing.Structure M := inferInstance

variable (M : Type*) [S : orderedRing.Structure M] [hM : Theory.RCF.Model M]

/-- The ring-reduct of an `orderedRing`-structure. -/
@[reducible] noncomputable def ringReduct : Language.ring.Structure M :=
  (LHom.sumInl : Language.ring →ᴸ orderedRing).reduct M

theorem RCF_model_field :
    letI := ringReduct M
    Theory.field.Model M := by
  letI := ringReduct M
  haveI : (LHom.sumInl : Language.ring →ᴸ orderedRing).IsExpansionOn M :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  refine (LHom.onTheory_model (LHom.sumInl : Language.ring →ᴸ orderedRing)
    Language.Theory.field).1 (hM.mono ?_)
  rw [Theory.RCF, Theory.orderedField]
  exact (Set.subset_union_left.trans Set.subset_union_left).trans Set.subset_union_left

theorem RCF_model_linearOrder : M ⊨ orderedRing.linearOrderTheory :=
  hM.mono (by
    rw [Theory.RCF, Theory.orderedField]
    exact (Set.subset_union_right.trans Set.subset_union_left).trans Set.subset_union_left)

/-- **Models of `Theory.RCF` are real closed ordered fields**: the packaged instance data.
Fields: a `Field`, a `LinearOrder`, `IsStrictOrderedRing` and `IsRealClosed` relative to them —
with operations and order induced by the first-order structure — together with the statement
that realization of formulas in the abstract structure agrees with realization in the canonical
structure of the resulting ordered field. -/
noncomputable def rcfModelData :
    Σ' (_ : Field M) (_ : LinearOrder M) (_ : IsStrictOrderedRing M),
      IsRealClosed M ∧
        ∀ {β : Type} (φ : orderedRing.Formula β) (v : β → M),
          @Formula.Realize orderedRing M S β φ v ↔
            @Formula.Realize orderedRing M (canonicalOrderedRingStructure M) β φ v := by
  classical
  letI ringS := ringReduct M
  haveI hexp : (LHom.sumInl : Language.ring →ᴸ orderedRing).IsExpansionOn M :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  haveI hfield : Theory.field.Model M := RCF_model_field M
  letI f : Field M := FirstOrder.Field.fieldOfModelField M
  letI cr : FirstOrder.Ring.CompatibleRing M := FirstOrder.Field.compatibleRingOfModelField M
  haveI hlin : M ⊨ orderedRing.linearOrderTheory := RCF_model_linearOrder M
  letI lo : LinearOrder M := orderedRing.linearOrderOfModels M
  haveI ost : orderedRing.OrderedStructure M := by
    constructor
    simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi]
    intros
    rfl
  -- the two order-compatibility axioms
  have hmulax : ∀ a b : M, 0 ≤ a → 0 ≤ b → 0 ≤ a * b := by
    have hmem : (∀' ∀' (rle 0 (&0) ⟹ rle 0 (&1) ⟹ rle 0 (&0 * &1)))
        ∈ Theory.RCF := by
      rw [Theory.RCF, Theory.orderedField]
      exact Set.mem_union_left _ (Set.mem_union_right _ (Set.mem_insert _ _))
    have := hM.realize_of_mem _ hmem
    simp only [Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
      BoundedFormula.realize_imp, rle, Term.realize_le, LHom.realize_onTerm,
      FirstOrder.Ring.realize_mul, FirstOrder.Ring.realize_zero] at this
    exact fun a b => this a b
  have haddax : ∀ a b c : M, a ≤ b → a + c ≤ b + c := by
    have hmem : (∀' ∀' ∀' (rle (&0) (&1) ⟹ rle (&0 + &2) (&1 + &2)))
        ∈ Theory.RCF := by
      rw [Theory.RCF, Theory.orderedField]
      exact Set.mem_union_left _ (Set.mem_union_right _ (Set.mem_insert_of_mem _ rfl))
    have := hM.realize_of_mem _ hmem
    simp only [Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
      BoundedFormula.realize_imp, rle, Term.realize_le, LHom.realize_onTerm,
      FirstOrder.Ring.realize_add] at this
    exact fun a b c => this a b c
  -- ordered ring structure
  haveI ham : IsOrderedAddMonoid M :=
    { add_le_add_left := fun a b h c => haddax a b c h }
  haveI hzlo : ZeroLEOneClass M := ⟨by
    rcases le_total (0 : M) 1 with h | h
    · exact h
    · have h1 : (0 : M) ≤ -1 := by simpa using haddax 1 0 (-1) h
      have := hmulax _ _ h1 h1
      simpa [neg_mul_neg] using this⟩
  haveI hor : IsOrderedRing M := IsOrderedRing.of_mul_nonneg hmulax
  haveI iso : IsStrictOrderedRing M := inferInstance
  -- semireality: sums of squares are nonnegative in the linear order
  haveI hsemi : IsSemireal M := ⟨fun {s} hs h0 => by
    have hs' := hs.nonneg
    have h1 : (0 : M) < 1 := zero_lt_one
    linarith⟩
  -- real closedness
  haveI irc : IsRealClosed M := by
    refine { isSquare_or_isSquare_neg := ?_, exists_isRoot_of_odd_natDegree := ?_ }
    · -- the squares axiom, realized
      have hmem : (∀' ∃' (req (&0) (&1 * &1) ⊔ req (-&0) (&1 * &1))) ∈ Theory.RCF := by
        rw [Theory.RCF, Theory.realClosedAxioms]
        exact Set.mem_union_right _ (Set.mem_union_left _ rfl)
      have hsq := Theory.realize_sentence_of_mem Theory.RCF hmem (M := M)
      simp only [Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
        BoundedFormula.realize_ex, BoundedFormula.realize_sup, req,
        BoundedFormula.realize_bdEqual, LHom.realize_onTerm, FirstOrder.Ring.realize_mul,
        FirstOrder.Ring.realize_neg] at hsq
      intro x
      rcases hsq x with ⟨y, hy | hy⟩
      · exact Or.inl ⟨y, hy⟩
      · exact Or.inr ⟨y, hy⟩
    · -- the odd-root axioms, realized
      intro g hg
      have hg0 : g ≠ 0 := fun h => by simp [h, Nat.odd_iff] at hg
      have hmem : (LHom.sumInl.onSentence
          (FirstOrder.Field.genericMonicPolyHasRoot g.natDegree)) ∈ Theory.RCF := by
        rw [Theory.RCF, Theory.realClosedAxioms]
        exact Set.mem_union_right _ (Set.mem_union_right _ ⟨_, ⟨g.natDegree, hg, rfl⟩, rfl⟩)
      have hgen := Theory.realize_sentence_of_mem Theory.RCF hmem (M := M)
      rw [LHom.realize_onSentence, FirstOrder.Field.realize_genericMonicPolyHasRoot] at hgen
      obtain ⟨x, hx⟩ := hgen ⟨g * Polynomial.C g.leadingCoeff⁻¹,
        Polynomial.monic_mul_leadingCoeff_inv hg0,
        Polynomial.natDegree_mul_C (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hg0))⟩
      refine ⟨x, ?_⟩
      have hx' : (g * Polynomial.C g.leadingCoeff⁻¹).IsRoot x := hx
      rw [Polynomial.IsRoot, Polynomial.eval_mul, Polynomial.eval_C, mul_eq_zero] at hx'
      rcases hx' with hx' | hx'
      · exact hx'
      · exact absurd hx' (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hg0))
  -- realization in the abstract structure agrees with the canonical structure:
  -- the identity map is an isomorphism of `orderedRing`-structures
  have hagree : ∀ {β : Type} (φ : orderedRing.Formula β) (v : β → M),
      @Formula.Realize orderedRing M S β φ v ↔
        @Formula.Realize orderedRing M (canonicalOrderedRingStructure M) β φ v := by
    letI Scan : orderedRing.Structure M := canonicalOrderedRingStructure M
    have hfun : ∀ {n} (fn : orderedRing.Functions n) (x : Fin n → M),
        @Structure.funMap orderedRing M S n fn x
          = @Structure.funMap orderedRing M Scan n fn x := by
      intro n fn x
      rcases fn with g | g
      · have hx : x = fun i => x i := rfl
        cases g with
        | add => show _ = x 0 + x 1; exact congrArg _ (funext fun i => by fin_cases i <;> rfl)
        | mul => show _ = x 0 * x 1; exact congrArg _ (funext fun i => by fin_cases i <;> rfl)
        | neg => show _ = -x 0; exact congrArg _ (funext fun i => by fin_cases i; rfl)
        | zero => show _ = (0 : M); exact congrArg _ (funext fun i => i.elim0)
        | one => show _ = (1 : M); exact congrArg _ (funext fun i => i.elim0)
      · exact g.elim
    have ostCan : @Language.OrderedStructure orderedRing M _ _ Scan :=
      orderedStructureOfOrderedField M
    have hrel : ∀ {n} (r : orderedRing.Relations n) (x : Fin n → M),
        (@Structure.RelMap orderedRing M S n r x
          ↔ @Structure.RelMap orderedRing M Scan n r x) := by
      intro n r
      rcases r with r | r
      · exact r.elim
      · cases r
        intro x
        exact (ost.relMap_leSymb x).trans (ostCan.relMap_leSymb x).symm
    intro β φ v
    have h1 := @FirstOrder.Language.ElementaryEmbedding.map_formula orderedRing M M S Scan
      (@FirstOrder.Language.Equiv.toElementaryEmbedding orderedRing M M S Scan
        (@FirstOrder.Language.Equiv.mk orderedRing M M S Scan (Equiv.refl M)
          (fun {n} fn x => hfun fn x) (fun {n} r x => (hrel r x).symm))) β φ v
    exact h1.symm
  exact ⟨f, lo, iso, irc, fun {β} φ v => hagree φ v⟩

end Artin.ModelTheory
