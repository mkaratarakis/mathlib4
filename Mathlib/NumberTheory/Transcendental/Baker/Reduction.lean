/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.NumberTheory.Transcendental.Baker.SchneiderLang
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Trace.Basic

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
  classical
  have hd0 : 0 < d := hd ▸ Module.finrank_pos
  have hcard : Fintype.card (Fin d) = Module.finrank ℚ K := by simp [hd]
  -- `β` is a `ℚ`-basis of `K`, so its embeddings matrix `M` is regular (Lemma 4.6).
  set Bas : Module.Basis (Fin d) ℚ K := basisOfLinearIndependentOfCardEqFinrank' β hβ hcard
    with hBas
  have hBasβ : ⇑Bas = β := coe_basisOfLinearIndependentOfCardEqFinrank' β hβ hcard
  have hcardAlg : Fintype.card (K →ₐ[ℚ] ℂ) = d := by rw [AlgHom.card, hd]
  -- Index the embeddings so that index `0` is the natural inclusion `K ⊆ ℂ`.
  set e : Fin d ≃ (K →ₐ[ℚ] ℂ) :=
    (Fintype.equivFinOfCardEq hcardAlg).symm.trans
      (Equiv.swap ((Fintype.equivFinOfCardEq hcardAlg).symm ⟨0, hd0⟩) K.val) with he
  have he0 : e ⟨0, hd0⟩ = K.val := by simp [he]
  set M : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun i v => (e v) (β i) with hM
  have hMdet : M.det ≠ 0 := by
    have h2 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ β e
    have h1 : Algebra.discr ℚ β ≠ 0 := by
      simpa [hBasβ] using Algebra.discr_not_zero_of_basis (K := ℚ) Bas
    intro hdet
    rw [show Algebra.embeddingsMatrixReindex ℚ ℂ β e = M from rfl, hdet] at h2
    simp only [ne_eq, zero_pow, OfNat.ofNat_ne_zero, not_false_eq_true] at h2
    exact h1 (by simpa using h2)
  -- The numbers `λ v = ∑ₖ σ_v(βₖ) ℓₖ` of the book.
  set A : Fin d → ℂ := fun v => ∑ k, (e v) (β k) * l k with hA
  have hA0 : A ⟨0, hd0⟩ = ∑ i, (β i : ℂ) * l i := by
    simp [hA, he0, IntermediateField.coe_val]
  -- Each `xᵢ · y_j` is the trace combination `∑ₘ Tr(βᵢβⱼβₘ) ℓₘ`, hence lies in `L`.
  have hdot : ∀ i j : Fin d, ∑ v, (e v) (β i) * ((e v) (β j) * A v) =
      ∑ m, ((Algebra.trace ℚ K (β i * β j * β m) : ℚ) : ℂ) * l m := by
    intro i j
    have : ∀ m : Fin d, ((Algebra.trace ℚ K (β i * β j * β m) : ℚ) : ℂ)
        = ∑ v, (e v) (β i * β j * β m) := by
      intro m
      have h := trace_eq_sum_embeddings (K := ℚ) (L := K) (E := ℂ)
        (x := β i * β j * β m)
      rw [← Equiv.sum_comp e fun σ : K →ₐ[ℚ] ℂ => σ (β i * β j * β m)] at h
      rw [← h, eq_ratCast]
    simp only [this, hA, Finset.mul_sum, Finset.sum_mul, map_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun m _ => by ring
  have hdotL : ∀ i j : Fin d, IsAlgebraic ℚ (exp (∑ v, (e v) (β i) * ((e v) (β j) * A v))) := by
    intro i j
    rw [hdot i j]
    exact isAlgebraic_exp_ratCast_combo _ l hl
  -- Coordinates of the `xᵢ` are algebraic, being conjugates of algebraic numbers.
  have hxalg : ∀ i v : Fin d, IsAlgebraic ℚ ((e v) (β i)) :=
    fun i v => (IsAlgebraic.of_finite ℚ (β i)).algHom (e v)
  -- Whatever embeddings are selected, the rows of `M` stay `ℚ`-linearly independent:
  -- a rational relation between them is pushed back through any single embedding.
  have hxli : ∀ {p : ℕ} (g : Fin p → Fin d), 0 < p →
      LinearIndependent ℚ (fun (i : Fin d) (v : Fin p) => (e (g v)) (β i)) := by
    intro p g hp
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    have hev : ∑ k, a k • (e (g ⟨0, hp⟩)) (β k) = 0 := by
      have h := congrFun ha ⟨0, hp⟩
      simpa using h
    have hker : (e (g ⟨0, hp⟩)) (∑ k, a k • β k) = 0 := by
      rw [map_sum]
      simpa [Algebra.smul_def] using hev
    have : ∑ k, a k • β k = 0 :=
      (map_eq_zero_iff _ (e (g ⟨0, hp⟩)).toRingHom.injective).mp hker
    exact Fintype.linearIndependent_iff.mp hβ a this i
  -- The three cases of §4.2.4, according to how many of the `A v` vanish.
  by_cases hall : ∀ v, A v = 0
  · -- Third case: all `A v` vanish.  The book stops here; the conclusion needs one more
    -- step, namely that `M` is regular, which is exactly Lemma 4.6.
    have hvec : Matrix.vecMul l M = 0 := by
      funext v
      have h := hall v
      simp only [hA] at h
      simpa [Matrix.vecMul, dotProduct, hM, mul_comm] using h
    exact fun i => congrFun (Matrix.eq_zero_of_vecMul_eq_zero hMdet hvec) i
  · push Not at hall
    by_cases hnone : ∀ v, A v ≠ 0
    · -- Second case: no `A v` vanishes; Corollary 4.4 applies and gives a contradiction.
      exfalso
      have : NeZero d := ⟨hd0.ne'⟩
      have hzero : (0 : Fin d) = ⟨0, hd0⟩ := Fin.ext (by simp)
      have hYdet : (M * Matrix.diagonal A).det ≠ 0 := by
        rw [Matrix.det_mul, Matrix.det_diagonal]
        exact mul_ne_zero hMdet (Finset.prod_ne_zero_iff.2 fun v _ => hnone v)
      have hYentry : ∀ j v, (M * Matrix.diagonal A) j v = (e v) (β j) * A v := by
        intro j v; simp [Matrix.mul_diagonal, hM]
      have hy1 : ∀ j, IsAlgebraic ℚ ((M * Matrix.diagonal A) j 0) := by
        intro j
        rw [hYentry, hzero, hA0]
        exact (hxalg j ⟨0, hd0⟩).mul hsum
      obtain ⟨i, j, hij⟩ := schneiderLang_one (d := d) (fun i v => (e v) (β i)) hxalg
        (hxli id hd0) (fun j => (M * Matrix.diagonal A) j)
        (Matrix.linearIndependent_rows_of_det_ne_zero hYdet) hy1
      exact hij (by simpa only [hYentry] using hdotL i j)
    · -- First case: some but not all `A v` vanish; Corollary 4.3 gives a contradiction.
      exfalso
      push Not at hnone
      set T : Finset (Fin d) := Finset.univ.filter (fun v => A v ≠ 0) with hTdef
      have hTmem : ∀ v, v ∈ T ↔ A v ≠ 0 := by simp [hTdef]
      set n : ℕ := T.card with hncard
      have hn0 : 0 < n := by
        obtain ⟨v, hv⟩ := hall
        exact Finset.card_pos.2 ⟨v, (hTmem v).2 hv⟩
      have hnd : n < d := by
        obtain ⟨u, hu⟩ := hnone
        have hsub : T ⊂ Finset.univ :=
          Finset.ssubset_univ_iff.2 fun h => ((hTmem u).1 (h ▸ Finset.mem_univ u)) hu
        simpa [hncard] using Finset.card_lt_card hsub
      -- Index the embeddings at which `A` does not vanish.
      set ef : Fin n ≃o T := T.orderIsoOfFin hncard.symm with hef
      set f : Fin n → Fin d := fun v => (ef v : Fin d) with hf
      have hfT : ∀ v, A (f v) ≠ 0 := fun v => (hTmem _).1 (ef v).2
      have hefsymm : ∀ v, ef.symm ⟨f v, (ef v).2⟩ = v := fun v => by
        simp [hf]
      -- Restricting the sum over all embeddings to `T` changes nothing, as `A` vanishes off `T`.
      have hrestrict : ∀ F : Fin d → ℂ, (∀ u, u ∉ T → F u = 0) →
          ∑ v : Fin n, F (f v) = ∑ u : Fin d, F u := by
        intro F hF
        rw [show ∑ v : Fin n, F (f v) = ∑ u ∈ T, F u from
          (Fintype.sum_equiv ef.toEquiv (fun v => F (f v)) (fun x : T => F x)
            fun v => rfl).trans (Finset.sum_coe_sort T F)]
        exact Finset.sum_subset T.subset_univ fun u _ hu => hF u hu
      -- The `d` vectors `y j` span `ℂⁿ`: solve `a ᵥ* M = c` and scale by the `A (f v)`.
      have hspan : Submodule.span ℂ
          (Set.range fun (j : Fin d) (v : Fin n) => (e (f v)) (β j) * A (f v)) = ⊤ := by
        rw [Submodule.eq_top_iff']
        intro w
        rw [Submodule.mem_span_range_iff_exists_fun]
        set c : Fin d → ℂ := fun u => if h : u ∈ T then w (ef.symm ⟨u, h⟩) / A u else 0 with hc
        refine ⟨Matrix.vecMul c M⁻¹, ?_⟩
        have hvm : Matrix.vecMul (Matrix.vecMul c M⁻¹) M = c := by
          rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul M (Ne.isUnit hMdet), Matrix.vecMul_one]
        funext v
        have hmem : f v ∈ T := (ef v).2
        have hcv : c (f v) = w v / A (f v) := by
          rw [hc]
          simp only
          rw [dite_eq_left hmem, hefsymm v]
        have hrow : ∑ x, Matrix.vecMul c M⁻¹ x * (e (f v)) (β x) = c (f v) := by
          simpa [Matrix.vecMul, dotProduct, hM] using congrFun hvm (f v)
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← mul_assoc]
        rw [← Finset.sum_mul, hrow, hcv, div_mul_cancel₀ _ (hfT v)]
      obtain ⟨i, j, hij⟩ := schneiderLang_zero (n := n) hnd
        (fun i v => (e (f v)) (β i)) (fun i v => hxalg i (f v)) (hxli f hn0) _ hspan
      refine hij ?_
      have hsum_eq : (∑ v : Fin n, (e (f v)) (β i) * ((e (f v)) (β j) * A (f v)))
          = ∑ v : Fin d, (e v) (β i) * ((e v) (β j) * A v) := by
        refine hrestrict (fun u => (e u) (β i) * ((e u) (β j) * A u)) fun u hu => ?_
        have hAu : A u = 0 := by by_contra h; exact hu ((hTmem u).2 h)
        rw [hAu]; ring
      rw [hsum_eq]
      exact hdotL i j


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
  have : FiniteDimensional ℚ K :=
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
