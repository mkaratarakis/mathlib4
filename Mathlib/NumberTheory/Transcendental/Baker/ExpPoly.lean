/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.NumberTheory.Transcendental.Baker.SchwarzProduct

/-!
# Exponential polynomials

The functions `z ↦ z ^ τ * exp (w · z)` on `ℂⁿ` from which the auxiliary function of the
Schneider–Lang criterion is built, and their Taylor coefficients at an arbitrary point.  This
is Lemma 4.9 of Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, in the
form of Taylor coefficients `D^σ φ (ξ) / σ!` rather than derivatives.

A function of the form `∏ᵢ gᵢ (zᵢ)` has as multi-index Taylor coefficients the products of
the one-variable ones (`hasSum_prod_pi`), and `(ξ + h) ^ τ e ^ {w h}` has the one-variable
coefficients `∑_{k ≤ σ} (τ choose k) ξ ^ (τ - k) w ^ (σ - k) / (σ - k)!`.

## Main statements

* `hasSum_prod_pi`: a finite product of absolutely convergent series is the sum, over
  multi-indices, of the products of their terms.
* `MultiIndex.taylorCoeff_expMonomial`: Lemma 4.9.
-/

@[expose] public section

open Finset

universe u

variable {R : Type*} [NormedCommRing R] [CompleteSpace R]

/-- The statement of `hasSum_prod_pi` for the index type `ι`. -/
def ProdPiStmt (R : Type*) [NormedCommRing R] (ι : Type u) [Fintype ι] : Prop :=
  ∀ f : ι → ℕ → R, (∀ i, Summable fun k => ‖f i k‖) →
    HasSum (fun σ : ι → ℕ => ∏ i, f i (σ i)) (∏ i, ∑' k, f i k) ∧
      Summable fun σ : ι → ℕ => ‖∏ i, f i (σ i)‖

omit [CompleteSpace R] in
lemma prodPiStmt_of_equiv {α β : Type u} [Fintype β] (e : α ≃ β)
    (ih : @ProdPiStmt R _ α (Fintype.ofEquiv β e.symm)) : ProdPiStmt R β := by
  intro f hf
  let _ : Fintype α := Fintype.ofEquiv β e.symm
  obtain ⟨h1, h2⟩ := ih (fun a => f (e a)) fun a => hf (e a)
  set E : (α → ℕ) ≃ (β → ℕ) := e.arrowCongr (Equiv.refl ℕ) with hE
  have hcomp : ∀ σ : α → ℕ, ∏ b, f b ((E σ) b) = ∏ a, f (e a) (σ a) := by
    intro σ
    rw [← e.prod_comp]
    simp [hE, Equiv.arrowCongr_apply]
  have hsum : ∏ b, ∑' k, f b k = ∏ a, ∑' k, f (e a) k := (e.prod_comp _).symm
  refine ⟨?_, ?_⟩
  · rw [← E.hasSum_iff, hsum]
    exact h1.congr_fun fun σ => hcomp σ
  · rw [← E.summable_iff]
    refine h2.congr fun σ => ?_
    simp only [Function.comp_apply, hcomp]

omit [CompleteSpace R] in
lemma prodPiStmt_empty : ProdPiStmt R PEmpty := by
  intro f _
  have hprod : ∀ σ : PEmpty → ℕ, ∏ i, f i (σ i) = 1 := fun σ => Finset.prod_of_isEmpty _
  have h1 : HasSum (fun σ : PEmpty → ℕ => ∏ i, f i (σ i)) 1 := by
    have := hasSum_single (f := fun σ : PEmpty → ℕ => ∏ i, f i (σ i)) default
      fun σ' hσ' => absurd (Subsingleton.elim σ' default) hσ'
    rwa [hprod] at this
  refine ⟨by rwa [Finset.prod_of_isEmpty], ?_⟩
  exact (hasSum_single (f := fun σ : PEmpty → ℕ => ‖∏ i, f i (σ i)‖) default
    fun σ' hσ' => absurd (Subsingleton.elim σ' default) hσ').summable

lemma prodPiStmt_option {α : Type u} [Fintype α] (ih : ProdPiStmt R α) :
    ProdPiStmt R (Option α) := by
  intro f hf
  obtain ⟨h1, h2⟩ := ih (fun a => f (some a)) fun a => hf (some a)
  have hs : Summable fun x : ℕ × (α → ℕ) => f none x.1 * ∏ i, f (some i) (x.2 i) :=
    summable_mul_of_summable_norm (f := f none) (g := fun σ : α → ℕ => ∏ i, f (some i) (σ i))
      (hf none) h2
  have hmul := HasSum.mul (hf none).of_norm.hasSum h1 hs
  have hg : ∀ x : ℕ × (α → ℕ),
      ∏ i, f i ((Equiv.piOptionEquivProd.symm x : Option α → ℕ) i) =
        f none x.1 * ∏ i, f (some i) (x.2 i) := fun x => by
    rw [Fintype.prod_option]
    rfl
  refine ⟨(Equiv.piOptionEquivProd.symm.hasSum_iff).1 ?_,
    (Equiv.piOptionEquivProd.symm.summable_iff).1 ?_⟩
  · rw [Fintype.prod_option]
    exact hmul.congr_fun fun x => hg x
  · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => ?_)
      ((hf none).mul_norm h2)
    simp only [Function.comp_apply, hg]
    exact le_rfl

/-- **Products of absolutely convergent series.**  For finitely many absolutely convergent
series `∑ₖ f i k` in a complete normed commutative ring, the family
`σ ↦ ∏ i, f i (σ i)` over multi-indices `σ : ι → ℕ` is absolutely summable with sum
`∏ i, ∑' k, f i k`. -/
theorem hasSum_prod_pi {ι : Type u} [Fintype ι] (f : ι → ℕ → R)
    (hf : ∀ i, Summable fun k => ‖f i k‖) :
    HasSum (fun σ : ι → ℕ => ∏ i, f i (σ i)) (∏ i, ∑' k, f i k) ∧
      Summable fun σ : ι → ℕ => ‖∏ i, f i (σ i)‖ := by
  have key : ProdPiStmt R ι := Fintype.induction_empty_option (P := fun ι _ => ProdPiStmt R ι)
    (fun _ _ _ e ih => prodPiStmt_of_equiv e ih) prodPiStmt_empty
    (fun _ _ ih => prodPiStmt_option ih) ι
  exact key f hf
