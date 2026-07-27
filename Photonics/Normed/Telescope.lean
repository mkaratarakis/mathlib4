/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Telescoping bounds for products of contractions in a normed ring

If `a₁, …, aₙ` and `b₁, …, bₙ` all have norm at most `1`, then the products `a₁ ⋯ aₙ` and
`b₁ ⋯ bₙ` differ by at most `∑ i, ‖aᵢ - bᵢ‖`.  This is the standard telescoping estimate
`∏ aᵢ - ∏ bᵢ = ∑ i, a₁ ⋯ aᵢ₋₁ (aᵢ - bᵢ) bᵢ₊₁ ⋯ bₙ`, and it says that a long product of
contractions is `1`-Lipschitz in each factor.

Unlike `dist_prod_prod_le`, which lives in a `SeminormedCommGroup` and therefore does not apply
to matrices, this estimate is available in any (noncommutative) seminormed ring and does not
require the factors to be invertible.  It is the tool of choice for error propagation through a
cascade of lossy linear stages.

## Main statements

* `List.norm_prod_le_one`: a product of factors of norm at most `1` has norm at most `1`.
* `List.norm_prod_sub_prod_le`: the telescoping estimate, for a list of pairs.
* `norm_prod_ofFn_sub_prod_ofFn_le`: the same estimate for two families indexed by `Fin n`.

## Tags

telescoping, contraction, product, normed ring
-/

@[expose] public section

variable {α : Type*} [SeminormedRing α] [NormOneClass α]

namespace List

/-- A product of ring elements of norm at most `1` has norm at most `1`. -/
theorem norm_prod_le_one : ∀ {l : List α}, (∀ a ∈ l, ‖a‖ ≤ 1) → ‖l.prod‖ ≤ 1
  | [], _ => by simp
  | a :: t, h => by
    rw [prod_cons]
    refine (norm_mul_le _ _).trans ?_
    exact mul_le_one₀ (h a mem_cons_self) (norm_nonneg _)
      (norm_prod_le_one fun b hb => h b (mem_cons_of_mem _ hb))

/-- **Telescoping estimate**: two products of contractions differ by at most the sum of the
differences of their factors.  No invertibility is required. -/
theorem norm_prod_sub_prod_le : ∀ {l : List (α × α)},
    (∀ p ∈ l, ‖p.1‖ ≤ 1) → (∀ p ∈ l, ‖p.2‖ ≤ 1) →
      ‖(l.map Prod.fst).prod - (l.map Prod.snd).prod‖ ≤ (l.map fun p => ‖p.1 - p.2‖).sum
  | [], _, _ => by simp
  | p :: t, h₁, h₂ => by
    have hP : ‖(t.map Prod.fst).prod‖ ≤ 1 := by
      refine norm_prod_le_one fun a ha => ?_
      obtain ⟨q, hq, rfl⟩ := mem_map.1 ha
      exact h₁ q (mem_cons_of_mem _ hq)
    have ih := norm_prod_sub_prod_le (l := t) (fun q hq => h₁ q (mem_cons_of_mem _ hq))
      (fun q hq => h₂ q (mem_cons_of_mem _ hq))
    simp only [map_cons, prod_cons, sum_cons]
    have key : p.1 * (t.map Prod.fst).prod - p.2 * (t.map Prod.snd).prod
        = (p.1 - p.2) * (t.map Prod.fst).prod
          + p.2 * ((t.map Prod.fst).prod - (t.map Prod.snd).prod) := by
      rw [sub_mul, mul_sub]; abel
    rw [key]
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_mul_le _ _).trans ?_) ((norm_mul_le _ _).trans ?_)
    · simpa using mul_le_mul_of_nonneg_left hP (norm_nonneg (p.1 - p.2))
    · exact (mul_le_mul (h₂ p mem_cons_self) ih (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

end List

/-- **Telescoping estimate** for two families of contractions indexed by `Fin n`, with the
products taken in the order `f 0 * f 1 * ⋯ * f (n - 1)`. -/
theorem norm_prod_ofFn_sub_prod_ofFn_le {n : ℕ} (f g : Fin n → α)
    (hf : ∀ i, ‖f i‖ ≤ 1) (hg : ∀ i, ‖g i‖ ≤ 1) :
    ‖(List.ofFn f).prod - (List.ofFn g).prod‖ ≤ ∑ i, ‖f i - g i‖ := by
  have h := List.norm_prod_sub_prod_le (l := List.ofFn fun i => (f i, g i))
    (by simp [hf]) (by simp [hg])
  simpa [List.map_ofFn, Function.comp_def, List.sum_ofFn] using h
