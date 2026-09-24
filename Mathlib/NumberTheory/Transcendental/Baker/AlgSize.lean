/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.Transcendental.Baker.Liouville

/-!
# Size of an algebraic number

`AlgSize δ α a H` records that `δ ^ a * α` is an algebraic integer of house at most `H`.  The
predicate is stable under sums, products and powers with explicit rules, so that the size of
a polynomial expression in finitely many algebraic numbers can be computed step by step; and
Liouville's inequality turns a size into a lower bound for `|α|` at every embedding.
-/

@[expose] public section

open Module

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- `δ ^ a * α` is an algebraic integer whose house is at most `H`. -/
def AlgSize (δ : ℕ) (α : K) (a : ℕ) (H : ℝ) : Prop :=
  IsIntegral ℤ ((δ : K) ^ a * α) ∧ house ((δ : K) ^ a * α) ≤ H

namespace AlgSize

variable {δ : ℕ} {α β : K} {a b : ℕ} {H H' : ℝ}

lemma nonneg (h : AlgSize δ α a H) : 0 ≤ H := (house_nonneg _).trans h.2

lemma mono (h : AlgSize δ α a H) (hH : H ≤ H') : AlgSize δ α a H' := ⟨h.1, h.2.trans hH⟩

lemma congr_exp (h : AlgSize δ α a H) (hab : a = b) : AlgSize δ α b H := hab ▸ h

lemma intCast (x : ℤ) : AlgSize δ (x : K) 0 |x| := by
  refine ⟨?_, by simp⟩
  have := isIntegral_algebraMap (R := ℤ) (A := K) (x := x)
  rw [eq_intCast] at this
  simpa using this

lemma natCast (x : ℕ) : AlgSize δ (x : K) 0 x := by
  simpa using intCast (δ := δ) (K := K) (x : ℤ)

lemma zero : AlgSize δ (0 : K) a 0 := ⟨by simpa using isIntegral_zero, by simp [house]⟩

/-- Raising the exponent of the denominator. -/
lemma raise (h : AlgSize δ α a H) (hab : a ≤ b) : AlgSize δ α b ((δ : ℝ) ^ (b - a) * H) := by
  have hsplit : (δ : K) ^ b * α = ((δ ^ (b - a) : ℕ) : K) * ((δ : K) ^ a * α) := by
    rw [← mul_assoc, Nat.cast_pow, ← pow_add, Nat.sub_add_cancel hab]
  refine ⟨?_, ?_⟩
  · have hn : IsIntegral ℤ (((δ ^ (b - a) : ℕ) : K)) := by
      have := isIntegral_algebraMap (R := ℤ) (A := K) (x := ((δ ^ (b - a) : ℕ) : ℤ))
      simpa using this
    rw [hsplit]
    exact hn.mul h.1
  · rw [hsplit, house_nat_mul]
    push_cast
    exact mul_le_mul_of_nonneg_left h.2 (by positivity)

lemma add (h : AlgSize δ α a H) (h' : AlgSize δ β a H') : AlgSize δ (α + β) a (H + H') := by
  refine ⟨by rw [mul_add]; exact h.1.add h'.1, ?_⟩
  rw [mul_add]
  exact (house_add_le _ _).trans (add_le_add h.2 h'.2)

lemma mul (h : AlgSize δ α a H) (h' : AlgSize δ β b H') : AlgSize δ (α * β) (a + b) (H * H') := by
  have hsplit : (δ : K) ^ (a + b) * (α * β) = ((δ : K) ^ a * α) * ((δ : K) ^ b * β) := by
    rw [pow_add]; ring
  refine ⟨by rw [hsplit]; exact h.1.mul h'.1, ?_⟩
  rw [hsplit]
  exact (house_mul_le _ _).trans (mul_le_mul h.2 h'.2 (house_nonneg _) h.nonneg)

lemma pow (h : AlgSize δ α a H) (k : ℕ) : AlgSize δ (α ^ k) (a * k) (H ^ k) := by
  have hsplit : (δ : K) ^ (a * k) * α ^ k = ((δ : K) ^ a * α) ^ k := by
    rw [mul_pow, pow_mul]
  refine ⟨by rw [hsplit]; exact h.1.pow k, ?_⟩
  rw [hsplit, house_pow]
  exact pow_le_pow_left₀ (house_nonneg _) h.2 k

lemma sum {ι : Type*} (s : Finset ι) {f : ι → K} {F : ι → ℝ}
    (h : ∀ i ∈ s, AlgSize δ (f i) a (F i)) : AlgSize δ (∑ i ∈ s, f i) a (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : AlgSize δ (0 : K) a 0)
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (h j (Finset.mem_insert_self j s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma prod {ι : Type*} (s : Finset ι) {f : ι → K} {e : ι → ℕ} {F : ι → ℝ}
    (h : ∀ i ∈ s, AlgSize δ (f i) (e i) (F i)) :
    AlgSize δ (∏ i ∈ s, f i) (∑ i ∈ s, e i) (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using (natCast (δ := δ) (K := K) 1)
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, Finset.prod_insert hj]
    exact (h j (Finset.mem_insert_self j s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **Liouville's inequality for a number of known size.**  If `δ ^ a * α` is a nonzero algebraic
integer of house at most `H`, then at every embedding `1 ≤ δ ^ a ‖φ α‖ H ^ (d - 1)`, where
`d = [K : ℚ]`. -/
theorem one_le (h : AlgSize δ α a H) (hα : α ≠ 0) (hδ : δ ≠ 0) (φ : K →+* ℂ) :
    1 ≤ (δ : ℝ) ^ a * ‖φ α‖ * H ^ (finrank ℚ K - 1) := by
  set β : 𝓞 K := ⟨(δ : K) ^ a * α, h.1⟩ with hβ
  have hβ0 : β ≠ 0 := by
    intro h0
    have : (δ : K) ^ a * α = 0 := congrArg Subtype.val h0
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hδ)) hα this
  have key := one_le_norm_embedding_mul_house_pow hβ0 φ
  have hφ : ‖φ (β : K)‖ = (δ : ℝ) ^ a * ‖φ α‖ := by
    rw [hβ]
    change ‖φ ((δ : K) ^ a * α)‖ = _
    rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow, Complex.norm_natCast]
  rw [hφ] at key
  exact key.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (house_nonneg _) h.2 _)
    (by positivity))

end AlgSize

end NumberField
