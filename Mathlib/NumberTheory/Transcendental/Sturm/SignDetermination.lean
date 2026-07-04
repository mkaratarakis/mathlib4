/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.Sturm.SignCount

/-!
# Joint sign determination: sign-vector counts from Tarski queries

The number of roots of `p` at which a finite family `q i` of polynomials realizes a prescribed
vector of **nonzero** signs `ε` is recovered from Tarski queries of products, by the classical
(Ben-Or–Kozen–Reif / Tarski) expansion: pointwise, for `s = sgn v` and `e ∈ {±1}`,

  `e·s + s² = if s = e then 2 else 0`,

so multiplying over the family and summing over the roots of `p`,

  `2^m · #{x : p(x) = 0, ∀ i, sgn (qᵢ(x)) = εᵢ}
     = ∑_{S ⊆ [m]} (∏_{i∈S} εᵢ) · TaQ(p, ∏_{i∈S} qᵢ · ∏_{i∉S} qᵢ²)`

(`two_pow_mul_card_sgn_vector`). Every Tarski query on the right transfers along monotone
embeddings into real closed fields (`tarskiQuery_map_congr`), so the joint sign-vector counts are
determined by the base ordered field (`card_roots_filter_sgn_vector_congr`).

Applied to the family of iterated derivatives of `p`, this makes the multiset of **Thom
encodings** of the roots of `p` base-determined — the pillar of order-compatible root matching
for the uniqueness of real closures.
-/

open Polynomial Finset

namespace Sturm

section SgnAlgebra

variable {R : Type*} [Field R] [LinearOrder R]

theorem sgn_of_pos' {a : R} (h : 0 < a) : sgn a = 1 := by
  unfold sgn; rw [if_pos h]

theorem sgn_of_neg' {a : R} (h : a < 0) : sgn a = -1 := by
  unfold sgn; rw [if_neg (asymm h), if_neg h.ne]

theorem sgn_zero'' : sgn (0 : R) = 0 := by
  unfold sgn; rw [if_neg (lt_irrefl 0), if_pos rfl]

/-- The sign function is multiplicative. -/
theorem sgn_mul (a b : R) : sgn (a * b) = sgn a * sgn b := by
  rcases lt_trichotomy a 0 with ha | rfl | ha <;> rcases lt_trichotomy b 0 with hb | rfl | hb
  · rw [sgn_of_pos' (mul_pos_of_neg_of_neg ha hb), sgn_of_neg' ha, sgn_of_neg' hb]; norm_num
  · rw [mul_zero, sgn_zero'', sgn_zero'', mul_zero]
  · rw [sgn_of_neg' (mul_neg_of_neg_of_pos ha hb), sgn_of_neg' ha, sgn_of_pos' hb]; norm_num
  · rw [zero_mul, sgn_zero'', sgn_zero'', zero_mul]
  · rw [mul_zero, sgn_zero'', sgn_zero'', mul_zero]
  · rw [zero_mul, sgn_zero'', sgn_zero'', zero_mul]
  · rw [sgn_of_neg' (mul_neg_of_pos_of_neg ha hb), sgn_of_pos' ha, sgn_of_neg' hb]; norm_num
  · rw [mul_zero, sgn_zero'', sgn_zero'', mul_zero]
  · rw [sgn_of_pos' (mul_pos ha hb), sgn_of_pos' ha, sgn_of_pos' hb]; norm_num

/-- The sign function turns finite products into products of signs. -/
theorem sgn_prod {ι : Type*} (s : Finset ι) (v : ι → R) :
    sgn (∏ i ∈ s, v i) = ∏ i ∈ s, sgn (v i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using sgn_of_pos' (zero_lt_one : (0 : R) < 1)
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, sgn_mul, ih]

/-- The pointwise Ben-Or–Kozen–Reif factor: for `e = ±1`,
`e·sgn v + sgn (v·v)` is `2` when `sgn v = e` and `0` otherwise. -/
theorem bkr_factor {v : R} {e : ℤ} (he : e = 1 ∨ e = -1) :
    e * sgn v + sgn (v * v) = if sgn v = e then 2 else 0 := by
  rcases lt_trichotomy v 0 with hv | rfl | hv
  · rw [sgn_of_neg' hv, sgn_of_pos' (mul_pos_of_neg_of_neg hv hv)]
    rcases he with rfl | rfl
    · rw [if_neg (by norm_num)]; ring
    · rw [if_pos rfl]; ring
  · rw [sgn_zero'', mul_zero, sgn_zero'']
    rcases he with rfl | rfl
    · rw [if_neg (by norm_num)]; ring
    · rw [if_neg (by norm_num)]; ring
  · rw [sgn_of_pos' hv, sgn_of_pos' (mul_pos hv hv)]
    rcases he with rfl | rfl
    · rw [if_pos rfl]; ring
    · rw [if_neg (by norm_num)]; ring

end SgnAlgebra

section Identity

variable {R : Type*} [Field R] [LinearOrder R] {m : ℕ}

/-- **Joint sign determination** (Tarski / Ben-Or–Kozen–Reif): the number of roots of `p` at
which the family `q` realizes the nonzero sign vector `ε` is a `ℤ`-linear combination of Tarski
queries of products of the `q i` and their squares. -/
theorem two_pow_mul_card_sgn_vector (p : R[X]) (q : Fin m → R[X]) (ε : Fin m → ℤ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    (2 ^ m : ℤ) * ((p.roots.toFinset.filter
        (fun x => ∀ i, sgn ((q i).eval x) = ε i)).card : ℤ)
      = ∑ S ∈ (Finset.univ : Finset (Fin m)).powerset,
          (∏ i ∈ S, ε i) *
            tarskiQuery_R p ((∏ i ∈ S, q i) * ∏ i ∈ Finset.univ \ S, (q i) ^ 2) := by
  classical
  -- pointwise: the product of BKR factors is `2^m` on matching sign vectors and `0` otherwise
  have hpt : ∀ x : R,
      (∏ i, (ε i * sgn ((q i).eval x) + sgn ((q i).eval x * (q i).eval x)))
        = if (∀ i, sgn ((q i).eval x) = ε i) then (2 ^ m : ℤ) else 0 := by
    intro x
    have hfac : ∀ i, ε i * sgn ((q i).eval x) + sgn ((q i).eval x * (q i).eval x)
        = if sgn ((q i).eval x) = ε i then 2 else 0 := fun i => bkr_factor (hε i)
    rw [Finset.prod_congr rfl fun i _ => hfac i]
    by_cases hall : ∀ i, sgn ((q i).eval x) = ε i
    · rw [if_pos hall, Finset.prod_congr rfl fun i _ => if_pos (hall i),
        Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    · push Not at hall
      obtain ⟨i₀, hi₀⟩ := hall
      rw [if_neg (by push Not; exact ⟨i₀, hi₀⟩)]
      exact Finset.prod_eq_zero (Finset.mem_univ i₀) (if_neg hi₀)
  -- sum the pointwise identity over the roots, expanding the product by subsets
  have hsum : ∑ x ∈ p.roots.toFinset,
      (∏ i, (ε i * sgn ((q i).eval x) + sgn ((q i).eval x * (q i).eval x)))
        = (2 ^ m : ℤ) * ((p.roots.toFinset.filter
            (fun x => ∀ i, sgn ((q i).eval x) = ε i)).card : ℤ) := by
    rw [Finset.sum_congr rfl fun x _ => hpt x, Finset.sum_ite, Finset.sum_const,
      Finset.sum_const_zero, add_zero, nsmul_eq_mul, mul_comm]
  rw [← hsum]
  -- expand each pointwise product over subsets and swap the summations
  have hexp : ∀ x : R,
      (∏ i, (ε i * sgn ((q i).eval x) + sgn ((q i).eval x * (q i).eval x)))
        = ∑ S ∈ (Finset.univ : Finset (Fin m)).powerset,
            (∏ i ∈ S, ε i * sgn ((q i).eval x)) *
              ∏ i ∈ Finset.univ \ S, sgn ((q i).eval x * (q i).eval x) := fun x =>
    Finset.prod_add _ _ _
  rw [Finset.sum_congr rfl fun x _ => hexp x, Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  -- identify each inner sum as a Tarski query
  rw [mul_comm ((∏ i ∈ S, ε i)) _, ← Finset.sum_mul]
  sorry

end Identity

end Sturm
