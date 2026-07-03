/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.Sturm.Transfer

/-!
# Sign counts at the roots of a polynomial are determined by the base ordered field

For polynomials `p, q` over an ordered field `K` and a monotone embedding `φ` of `K` into a real
closed field `L`, the numbers

* `c₊` of roots `x` of `p.map φ` in `L` with `(q.map φ).eval x > 0`,
* `c₋` of roots with `(q.map φ).eval x < 0`,
* `c₀` of roots with `(q.map φ).eval x = 0`

are all determined inside `K`: they are recovered from the Tarski queries `TaQ(p, q)`,
`TaQ(p, q²)` and `TaQ(p, 1)`, each of which equals a Sturm sign-variation count of `K`-polynomial
data (`sturm_tarski_R` + `seqVarRSturm_map_of_strictMono`). Consequently all three counts agree
across *any* two real closed order-extensions of `K` (`card_roots_filter_pos_congr` and
friends).

This is the single-polynomial case of Tarski's sign-determination principle — the counting input
for order-compatible root matching in the uniqueness of real closures, and (iterated) for the
sign-sequence determination behind quantifier elimination.

## Identities

Writing `TaQ(p, q) = ∑_{p(x)=0} sgn q(x)` (`tarskiQuery_R`):

* `TaQ(p, q) = c₊ - c₋` (`tarskiQuery_R_eq_card_sub_card`);
* `TaQ(p, q²) = c₊ + c₋` (`tarskiQuery_R_sq_eq_card_add_card`);
* `TaQ(p, 1) = c₊ + c₋ + c₀` (all roots; `sturm_R`).
-/

open Polynomial

namespace Sturm

section Partition

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

omit [IsStrictOrderedRing R] in
private theorem sgn_of_pos {a : R} (h : 0 < a) : sgn a = 1 := by
  unfold sgn; rw [if_pos h]

omit [IsStrictOrderedRing R] in
private theorem sgn_of_neg {a : R} (h : a < 0) : sgn a = -1 := by
  unfold sgn; rw [if_neg (asymm h), if_neg h.ne]

omit [IsStrictOrderedRing R] in
private theorem sgn_of_eq {a : R} (h : a = 0) : sgn a = 0 := by
  unfold sgn; rw [if_neg (by rw [h]; exact lt_irrefl 0), if_pos h]

omit [IsStrictOrderedRing R] in
/-- **The Tarski query is the signed root count**: `TaQ(p, q) = c₊ - c₋`, where `c₊` (resp. `c₋`)
counts the roots of `p` where `q` is positive (resp. negative). -/
theorem tarskiQuery_R_eq_card_sub_card (p q : R[X]) :
    tarskiQuery_R p q
      = ((p.roots.toFinset.filter fun x => 0 < q.eval x).card : ℤ)
        - ((p.roots.toFinset.filter fun x => q.eval x < 0).card : ℤ) := by
  unfold tarskiQuery_R
  rw [← Finset.sum_filter_add_sum_filter_not p.roots.toFinset (fun x => 0 < q.eval x)]
  have h1 : ∑ x ∈ p.roots.toFinset.filter (fun x => 0 < q.eval x), sgn (q.eval x)
      = ((p.roots.toFinset.filter fun x => 0 < q.eval x).card : ℤ) := by
    rw [Finset.sum_congr rfl fun x hx => sgn_of_pos (Finset.mem_filter.mp hx).2]
    simp [mul_comm]
  have hsplit : p.roots.toFinset.filter (fun x => ¬ 0 < q.eval x)
      = p.roots.toFinset.filter (fun x => q.eval x < 0)
        ∪ p.roots.toFinset.filter (fun x => q.eval x = 0) := by
    rw [← Finset.filter_or]
    exact Finset.filter_congr fun x _ => by
      constructor
      · intro h
        rcases lt_trichotomy (q.eval x) 0 with h' | h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
        · exact absurd h' h
      · rintro (h | h)
        · exact asymm h
        · rw [h]; exact lt_irrefl 0
  have hdisj : Disjoint (p.roots.toFinset.filter fun x => q.eval x < 0)
      (p.roots.toFinset.filter fun x => q.eval x = 0) :=
    Finset.disjoint_left.mpr fun x hx hx' =>
      (Finset.mem_filter.mp hx).2.ne (Finset.mem_filter.mp hx').2
  have h2 : ∑ x ∈ p.roots.toFinset.filter (fun x => ¬ 0 < q.eval x), sgn (q.eval x)
      = -((p.roots.toFinset.filter fun x => q.eval x < 0).card : ℤ) := by
    rw [hsplit, Finset.sum_union hdisj,
      Finset.sum_congr rfl fun x hx => sgn_of_neg (Finset.mem_filter.mp hx).2,
      Finset.sum_congr rfl fun x hx => sgn_of_eq (Finset.mem_filter.mp hx).2]
    simp
  rw [h1, h2]
  ring

/-- **The Tarski query of the square is the unsigned root count**: `TaQ(p, q²) = c₊ + c₋`. -/
theorem tarskiQuery_R_sq_eq_card_add_card (p q : R[X]) :
    tarskiQuery_R p (q ^ 2)
      = ((p.roots.toFinset.filter fun x => 0 < q.eval x).card : ℤ)
        + ((p.roots.toFinset.filter fun x => q.eval x < 0).card : ℤ) := by
  unfold tarskiQuery_R
  have hsgn : ∀ x, sgn ((q ^ 2).eval x) = if q.eval x = 0 then 0 else 1 := fun x => by
    rw [eval_pow]
    by_cases h : q.eval x = 0
    · rw [if_pos h, h]
      exact sgn_of_eq (by ring)
    · rw [if_neg h]
      exact sgn_of_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h)))
  rw [Finset.sum_congr rfl fun x _ => hsgn x, Finset.sum_ite, Finset.sum_const,
    Finset.sum_const]
  have hcard : (p.roots.toFinset.filter fun x => ¬ q.eval x = 0).card
      = (p.roots.toFinset.filter fun x => 0 < q.eval x).card
        + (p.roots.toFinset.filter fun x => q.eval x < 0).card := by
    have hsplit : p.roots.toFinset.filter (fun x => ¬ q.eval x = 0)
        = p.roots.toFinset.filter (fun x => 0 < q.eval x)
          ∪ p.roots.toFinset.filter (fun x => q.eval x < 0) := by
      rw [← Finset.filter_or]
      exact Finset.filter_congr fun x _ => by
        constructor
        · intro h
          rcases lt_trichotomy (q.eval x) 0 with h' | h' | h'
          · exact Or.inr h'
          · exact absurd h' h
          · exact Or.inl h'
        · rintro (h | h)
          · exact h.ne'
          · exact h.ne
    have hdisj : Disjoint (p.roots.toFinset.filter fun x => 0 < q.eval x)
        (p.roots.toFinset.filter fun x => q.eval x < 0) :=
      Finset.disjoint_left.mpr fun x hx hx' =>
        asymm (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hx').2
    rw [hsplit, Finset.card_union_of_disjoint hdisj]
  rw [hcard]
  ring

omit [IsStrictOrderedRing R] in
/-- The roots of `p` are partitioned by the sign of `q`. -/
theorem card_roots_eq_sign_partition (p q : R[X]) :
    p.roots.toFinset.card
      = (p.roots.toFinset.filter fun x => 0 < q.eval x).card
        + (p.roots.toFinset.filter fun x => q.eval x < 0).card
        + (p.roots.toFinset.filter fun x => q.eval x = 0).card := by
  have h1 := Finset.card_filter_add_card_filter_not
    (s := p.roots.toFinset) (p := fun x => q.eval x = 0)
  have hsplit : p.roots.toFinset.filter (fun x => ¬ q.eval x = 0)
      = p.roots.toFinset.filter (fun x => 0 < q.eval x)
        ∪ p.roots.toFinset.filter (fun x => q.eval x < 0) := by
    rw [← Finset.filter_or]
    exact Finset.filter_congr fun x _ => by
      constructor
      · intro h
        rcases lt_trichotomy (q.eval x) 0 with h' | h' | h'
        · exact Or.inr h'
        · exact absurd h' h
        · exact Or.inl h'
      · rintro (h | h)
        · exact h.ne'
        · exact h.ne
  have hdisj : Disjoint (p.roots.toFinset.filter fun x => 0 < q.eval x)
      (p.roots.toFinset.filter fun x => q.eval x < 0) :=
    Finset.disjoint_left.mpr fun x hx hx' =>
      asymm (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hx').2
  rw [hsplit, Finset.card_union_of_disjoint hdisj] at h1
  omega

end Partition

section Transfer

variable {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Field L] [LinearOrder L] [IsStrictOrderedRing L] {φ : K →+* L}

/-- **Tarski queries are determined by the base ordered field**: for a monotone embedding into a
real closed field, `TaQ(p.map φ, q.map φ)` equals a Sturm sign-variation count computed entirely
inside `K`. -/
theorem tarskiQuery_map_of_strictMono [IsRealClosed L] (hφ : StrictMono φ) (p q : K[X]) :
    tarskiQuery_R (p.map φ) (q.map φ)
      = seqVarRSturm p (Polynomial.derivative p * q) := by
  rw [sturm_tarski_R, Polynomial.derivative_map, ← Polynomial.map_mul,
    seqVarRSturm_map_of_strictMono hφ]

variable {L' : Type*} [Field L'] [LinearOrder L'] [IsStrictOrderedRing L'] {φ' : K →+* L'}

/-- Tarski queries agree across any two real closed order-extensions of `K`. -/
theorem tarskiQuery_map_congr [IsRealClosed L] [IsRealClosed L']
    (hφ : StrictMono φ) (hφ' : StrictMono φ') (p q : K[X]) :
    tarskiQuery_R (p.map φ) (q.map φ) = tarskiQuery_R (p.map φ') (q.map φ') := by
  rw [tarskiQuery_map_of_strictMono hφ, tarskiQuery_map_of_strictMono hφ']

/-- **Positive sign counts are determined by the base ordered field**: the number of roots of `p`
where `q` is positive is the same in every real closed order-extension of `K`. -/
theorem card_roots_filter_pos_congr [IsRealClosed L] [IsRealClosed L']
    (hφ : StrictMono φ) (hφ' : StrictMono φ') (p q : K[X]) :
    ((p.map φ).roots.toFinset.filter fun x => 0 < (q.map φ).eval x).card
      = ((p.map φ').roots.toFinset.filter fun x => 0 < (q.map φ').eval x).card := by
  have h1 := tarskiQuery_R_eq_card_sub_card (p.map φ) (q.map φ)
  have h1' := tarskiQuery_R_eq_card_sub_card (p.map φ') (q.map φ')
  have h2 := tarskiQuery_R_sq_eq_card_add_card (p.map φ) (q.map φ)
  have h2' := tarskiQuery_R_sq_eq_card_add_card (p.map φ') (q.map φ')
  have hq := tarskiQuery_map_congr hφ hφ' p q
  have hq2 : tarskiQuery_R ((p.map φ)) ((q.map φ) ^ 2)
      = tarskiQuery_R ((p.map φ')) ((q.map φ') ^ 2) := by
    rw [← Polynomial.map_pow, ← Polynomial.map_pow]
    exact tarskiQuery_map_congr hφ hφ' p (q ^ 2)
  omega

/-- **Negative sign counts are determined by the base ordered field.** -/
theorem card_roots_filter_neg_congr [IsRealClosed L] [IsRealClosed L']
    (hφ : StrictMono φ) (hφ' : StrictMono φ') (p q : K[X]) :
    ((p.map φ).roots.toFinset.filter fun x => (q.map φ).eval x < 0).card
      = ((p.map φ').roots.toFinset.filter fun x => (q.map φ').eval x < 0).card := by
  have h1 := tarskiQuery_R_eq_card_sub_card (p.map φ) (q.map φ)
  have h1' := tarskiQuery_R_eq_card_sub_card (p.map φ') (q.map φ')
  have h2 := tarskiQuery_R_sq_eq_card_add_card (p.map φ) (q.map φ)
  have h2' := tarskiQuery_R_sq_eq_card_add_card (p.map φ') (q.map φ')
  have hq := tarskiQuery_map_congr hφ hφ' p q
  have hq2 : tarskiQuery_R ((p.map φ)) ((q.map φ) ^ 2)
      = tarskiQuery_R ((p.map φ')) ((q.map φ') ^ 2) := by
    rw [← Polynomial.map_pow, ← Polynomial.map_pow]
    exact tarskiQuery_map_congr hφ hφ' p (q ^ 2)
  omega

/-- **Vanishing counts are determined by the base ordered field**: the number of common roots of
`p` and `q` is the same in every real closed order-extension of `K`. -/
theorem card_roots_filter_eq_zero_congr [IsRealClosed L] [IsRealClosed L']
    (hφ : StrictMono φ) (hφ' : StrictMono φ') (p q : K[X]) :
    ((p.map φ).roots.toFinset.filter fun x => (q.map φ).eval x = 0).card
      = ((p.map φ').roots.toFinset.filter fun x => (q.map φ').eval x = 0).card := by
  have hpart := card_roots_eq_sign_partition (p.map φ) (q.map φ)
  have hpart' := card_roots_eq_sign_partition (p.map φ') (q.map φ')
  have hall : (p.map φ).roots.toFinset.card = (p.map φ').roots.toFinset.card :=
    card_roots_map_congr hφ hφ' p
  have hpos := card_roots_filter_pos_congr hφ hφ' p q
  have hneg := card_roots_filter_neg_congr hφ hφ' p q
  omega

end Transfer

end Sturm
