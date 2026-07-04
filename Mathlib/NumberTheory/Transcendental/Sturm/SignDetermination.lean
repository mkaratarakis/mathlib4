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

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

omit [IsStrictOrderedRing R] in
theorem sgn_of_pos' {a : R} (h : 0 < a) : sgn a = 1 := by
  unfold sgn; rw [if_pos h]

omit [IsStrictOrderedRing R] in
theorem sgn_of_neg' {a : R} (h : a < 0) : sgn a = -1 := by
  unfold sgn; rw [if_neg (asymm h), if_neg h.ne]

omit [IsStrictOrderedRing R] in
theorem sgn_zero'' : sgn (0 : R) = 0 := by
  unfold sgn; rw [if_neg (lt_irrefl 0), if_pos rfl]

/-- The sign function is multiplicative. -/
theorem sgn_mul (a b : R) : sgn (a * b) = sgn a * sgn b := by
  rcases lt_trichotomy a 0 with ha | rfl | ha <;> rcases lt_trichotomy b 0 with hb | rfl | hb
  · rw [sgn_of_pos' (mul_pos_of_neg_of_neg ha hb), sgn_of_neg' ha, sgn_of_neg' hb]; norm_num
  · simp [sgn_zero'']
  · rw [sgn_of_neg' (mul_neg_of_neg_of_pos ha hb), sgn_of_neg' ha, sgn_of_pos' hb]; norm_num
  · simp [sgn_zero'']
  · simp [sgn_zero'']
  · simp [sgn_zero'']
  · rw [sgn_of_neg' (mul_neg_of_pos_of_neg ha hb), sgn_of_pos' ha, sgn_of_neg' hb]; norm_num
  · simp [sgn_zero'']
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
  · simp only [mul_zero, sgn_zero'', zero_add]
    rcases he with rfl | rfl
    · rw [if_neg (by norm_num)]
    · rw [if_neg (by norm_num)]
  · rw [sgn_of_pos' hv, sgn_of_pos' (mul_pos hv hv)]
    rcases he with rfl | rfl
    · rw [if_pos rfl]; ring
    · rw [if_neg (by norm_num)]; ring

end SgnAlgebra

section Identity

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] {m : ℕ}

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
  have hterm : ∀ x : R,
      (∏ i ∈ S, ε i * sgn ((q i).eval x)) *
          ∏ i ∈ Finset.univ \ S, sgn ((q i).eval x * (q i).eval x)
        = (∏ i ∈ S, ε i) *
            sgn (((∏ i ∈ S, q i) * ∏ i ∈ Finset.univ \ S, (q i) ^ 2).eval x) := by
    intro x
    have hsq : ∀ i ∈ Finset.univ \ S, sgn (((q i) ^ 2).eval x)
        = sgn ((q i).eval x * (q i).eval x) := fun i _ => by rw [eval_pow, sq]
    rw [Finset.prod_mul_distrib, eval_mul, eval_prod, eval_prod, sgn_mul, sgn_prod, sgn_prod,
      Finset.prod_congr rfl hsq, mul_assoc]
  rw [Finset.sum_congr rfl fun x _ => hterm x]
  simp only [tarskiQuery_R]
  rw [Finset.mul_sum]

end Identity

section Transfer

variable {K L L' : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Field L] [LinearOrder L] [IsStrictOrderedRing L]
  [Field L'] [LinearOrder L'] [IsStrictOrderedRing L'] {m : ℕ}

/-- **Joint sign-vector counts are determined by the base ordered field**: for a family `q` of
polynomials over `K` and a nonzero sign vector `ε`, the number of roots of `p` at which the family
realizes `ε` is the same in every real closed order-extension of `K`. Applied to the iterated
derivatives of `p`, the multiset of Thom encodings of the roots of `p` is base-determined. -/
theorem card_roots_filter_sgn_vector_congr [IsRealClosed L] [IsRealClosed L']
    {φ : K →+* L} {φ' : K →+* L'} (hφ : StrictMono φ) (hφ' : StrictMono φ')
    (p : K[X]) (q : Fin m → K[X]) (ε : Fin m → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    ((p.map φ).roots.toFinset.filter
        (fun x => ∀ i, sgn (((q i).map φ).eval x) = ε i)).card
      = ((p.map φ').roots.toFinset.filter
          (fun x => ∀ i, sgn (((q i).map φ').eval x) = ε i)).card := by
  classical
  have h1 := two_pow_mul_card_sgn_vector (p.map φ) (fun i => (q i).map φ) ε hε
  have h2 := two_pow_mul_card_sgn_vector (p.map φ') (fun i => (q i).map φ') ε hε
  -- each Tarski query on the right is the image of a `K`-datum, hence transfers
  have hq : ∀ S : Finset (Fin m),
      tarskiQuery_R (p.map φ)
          ((∏ i ∈ S, (q i).map φ) * ∏ i ∈ Finset.univ \ S, ((q i).map φ) ^ 2)
        = tarskiQuery_R (p.map φ')
            ((∏ i ∈ S, (q i).map φ') * ∏ i ∈ Finset.univ \ S, ((q i).map φ') ^ 2) := by
    intro S
    have hmapφ : (∏ i ∈ S, (q i).map φ) * ∏ i ∈ Finset.univ \ S, ((q i).map φ) ^ 2
        = ((∏ i ∈ S, q i) * ∏ i ∈ Finset.univ \ S, (q i) ^ 2).map φ := by
      rw [Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_prod]
      simp [Polynomial.map_pow]
    have hmapφ' : (∏ i ∈ S, (q i).map φ') * ∏ i ∈ Finset.univ \ S, ((q i).map φ') ^ 2
        = ((∏ i ∈ S, q i) * ∏ i ∈ Finset.univ \ S, (q i) ^ 2).map φ' := by
      rw [Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_prod]
      simp [Polynomial.map_pow]
    rw [hmapφ, hmapφ', tarskiQuery_map_congr hφ hφ']
  rw [Finset.sum_congr rfl fun S _ => by rw [hq S]] at h1
  have h12 := h1.trans h2.symm
  have hpow : (2 ^ m : ℤ) ≠ 0 := pow_ne_zero m two_ne_zero
  exact_mod_cast mul_left_cancel₀ hpow h12

end Transfer

end Sturm
