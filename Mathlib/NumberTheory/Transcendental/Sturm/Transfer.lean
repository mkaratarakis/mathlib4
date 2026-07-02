/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.Sturm.Theorem

/-!
# Transfer of Sturm data along a field embedding

Toward the quantifier-elimination core: the Sturm sign-variation count is invariant under an
order-preserving embedding of real closed fields, so the number of real roots of a polynomial with
coefficients in `K` is the same whether counted in `K` or a real closed extension `L`. This is the
semantic heart of quantifier elimination — realizable sign conditions are determined by the
coefficients, hence transfer between a real closed field and any real closed extension.

The first brick: the Sturm sequence commutes with `Polynomial.map φ` for a ring embedding `φ` of
fields (`sturmSeq_map`), because polynomial remainder commutes with `map` over a field
(`Polynomial.map_mod`).
-/

open Polynomial

namespace Sturm

variable {K L : Type*} [Field K] [LinearOrder K] [Field L] [LinearOrder L]

/-- One-step unfolding of the Sturm sequence at `0`. -/
theorem sturmSeq_zero (g : K[X]) : sturmSeq 0 g = [] := by
  unfold sturmSeq; simp

/-- One-step unfolding of the Sturm sequence at a nonzero head. -/
theorem sturmSeq_cons {f g : K[X]} (hf : f ≠ 0) :
    sturmSeq f g = f :: sturmSeq g (-f % g) := by
  conv_lhs => unfold sturmSeq
  rw [if_neg hf]

/-- The Sturm sequence commutes with `Polynomial.map` along a field hom: mapping the whole sequence
equals the Sturm sequence of the mapped polynomials. -/
theorem sturmSeq_map (φ : K →+* L) (f g : K[X]) :
    (sturmSeq f g).map (Polynomial.map φ) = sturmSeq (f.map φ) (g.map φ) := by
  induction f, g using sturmSeq.induct with
  | case1 g =>
    rw [sturmSeq_zero, Polynomial.map_zero, sturmSeq_zero, List.map_nil]
  | case2 f g hf ih =>
    have hfφ : f.map φ ≠ 0 := by rwa [Ne, Polynomial.map_eq_zero_iff φ.injective]
    rw [sturmSeq_cons hf, List.map_cons, sturmSeq_cons hfφ, ih, Polynomial.map_mod,
      Polynomial.map_neg]

section RealClosed

variable [IsStrictOrderedRing K] [IsRealClosed K] [IsStrictOrderedRing L]

/-- A ring hom between real closed fields preserves nonnegativity (nonnegatives are squares). -/
theorem map_nonneg (φ : K →+* L) {a : K} (ha : 0 ≤ a) : 0 ≤ φ a := by
  obtain ⟨s, rfl⟩ := IsSquare.of_nonneg ha
  rw [map_mul]; exact mul_self_nonneg _

/-- A ring hom between real closed fields reflects nonnegativity, hence is an order embedding. -/
theorem map_nonneg_iff (φ : K →+* L) {a : K} : 0 ≤ φ a ↔ 0 ≤ a := by
  refine ⟨fun h => ?_, map_nonneg φ⟩
  by_contra hlt
  push Not at hlt
  have h2 : 0 ≤ φ (-a) := map_nonneg φ (by linarith)
  rw [map_neg] at h2
  have hφa : φ a = 0 := le_antisymm (by linarith) h
  exact absurd (φ.injective (hφa.trans (map_zero φ).symm)) (by linarith)

/-- A ring hom between real closed fields preserves and reflects strict positivity. -/
theorem map_pos (φ : K →+* L) {a : K} : 0 < φ a ↔ 0 < a := by
  rw [lt_iff_le_and_ne, lt_iff_le_and_ne, map_nonneg_iff, ne_comm, ne_comm (a := (0 : K)),
    ← map_zero φ, φ.injective.ne_iff]

/-- The `sgn` sign function is preserved by a ring hom between real closed fields. -/
theorem sgn_map (φ : K →+* L) (a : K) : sgn (φ a) = sgn a := by
  unfold sgn
  by_cases hpos : 0 < a
  · rw [if_pos ((map_pos φ).mpr hpos), if_pos hpos]
  · by_cases h0 : a = 0
    · subst h0; simp
    · have : ¬ 0 < φ a := fun h => hpos ((map_pos φ).mp h)
      have : φ a ≠ 0 := fun h => h0 (φ.injective (h.trans (map_zero φ).symm))
      rw [if_neg (by assumption), if_neg (by assumption), if_neg hpos, if_neg h0]

/-- A ring hom between real closed fields preserves and reflects strict negativity. -/
theorem map_neg_lt (φ : K →+* L) {a : K} : φ a < 0 ↔ a < 0 := by
  rw [← neg_pos, ← map_neg, map_pos, neg_pos]

/-- The sign at `+∞` is preserved by a ring hom between real closed fields. -/
theorem sgn_pos_inf_map (φ : K →+* L) (p : K[X]) : sgn_pos_inf (p.map φ) = sgn_pos_inf p := by
  unfold sgn_pos_inf; rw [Polynomial.leadingCoeff_map, sgn_map]

/-- The sign at `-∞` is preserved by a ring hom between real closed fields. -/
theorem sgn_neg_inf_map (φ : K →+* L) (p : K[X]) : sgn_neg_inf (p.map φ) = sgn_neg_inf p := by
  unfold sgn_neg_inf; rw [Polynomial.natDegree_map, Polynomial.leadingCoeff_map, sgn_map]

/-- The sign-variation count of a list is invariant under a ring hom between real closed fields. -/
theorem seqVar_map (φ : K →+* L) (l : List K) : seqVar (l.map φ) = seqVar l := by
  induction l using seqVar.induct with
  | case1 => simp [seqVar]
  | case2 a => simp [seqVar]
  | case3 a b as hb ih =>
    have hbφ : (φ b == 0) = true := by
      rw [beq_iff_eq] at hb ⊢; rw [hb, map_zero]
    simp only [List.map_cons, seqVar, hb, hbφ, if_true]
    rw [← List.map_cons]; exact ih
  | case4 a b as hb hab ih =>
    have hbφ : ¬ (φ b == 0) = true := by
      rw [beq_iff_eq] at hb ⊢
      exact fun h => hb (φ.injective (h.trans (map_zero φ).symm))
    have hltφ : φ a * φ b < 0 := by rw [← map_mul]; exact (map_neg_lt φ).mpr hab
    rw [List.map_cons, List.map_cons, seqVar, if_neg hbφ, if_pos hltφ, ← List.map_cons, ih,
      seqVar, if_neg hb, if_pos hab]
  | case5 a b as hb hab ih =>
    have hbφ : ¬ (φ b == 0) = true := by
      rw [beq_iff_eq] at hb ⊢
      exact fun h => hb (φ.injective (h.trans (map_zero φ).symm))
    have hltφ : ¬ φ a * φ b < 0 := by rw [← map_mul]; rwa [map_neg_lt φ]
    rw [List.map_cons, List.map_cons, seqVar, if_neg hbφ, if_neg hltφ, ← List.map_cons, ih,
      seqVar, if_neg hb, if_neg hab]

theorem seq_sgn_pos_inf_map (φ : K →+* L) (P : List K[X]) :
    seq_sgn_pos_inf (P.map (Polynomial.map φ)) = (seq_sgn_pos_inf P).map φ := by
  induction P with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, seq_sgn_pos_inf, sgn_pos_inf_map, map_intCast, ih]

theorem seq_sgn_neg_inf_map (φ : K →+* L) (P : List K[X]) :
    seq_sgn_neg_inf (P.map (Polynomial.map φ)) = (seq_sgn_neg_inf P).map φ := by
  induction P with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, seq_sgn_neg_inf, sgn_neg_inf_map, map_intCast, ih]

/-- The total Sturm sign-variation count is invariant under a ring hom between real closed
fields. -/
theorem seqVarRSturm_map (φ : K →+* L) (f g : K[X]) :
    seqVarRSturm (f.map φ) (g.map φ) = seqVarRSturm f g := by
  unfold seqVarRSturm seqVarR
  rw [← sturmSeq_map, seq_sgn_neg_inf_map, seq_sgn_pos_inf_map, seqVar_map, seqVar_map]

/-- **Root count is preserved under a real closed field extension.** A polynomial over `K` has the
same number of distinct roots in `K` as its image has in a real closed extension `L`. -/
theorem card_roots_map [IsRealClosed L] (φ : K →+* L) (p : K[X]) :
    (p.map φ).roots.toFinset.card = p.roots.toFinset.card := by
  have hL := sturm_R (p.map φ)
  rw [Polynomial.derivative_map, seqVarRSturm_map, ← sturm_R p] at hL
  exact_mod_cast hL

/-- **Roots do not move under a real closed extension.** The set of roots of `p.map φ` in `L` is
exactly the `φ`-image of the set of roots of `p` in `K`: the embedded copies exhaust the root count
given by `card_roots_map`, so no new roots can appear upstairs. -/
theorem roots_toFinset_map [IsRealClosed L] (φ : K →+* L) (p : K[X]) :
    (p.map φ).roots.toFinset = p.roots.toFinset.image φ := by
  have hsub : p.roots.toFinset.image φ ⊆ (p.map φ).roots.toFinset := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [Multiset.mem_toFinset] at hx ⊢
    exact Multiset.mem_of_le (Polynomial.map_roots_le_of_injective p φ.injective)
      (Multiset.mem_map_of_mem _ hx)
  refine (Finset.eq_of_subset_of_card_le hsub (le_of_eq ?_)).symm
  rw [card_roots_map φ p, Finset.card_image_of_injective _ φ.injective]

/-- **Root existence descends along a real closed extension**: a polynomial over `K` has a root in
a real closed extension `L` iff it already has a root in `K`. -/
theorem exists_isRoot_map_iff [IsRealClosed L] (φ : K →+* L) {p : K[X]} (hp : p ≠ 0) :
    (∃ y : L, (p.map φ).IsRoot y) ↔ ∃ x : K, p.IsRoot x := by
  constructor
  · rintro ⟨y, hy⟩
    have hy' : y ∈ (p.map φ).roots.toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots']
      exact ⟨(Polynomial.map_ne_zero_iff φ.injective).mpr hp, hy⟩
    rw [roots_toFinset_map φ p] at hy'
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy'
    exact ⟨x, (Polynomial.mem_roots'.mp (Multiset.mem_toFinset.mp hx)).2⟩
  · rintro ⟨x, hx⟩
    exact ⟨φ x, hx.map⟩

end RealClosed

end Sturm
