/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.Sturm.Theorem
import Mathlib.NumberTheory.Transcendental.Hilbert17IVP

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

section SignPersistence

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **Sign persistence on a root-free interval.** If a polynomial has no root on `[u, v]`, then its
values at `u` and `v` are negative together (by the intermediate value property). -/
theorem eval_neg_iff_of_no_root {p : R[X]} {u v : R} (huv : u ≤ v)
    (hroot : ∀ z, u ≤ z → z ≤ v → ¬ p.IsRoot z) :
    p.eval u < 0 ↔ p.eval v < 0 := by
  constructor
  · intro hu
    by_contra hv
    push Not at hv
    obtain ⟨z, hz, hz0⟩ := IsRealClosed.intermediate_value_property (f := -p) huv
      (by simpa using hu.le) (by simpa using hv)
    exact hroot z hz.1 hz.2 (by simpa [Polynomial.IsRoot] using hz0)
  · intro hv
    by_contra hu
    push Not at hu
    obtain ⟨z, hz, hz0⟩ := IsRealClosed.intermediate_value_property huv hu hv.le
    exact hroot z hz.1 hz.2 hz0

end SignPersistence

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

/-- A ring hom between real closed fields is strictly monotone. -/
theorem strictMono_map (φ : K →+* L) : StrictMono φ := fun a b hab => by
  have h : (0 : L) < φ (b - a) := (map_pos φ).mpr (sub_pos.mpr hab)
  rw [map_sub] at h
  linarith

omit [LinearOrder K] [LinearOrder L] [IsStrictOrderedRing K] [IsRealClosed K]
  [IsStrictOrderedRing L] in
/-- Evaluating the mapped polynomial at an embedded point computes in `K`. -/
theorem eval_map_apply (φ : K →+* L) (p : K[X]) (x : K) :
    (p.map φ).eval (φ x) = φ (p.eval x) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]

/-- If `p.map φ` is negative at `y` and has no root between `y` and the embedded point `φ x`,
then `p` is negative at `x`. -/
theorem eval_neg_at_of_no_root_between [IsRealClosed L] (φ : K →+* L) {p : K[X]} {y : L} {x : K}
    (hy : (p.map φ).eval y < 0)
    (hroot : ∀ z ∈ Set.uIcc y (φ x), ¬ (p.map φ).IsRoot z) :
    p.eval x < 0 := by
  have hφx : (p.map φ).eval (φ x) < 0 := by
    rcases le_total y (φ x) with h | h
    · exact (eval_neg_iff_of_no_root h
        (fun z hz1 hz2 => hroot z (Set.mem_uIcc.mpr (.inl ⟨hz1, hz2⟩)))).mp hy
    · exact (eval_neg_iff_of_no_root h
        (fun z hz1 hz2 => hroot z (Set.mem_uIcc.mpr (.inr ⟨hz1, hz2⟩)))).mpr hy
  rw [eval_map_apply] at hφx
  exact (map_neg_lt φ).mp hφx

/-- **Negativity descends along a real closed extension**: a polynomial over `K` takes a negative
value in a real closed extension `L` iff it already takes a negative value in `K`. The witness in
`K` is found by sampling: beyond all roots if `y` is extreme, or at the midpoint of the two
consecutive roots surrounding `y` otherwise — sign persistence on root-free intervals
(`eval_neg_iff_of_no_root`) plus `roots_toFinset_map` (roots do not move) do the rest. This is the
one-polynomial prototype of sign-condition transfer for quantifier elimination. -/
theorem exists_eval_neg_map_iff [IsRealClosed L] (φ : K →+* L) (p : K[X]) :
    (∃ y : L, (p.map φ).eval y < 0) ↔ ∃ x : K, p.eval x < 0 := by
  constructor
  · rintro ⟨y, hy⟩
    rcases eq_or_ne p 0 with rfl | hp
    · simp at hy
    set S := p.roots.toFinset with hSdef
    have hT : (p.map φ).roots.toFinset = S.image φ := roots_toFinset_map φ p
    -- every root of `p.map φ` is an embedded root, and `y` is not a root
    have hroot_shape : ∀ z : L, (p.map φ).IsRoot z → ∃ r ∈ S, φ r = z := by
      intro z hz
      have hz' : z ∈ (p.map φ).roots.toFinset := by
        rw [Multiset.mem_toFinset, Polynomial.mem_roots']
        exact ⟨(Polynomial.map_ne_zero_iff φ.injective).mpr hp, hz⟩
      rw [hT] at hz'
      exact Finset.mem_image.mp hz'
    have hynr : ∀ r ∈ S, φ r ≠ y := by
      intro r hr hry
      have hymem : y ∈ (p.map φ).roots.toFinset := by
        rw [hT, ← hry]
        exact Finset.mem_image_of_mem φ hr
      exact hy.ne (Polynomial.mem_roots'.mp (Multiset.mem_toFinset.mp hymem)).2
    rcases S.eq_empty_or_nonempty with hSe | hne
    · -- no roots at all: the sign is global; sample at `0`
      refine ⟨0, eval_neg_at_of_no_root_between φ hy ?_⟩
      intro z _ hzroot
      obtain ⟨r, hr, _⟩ := hroot_shape z hzroot
      simp [hSe] at hr
    rcases lt_or_ge y (φ (S.min' hne)) with hlo | hlo
    · -- below all embedded roots: sample below the least root of `p`
      refine ⟨S.min' hne - 1, eval_neg_at_of_no_root_between φ hy ?_⟩
      intro z hzmem hzroot
      obtain ⟨r, hr, rfl⟩ := hroot_shape z hzroot
      have h1 : φ (S.min' hne) ≤ φ r := (strictMono_map φ).monotone (S.min'_le r hr)
      have h2 : φ (S.min' hne - 1) < φ (S.min' hne) := strictMono_map φ (by linarith)
      rcases Set.mem_uIcc.mp hzmem with ⟨_, hzb⟩ | ⟨_, hzb⟩ <;> linarith
    rcases lt_or_ge (φ (S.max' hne)) y with hhi | hhi
    · -- above all embedded roots: sample above the greatest root of `p`
      refine ⟨S.max' hne + 1, eval_neg_at_of_no_root_between φ hy ?_⟩
      intro z hzmem hzroot
      obtain ⟨r, hr, rfl⟩ := hroot_shape z hzroot
      have h1 : φ r ≤ φ (S.max' hne) := (strictMono_map φ).monotone (S.le_max' r hr)
      have h2 : φ (S.max' hne) < φ (S.max' hne + 1) := strictMono_map φ (by linarith)
      rcases Set.mem_uIcc.mp hzmem with ⟨hza, _⟩ | ⟨hza, _⟩ <;> linarith
    · -- strictly between two consecutive embedded roots: sample at the midpoint
      set S₁ := S.filter (fun r => φ r < y) with hS₁
      set S₂ := S.filter (fun r => y < φ r) with hS₂
      have h1ne : S₁.Nonempty := by
        refine ⟨S.min' hne, Finset.mem_filter.mpr ⟨S.min'_mem hne, ?_⟩⟩
        exact lt_of_le_of_ne hlo (hynr _ (S.min'_mem hne))
      have h2ne : S₂.Nonempty := by
        refine ⟨S.max' hne, Finset.mem_filter.mpr ⟨S.max'_mem hne, ?_⟩⟩
        exact lt_of_le_of_ne hhi (Ne.symm (hynr _ (S.max'_mem hne)))
      set r₁ := S₁.max' h1ne with hr₁def
      set r₂ := S₂.min' h2ne with hr₂def
      have hr₁ : φ r₁ < y := (Finset.mem_filter.mp (S₁.max'_mem h1ne)).2
      have hr₂ : y < φ r₂ := (Finset.mem_filter.mp (S₂.min'_mem h2ne)).2
      have hr₁₂ : r₁ < r₂ := (strictMono_map φ).lt_iff_lt.mp (hr₁.trans hr₂)
      refine ⟨(r₁ + r₂) / 2, eval_neg_at_of_no_root_between φ hy ?_⟩
      have hφ1 : φ r₁ < φ ((r₁ + r₂) / 2) := strictMono_map φ (left_lt_add_div_two.mpr hr₁₂)
      have hφ2 : φ ((r₁ + r₂) / 2) < φ r₂ := strictMono_map φ (add_div_two_lt_right.mpr hr₁₂)
      intro z hzmem hzroot
      obtain ⟨r, hr, rfl⟩ := hroot_shape z hzroot
      -- the root `φ r` lies strictly between `φ r₁` and `φ r₂`
      have hzlo : φ r₁ < φ r := by
        rcases Set.mem_uIcc.mp hzmem with ⟨hza, _⟩ | ⟨hza, _⟩ <;> linarith
      have hzhi : φ r < φ r₂ := by
        rcases Set.mem_uIcc.mp hzmem with ⟨_, hzb⟩ | ⟨_, hzb⟩ <;> linarith
      -- but `r₁` and `r₂` are consecutive: no root of `p` sits strictly between them
      rcases lt_trichotomy (φ r) y with hry | hry | hry
      · have hrS₁ : r ∈ S₁ := Finset.mem_filter.mpr ⟨hr, hry⟩
        have hle := S₁.le_max' r hrS₁
        have hlt := (strictMono_map φ).lt_iff_lt.mp hzlo
        linarith
      · exact hynr r hr hry
      · have hrS₂ : r ∈ S₂ := Finset.mem_filter.mpr ⟨hr, hry⟩
        have hle := S₂.min'_le r hrS₂
        have hlt := (strictMono_map φ).lt_iff_lt.mp hzhi
        linarith
  · rintro ⟨x, hx⟩
    exact ⟨φ x, by rw [eval_map_apply]; exact (map_neg_lt φ).mpr hx⟩

/-- **Positivity descends along a real closed extension.** -/
theorem exists_eval_pos_map_iff [IsRealClosed L] (φ : K →+* L) (p : K[X]) :
    (∃ y : L, 0 < (p.map φ).eval y) ↔ ∃ x : K, 0 < p.eval x := by
  have h := exists_eval_neg_map_iff φ (-p)
  simpa only [Polynomial.map_neg, Polynomial.eval_neg, neg_lt_zero] using h

end RealClosed

end Sturm
