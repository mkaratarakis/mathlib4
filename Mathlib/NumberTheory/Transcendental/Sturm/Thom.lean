/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.Sturm.Rolle

/-!
# Thom's lemma over a real closed field

**Thom's lemma**: on the set where all derivatives of a polynomial `p` have prescribed signs, the
sign of `p` itself is constant — formulated here as convexity (`thom_convex`): if the signs of
`p, p', p'', …` all agree at two points `x ≤ y`, they take those same values everywhere on
`[x, y]`. The key consequence is **separation** (`thom_separation`): two distinct roots of `p`
are distinguished by the sign of some derivative. This is what makes the *Thom encoding* of a
real algebraic number well defined, and it powers the sign-sequence determination behind
order-compatible root matching (uniqueness of real closures) and quantifier elimination.

The engine is purely algebraic monotonicity (`eval_lt_eval_of_forall_derivative_pos`): if `p' > 0`
on `[x, y]` then `p(x) < p(y)`, proved from Rolle (`Sturm.rolle`) — a descent `p(x) > p(y)` would
give the shifted polynomial `q = p - p(y)` a second root just left of `y` (found by dodging the
finitely many roots of `q·w`, where `q = (X - y)w`), and Rolle would then plant a root of `p'`
inside the interval.

Everything is over an abstract real closed field: no analysis, no completeness of `ℝ`.
-/

open Polynomial

namespace Sturm

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-! ### Sign helpers -/

omit [IsStrictOrderedRing R] [IsRealClosed R] in
private theorem sgn_pos_iff {a : R} : sgn a = 1 ↔ 0 < a := by
  unfold sgn
  split_ifs with h1 h2
  · simp [h1]
  · simp [h2]
  · constructor
    · intro hh; norm_num at hh
    · intro hh; exact absurd hh h1

omit [IsStrictOrderedRing R] [IsRealClosed R] in
private theorem sgn_zero_iff {a : R} : sgn a = 0 ↔ a = 0 := by
  unfold sgn
  split_ifs with h1 h2
  · simp [h1.ne']
  · simp [h2]
  · simp [h2]

omit [IsStrictOrderedRing R] [IsRealClosed R] in
private theorem pos_of_sgn_eq {a b : R} (h : sgn a = sgn b) (hb : 0 < b) : 0 < a :=
  sgn_pos_iff.mp (h.trans (sgn_pos_iff.mpr hb))

omit [IsStrictOrderedRing R] [IsRealClosed R] in
private theorem eq_zero_of_sgn_eq_zero {a : R} (h : sgn a = 0) : a = 0 :=
  sgn_zero_iff.mp h

omit [IsStrictOrderedRing R] [IsRealClosed R] in
private theorem sgn_zero' : sgn (0 : R) = 0 := sgn_zero_iff.mpr rfl

/-! ### Monotonicity from derivative positivity, algebraically -/

/-- **Strict monotonicity from a positive derivative**, over a real closed field, with no
analysis: if `p' > 0` throughout `[x, y]` then `p(x) < p(y)`. Equality is killed by Rolle
directly; a descent `p(x) > p(y)` gives the shifted polynomial `q = p - p(y)` a sign change
between `x` and a point just left of `y` (dodging the roots of `q·w` where `q = (X - y)·w`),
hence a second root, and Rolle plants a root of `p'` in `(x, y)`. -/
theorem eval_lt_eval_of_forall_derivative_pos {p : R[X]} {x y : R} (hxy : x < y)
    (hpos : ∀ z, x ≤ z → z ≤ y → 0 < p.derivative.eval z) :
    p.eval x < p.eval y := by
  rcases lt_trichotomy (p.eval x) (p.eval y) with h | h | h
  · exact h
  · -- equal values: Rolle on the shift kills the positive derivative
    exfalso
    set q := p - C (p.eval y) with hqdef
    have hq' : q.derivative = p.derivative := by
      rw [hqdef, derivative_sub, derivative_C, sub_zero]
    have hqx : q.IsRoot x := by simp [hqdef, h]
    have hqy : q.IsRoot y := by simp [hqdef]
    obtain ⟨c, hc₁, hc₂, hcroot⟩ := rolle hxy hqx hqy
    rw [hq'] at hcroot
    exact absurd hcroot (hpos c hc₁.le hc₂.le).ne'
  · -- descent: manufacture a second root of the shift, then Rolle
    exfalso
    set q := p - C (p.eval y) with hqdef
    have hq' : q.derivative = p.derivative := by
      rw [hqdef, derivative_sub, derivative_C, sub_zero]
    have hqx : 0 < q.eval x := by
      rw [hqdef, eval_sub, eval_C]
      linarith
    have hqy : q.IsRoot y := by simp [hqdef]
    obtain ⟨w, hw⟩ := dvd_iff_isRoot.mpr hqy
    -- the cofactor is positive at `y` (it equals `p'(y)` there)
    have hwy : w.eval y = p.derivative.eval y := by
      have hqd : q.derivative = w + (X - C y) * w.derivative := by
        rw [hw, derivative_mul, derivative_X_sub_C]
        ring
      have := congrArg (eval y) hqd
      rw [hq'] at this
      simpa using this.symm
    have hwypos : 0 < w.eval y := hwy ▸ hpos y hxy.le le_rfl
    have hqne : q ≠ 0 := fun h0 => by simp [h0] at hqx
    have hwne : w ≠ 0 := fun h0 => by rw [h0] at hwypos; simp at hwypos
    -- a sample point `s` just left of `y`, past every root of `q·w`
    set M := insert x (((q * w).roots.toFinset.filter (fun z => z < y))) with hM
    have hMne : M.Nonempty := Finset.insert_nonempty _ _
    have hMlt : M.max' hMne < y := by
      rw [Finset.max'_lt_iff]
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz'
      · exact hxy
      · exact (Finset.mem_filter.mp hz').2
    set s := (M.max' hMne + y) / 2 with hs
    have hMs : M.max' hMne < s := left_lt_add_div_two.mpr hMlt
    have hsy : s < y := add_div_two_lt_right.mpr hMlt
    have hxs : x < s := lt_of_le_of_lt (M.le_max' x (Finset.mem_insert_self x _)) hMs
    -- no roots of `q·w` in `[s, y)`
    have hnoroot : ∀ z, s ≤ z → z < y → ¬ (q * w).IsRoot z := by
      intro z hsz hzy hzroot
      have hzmem : z ∈ M := Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨Multiset.mem_toFinset.mpr (mem_roots'.mpr ⟨mul_ne_zero hqne hwne, hzroot⟩), hzy⟩))
      exact absurd (lt_of_le_of_lt (M.le_max' z hzmem) hMs) (not_lt.mpr hsz)
    -- `w` is positive at `s` by sign constancy on `[s, y]`
    have hwnoroot : ∀ z ∈ Set.uIcc s y, ¬ w.IsRoot z := by
      intro z hz hzroot
      rw [Set.uIcc_of_le hsy.le] at hz
      rcases eq_or_lt_of_le hz.2 with h₂ | h₂
      · exact hwypos.ne' (h₂ ▸ hzroot)
      · exact hnoroot z hz.1 h₂ (by rw [IsRoot, eval_mul, hzroot, mul_zero])
    have hws : 0 < w.eval s :=
      pos_of_sgn_eq (sgn_eval_eq_of_no_root_uIcc hwnoroot) hwypos
    -- hence `q(s) < 0`, giving a sign change of `q` on `(x, s)`
    have hqs : q.eval s < 0 := by
      rw [hw, eval_mul, eval_sub, eval_X, eval_C]
      exact mul_neg_of_neg_of_pos (sub_neg.mpr hsy) hws
    obtain ⟨r, hr₁, hr₂, hrroot⟩ :=
      exists_isRoot_of_eval_mul_neg hxs (mul_neg_of_pos_of_neg hqx hqs)
    -- two roots `r < y` of `q`: Rolle plants a root of `p'` in `(x, y)`
    obtain ⟨c, hc₁, hc₂, hcroot⟩ := rolle (lt_trans hr₂ hsy) hrroot hqy
    rw [hq'] at hcroot
    exact absurd hcroot
      (hpos c (le_of_lt (lt_trans hr₁ hc₁)) hc₂.le).ne'

/-- Monotone decrease from a negative derivative (mirror of
`eval_lt_eval_of_forall_derivative_pos`, applied to `-p`). -/
theorem eval_lt_eval_of_forall_derivative_neg {p : R[X]} {x y : R} (hxy : x < y)
    (hneg : ∀ z, x ≤ z → z ≤ y → p.derivative.eval z < 0) :
    p.eval y < p.eval x := by
  have := eval_lt_eval_of_forall_derivative_pos (p := -p) hxy (fun z hz hz' => by
    rw [derivative_neg, eval_neg]
    linarith [hneg z hz hz'])
  simp only [eval_neg] at this
  linarith

/-! ### Thom's lemma -/

/-- **Thom's lemma, convexity form.** If the signs of all iterated derivatives
`p, p', …, p^(natDegree p)` agree at `x` and at `y`, then they take those same values at every
point of `[x, y]`. Induction on the degree: the derivative-sign hypotheses make `p'` of constant
sign on `[x, y]` (inductively), so `p` is monotone (or constant) there, and a value squeezed
between two values of equal sign has that sign. -/
theorem thom_convex {p : R[X]} {x y : R} (hxy : x ≤ y)
    (hsgn : ∀ k, k ≤ p.natDegree →
      sgn ((derivative^[k] p).eval x) = sgn ((derivative^[k] p).eval y)) :
    ∀ z, x ≤ z → z ≤ y → ∀ k, k ≤ p.natDegree →
      sgn ((derivative^[k] p).eval z) = sgn ((derivative^[k] p).eval x) := by
  induction hd : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ d ih =>
  subst hd
  intro z hxz hzy k hk
  by_cases hd0 : p.natDegree = 0
  · -- constant polynomial
    have hk0 : k = 0 := by omega
    subst hk0
    rw [p.eq_C_of_natDegree_eq_zero hd0]
    simp
  -- shift the hypothesis to the derivative
  have hshift : ∀ j, derivative^[j] (derivative p) = derivative^[j + 1] p := fun j =>
    (Function.iterate_succ_apply derivative j p).symm
  have hdlt : (derivative p).natDegree < p.natDegree :=
    natDegree_derivative_lt hd0
  have hsgn' : ∀ j, j ≤ (derivative p).natDegree →
      sgn ((derivative^[j] (derivative p)).eval x)
        = sgn ((derivative^[j] (derivative p)).eval y) := fun j hj => by
    rw [hshift]
    exact hsgn (j + 1) (by omega)
  have IH := ih (derivative p).natDegree hdlt (p := derivative p) hsgn' rfl
  rcases k with _ | k'
  · -- `k = 0`: the sign of `p` itself, via monotonicity
    simp only [Function.iterate_zero, id] at *
    -- the derivative has constant sign class on `[x, y]`
    have hder : ∀ w, x ≤ w → w ≤ y → sgn (p.derivative.eval w) = sgn (p.derivative.eval x) := by
      intro w hw hw'
      have := IH w hw hw' 0 (Nat.zero_le _)
      simpa using this
    rcases lt_trichotomy (p.derivative.eval x) 0 with hcase | hcase | hcase
    · -- decreasing
      have hneg : ∀ w, x ≤ w → w ≤ y → p.derivative.eval w < 0 := by
        intro w hw hw'
        have h := hder w hw hw'
        rcases lt_trichotomy (p.derivative.eval w) 0 with h' | h' | h'
        · exact h'
        · exfalso
          rw [h', sgn_zero'] at h
          exact hcase.ne (eq_zero_of_sgn_eq_zero h.symm)
        · exfalso
          exact hcase.not_gt (pos_of_sgn_eq (hder w hw hw').symm h')
      have h₁ : p.eval z ≤ p.eval x := by
        rcases eq_or_lt_of_le hxz with rfl | h'
        · exact le_refl _
        · exact (eval_lt_eval_of_forall_derivative_neg h'
            (fun w hw hw' => hneg w hw (le_trans hw' hzy))).le
      have h₂ : p.eval y ≤ p.eval z := by
        rcases eq_or_lt_of_le hzy with rfl | h'
        · exact le_refl _
        · exact (eval_lt_eval_of_forall_derivative_neg h'
            (fun w hw hw' => hneg w (le_trans hxz hw) hw')).le
      -- squeeze the sign
      have h0 := hsgn 0 (Nat.zero_le _)
      simp only [Function.iterate_zero, id] at h0
      rcases lt_trichotomy (p.eval x) 0 with hs | hs | hs
      · -- both ends negative
        unfold sgn
        rw [if_neg (asymm hs), if_neg hs.ne, if_neg (by linarith : ¬ 0 < p.eval z),
          if_neg (by linarith : ¬ p.eval z = 0)]
      · -- both ends zero
        have hy0 : p.eval y = 0 := eq_zero_of_sgn_eq_zero (by rw [← h0, hs, sgn_zero'])
        have hz0 : p.eval z = 0 := le_antisymm (hs ▸ h₁) (hy0 ▸ h₂)
        rw [hz0, hs]
      · -- both ends positive
        have hy0 : 0 < p.eval y := pos_of_sgn_eq h0.symm hs
        unfold sgn
        rw [if_pos hs, if_pos (by linarith : 0 < p.eval z)]
    · -- derivative vanishes identically on `[x, y]`
      rcases eq_or_lt_of_le hxy with rfl | hxy'
      · have : z = x := le_antisymm hzy hxz
        rw [this]
      · exfalso
        have hzero : ∀ w ∈ Set.Icc x y, p.derivative.IsRoot w := by
          intro w hw
          exact eq_zero_of_sgn_eq_zero (by rw [hder w hw.1 hw.2, hcase, sgn_zero'])
        have hinf : {w | p.derivative.IsRoot w}.Infinite :=
          Set.Infinite.mono hzero (Set.infinite_coe_iff.mp ⟨(Set.Icc.infinite hxy').1⟩)
        have hder0 : p.derivative = 0 := p.derivative.eq_zero_of_infinite_isRoot hinf
        exact hd0 (Polynomial.derivative_eq_zero.mp hder0)
    · -- increasing (mirror of the first case)
      have hpos : ∀ w, x ≤ w → w ≤ y → 0 < p.derivative.eval w := by
        intro w hw hw'
        exact pos_of_sgn_eq (hder w hw hw') hcase
      have h₁ : p.eval x ≤ p.eval z := by
        rcases eq_or_lt_of_le hxz with rfl | h'
        · exact le_refl _
        · exact (eval_lt_eval_of_forall_derivative_pos h'
            (fun w hw hw' => hpos w hw (le_trans hw' hzy))).le
      have h₂ : p.eval z ≤ p.eval y := by
        rcases eq_or_lt_of_le hzy with rfl | h'
        · exact le_refl _
        · exact (eval_lt_eval_of_forall_derivative_pos h'
            (fun w hw hw' => hpos w (le_trans hxz hw) hw')).le
      have h0 := hsgn 0 (Nat.zero_le _)
      simp only [Function.iterate_zero, id] at h0
      rcases lt_trichotomy (p.eval x) 0 with hs | hs | hs
      · have hy0 : p.eval y < 0 := by
          rcases lt_trichotomy (p.eval y) 0 with h' | h' | h'
          · exact h'
          · exfalso; rw [h', sgn_zero'] at h0; exact hs.ne (eq_zero_of_sgn_eq_zero h0)
          · exfalso; exact hs.not_gt (pos_of_sgn_eq h0 h')
        unfold sgn
        rw [if_neg (asymm hs), if_neg hs.ne, if_neg (by linarith : ¬ 0 < p.eval z),
          if_neg (by linarith : ¬ p.eval z = 0)]
      · have hy0 : p.eval y = 0 := eq_zero_of_sgn_eq_zero (by rw [← h0, hs, sgn_zero'])
        have hz0 : p.eval z = 0 := le_antisymm (hy0 ▸ h₂) (hs ▸ h₁)
        rw [hz0, hs]
      · unfold sgn
        rw [if_pos hs, if_pos (by linarith : 0 < p.eval z)]
  · -- `k = k' + 1`: inherited from the derivative
    by_cases hk' : k' ≤ (derivative p).natDegree
    · have := IH z hxz hzy k' hk'
      rwa [hshift] at this
    · -- beyond the degree of the derivative: the iterated derivative vanishes
      have h0 : derivative^[k' + 1] p = 0 := by
        rw [← hshift]
        exact iterate_derivative_eq_zero (by omega)
      rw [h0]
      simp

/-- **Thom separation**: two distinct roots of a nonzero polynomial are distinguished by the sign
of some derivative. Equivalently, the *Thom encoding* (the sign vector of all derivatives at a
root) determines the root. Immediate from `thom_convex`: full sign agreement at both roots would
freeze `p` at the value `0` on the whole (infinite) interval. -/
theorem thom_separation {p : R[X]} (hp : p ≠ 0) {a b : R} (hab : a < b)
    (ha : p.IsRoot a) (hb : p.IsRoot b) :
    ∃ k, 1 ≤ k ∧ k ≤ p.natDegree ∧
      sgn ((derivative^[k] p).eval a) ≠ sgn ((derivative^[k] p).eval b) := by
  by_contra hcon
  push Not at hcon
  have hall : ∀ k, k ≤ p.natDegree →
      sgn ((derivative^[k] p).eval a) = sgn ((derivative^[k] p).eval b) := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · simp only [Function.iterate_zero, id]
      rw [ha.eq_zero, hb.eq_zero]
    · exact hcon k hk1 hk
  have hconv := thom_convex hab.le hall
  have hroots : ∀ z ∈ Set.Icc a b, p.IsRoot z := by
    intro z hz
    have := hconv z hz.1 hz.2 0 (Nat.zero_le _)
    simp only [Function.iterate_zero, id] at this
    rw [ha.eq_zero, sgn_zero'] at this
    exact eq_zero_of_sgn_eq_zero this
  exact hp (p.eq_zero_of_infinite_isRoot
    (Set.Infinite.mono hroots (Set.infinite_coe_iff.mp ⟨(Set.Icc.infinite hab).1⟩)))

end Sturm
