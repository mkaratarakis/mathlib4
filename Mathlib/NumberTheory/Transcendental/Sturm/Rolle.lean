/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.Sturm.Transfer

/-!
# Rolle's theorem for polynomials over a real closed field

`rolle`: between two roots of a polynomial over a real closed field lies a root of its
derivative. The proof is purely algebraic (no analysis): reduce to *consecutive* roots
`a' < b'` (`exists_consecutive_roots`), factor out the multiplicities
`p = (X - a')^m (X - b')^n h` with `h` root-free — hence sign-constant
(`sgn_eval_eq_of_no_root_uIcc`) — on `[a', b']`, and compute

`p' = (X - a')^(m-1) (X - b')^(n-1) G`,  `G = m (X - b') h + n (X - a') h + (X - a')(X - b') h'`.

Then `G(a') = m (a' - b') h(a')` and `G(b') = n (b' - a') h(b')` have opposite signs, so `G` has a
root strictly between (`exists_isRoot_of_eval_mul_neg`, from the intermediate value property), and
that root kills `p'`.

This is the key ingredient for **Thom's lemma** (roots of a polynomial are separated by the signs
of its derivatives), which in turn powers the sign-sequence determination needed for
order-compatible root matching in the uniqueness of real closures.
-/

open Polynomial

namespace Sturm

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **A sign change locates a root strictly inside the interval**: if `f(u) f(v) < 0` then `f` has
a root in the open interval `(u, v)`. Immediate from the intermediate value property; the root is
interior because the endpoint values are nonzero. -/
theorem exists_isRoot_of_eval_mul_neg {f : R[X]} {u v : R} (huv : u < v)
    (hprod : f.eval u * f.eval v < 0) : ∃ c, u < c ∧ c < v ∧ f.IsRoot c := by
  have hu0 : f.eval u ≠ 0 := fun h => by rw [h, zero_mul] at hprod; exact lt_irrefl 0 hprod
  have hv0 : f.eval v ≠ 0 := fun h => by rw [h, mul_zero] at hprod; exact lt_irrefl 0 hprod
  rcases mul_neg_iff.mp hprod with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · obtain ⟨z, hz, hz0⟩ := IsRealClosed.intermediate_value_property huv.le hu.le hv.le
    exact ⟨z, lt_of_le_of_ne hz.1 (fun h => hu0 (by rw [h]; exact hz0)),
      lt_of_le_of_ne hz.2 (fun h => hv0 (by rw [← h]; exact hz0)), hz0⟩
  · obtain ⟨z, hz, hz0⟩ := IsRealClosed.intermediate_value_property (f := -f) huv.le
      (by simpa using hu.le) (by simpa using hv.le)
    rw [eval_neg, neg_eq_zero] at hz0
    exact ⟨z, lt_of_le_of_ne hz.1 (fun h => hu0 (by rw [h]; exact hz0)),
      lt_of_le_of_ne hz.2 (fun h => hv0 (by rw [← h]; exact hz0)), hz0⟩

omit [IsStrictOrderedRing R] [IsRealClosed R] in
/-- Between any two roots of a nonzero polynomial there is a pair of **consecutive** roots: roots
`a' < b'` within `[a, b]` with no root strictly between them. -/
theorem exists_consecutive_roots {p : R[X]} (hp : p ≠ 0) {a b : R} (hab : a < b)
    (ha : p.IsRoot a) (hb : p.IsRoot b) :
    ∃ a' b', a ≤ a' ∧ a' < b' ∧ b' ≤ b ∧ p.IsRoot a' ∧ p.IsRoot b' ∧
      ∀ z, a' < z → z < b' → ¬ p.IsRoot z := by
  set S₂ := p.roots.toFinset.filter (fun z => a < z ∧ z ≤ b) with hS₂
  have h₂ : S₂.Nonempty :=
    ⟨b, Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr (mem_roots'.mpr ⟨hp, hb⟩),
      hab, le_refl b⟩⟩
  set b' := S₂.min' h₂ with hb'def
  have hb'mem := Finset.mem_filter.mp (S₂.min'_mem h₂)
  have hab' : a < b' := hb'mem.2.1
  set S₁ := p.roots.toFinset.filter (fun z => a ≤ z ∧ z < b') with hS₁
  have h₁ : S₁.Nonempty :=
    ⟨a, Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr (mem_roots'.mpr ⟨hp, ha⟩),
      le_refl a, hab'⟩⟩
  set a' := S₁.max' h₁ with ha'def
  have ha'mem := Finset.mem_filter.mp (S₁.max'_mem h₁)
  refine ⟨a', b', ha'mem.2.1, ha'mem.2.2, hb'mem.2.2,
    (mem_roots'.mp (Multiset.mem_toFinset.mp ha'mem.1)).2,
    (mem_roots'.mp (Multiset.mem_toFinset.mp hb'mem.1)).2, fun z hz₁ hz₂ hzroot => ?_⟩
  -- a root strictly between `a'` and `b'` would beat the minimality of `b'`
  have hza : a < z := lt_of_le_of_lt ha'mem.2.1 hz₁
  have hzb : z ≤ b := le_of_lt (lt_of_lt_of_le hz₂ hb'mem.2.2)
  have hzS₂ : z ∈ S₂ := Finset.mem_filter.mpr
    ⟨Multiset.mem_toFinset.mpr (mem_roots'.mpr ⟨hp, hzroot⟩), hza, hzb⟩
  exact absurd (S₂.min'_le z hzS₂) (not_le.mpr hz₂)

omit [IsRealClosed R] in
/-- Same-sign nonzero values have positive product. -/
private theorem mul_pos_of_sgn_eq {x y : R} (h : sgn x = sgn y) (hx : x ≠ 0) : 0 < x * y := by
  rcases lt_trichotomy x 0 with hx' | hx' | hx'
  · have hy : y < 0 := by
      by_contra hy
      rcases eq_or_lt_of_le (not_lt.mp hy) with hy' | hy'
      · unfold sgn at h
        rw [if_neg (asymm hx'), if_neg hx, if_neg (by rw [← hy']; exact lt_irrefl 0),
          if_pos hy'.symm] at h
        norm_num at h
      · unfold sgn at h
        rw [if_neg (asymm hx'), if_neg hx, if_pos hy'] at h
        norm_num at h
    exact mul_pos_of_neg_of_neg hx' hy
  · exact absurd hx' hx
  · have hy : 0 < y := by
      by_contra hy
      rcases eq_or_lt_of_le (not_lt.mp hy) with hy' | hy'
      · unfold sgn at h
        rw [if_pos hx', if_neg (by rw [hy']; exact lt_irrefl 0), if_pos hy'] at h
        norm_num at h
      · unfold sgn at h
        rw [if_pos hx', if_neg (asymm hy'), if_neg hy'.ne] at h
        norm_num at h
    exact mul_pos hx' hy

/-- **Rolle's theorem for polynomials over a real closed field**: between two roots of `p` there
is a root of `p'`. Purely algebraic — multiplicity factorization at a pair of consecutive roots
plus the intermediate value property. -/
theorem rolle {p : R[X]} {a b : R} (hab : a < b) (ha : p.IsRoot a) (hb : p.IsRoot b) :
    ∃ c, a < c ∧ c < b ∧ p.derivative.IsRoot c := by
  rcases eq_or_ne p 0 with rfl | hp
  · exact ⟨(a + b) / 2, left_lt_add_div_two.mpr hab, add_div_two_lt_right.mpr hab, by simp⟩
  obtain ⟨a', b', haa', ha'b', hb'b, ha', hb', hcons⟩ :=
    exists_consecutive_roots hp hab ha hb
  -- factor out the root `a'`
  obtain ⟨q, hpq, hqa⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp a'
  have hqa' : q.eval a' ≠ 0 := fun h => hqa (dvd_iff_isRoot.mpr h)
  have hq0 : q ≠ 0 := fun h => hp (by rw [hpq, h, mul_zero])
  -- `b'` is a root of `q`
  have hqb' : q.IsRoot b' := by
    have := ha'b'.ne'
    have hpb' := hb'
    rw [IsRoot, hpq, eval_mul, eval_pow, eval_sub, eval_X, eval_C, mul_eq_zero] at hpb'
    rcases hpb' with h | h
    · exact absurd (pow_eq_zero_iff (n := p.rootMultiplicity a')
        (by
          have := (rootMultiplicity_pos hp).mpr ha'
          omega) |>.mp h) (sub_ne_zero.mpr ha'b'.ne')
    · exact h
  -- factor out the root `b'`
  obtain ⟨h, hqh, hhb⟩ := q.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hq0 b'
  have hhb' : h.eval b' ≠ 0 := fun hh => hhb (dvd_iff_isRoot.mpr hh)
  have hha' : h.eval a' ≠ 0 := by
    intro hh
    apply hqa'
    rw [hqh, eval_mul, hh, mul_zero]
  -- positive multiplicities
  obtain ⟨m₀, hm₀⟩ : ∃ m₀, p.rootMultiplicity a' = m₀ + 1 :=
    ⟨p.rootMultiplicity a' - 1, by have := (rootMultiplicity_pos hp).mpr ha'; omega⟩
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, q.rootMultiplicity b' = n₀ + 1 :=
    ⟨q.rootMultiplicity b' - 1, by have := (rootMultiplicity_pos hq0).mpr hqb'; omega⟩
  have hpfact : p = (X - C a') ^ (m₀ + 1) * ((X - C b') ^ (n₀ + 1) * h) := by
    rw [hpq, hqh, hm₀, hn₀]
  -- `h` divides `p`, so `h` has no roots on `[a', b']`
  have hhnoroot : ∀ z ∈ Set.uIcc a' b', ¬ h.IsRoot z := by
    intro z hz hzroot
    have hzroot' : p.IsRoot z := by
      rw [IsRoot, hpfact, eval_mul, eval_mul, hzroot, mul_zero, mul_zero]
    rw [Set.uIcc_of_le ha'b'.le] at hz
    rcases eq_or_lt_of_le hz.1 with h₁ | h₁
    · exact hha' (h₁ ▸ hzroot)
    rcases eq_or_lt_of_le hz.2 with h₂ | h₂
    · exact hhb' (h₂ ▸ hzroot)
    exact hcons z h₁ h₂ hzroot'
  -- the cofactor `G` of `p'`
  set G : R[X] := C ((m₀ + 1 : ℕ) : R) * (X - C b') * h
      + C ((n₀ + 1 : ℕ) : R) * (X - C a') * h
      + (X - C a') * (X - C b') * derivative h with hG
  have hd : derivative p = (X - C a') ^ m₀ * (X - C b') ^ n₀ * G := by
    rw [hpfact]
    simp only [derivative_mul, derivative_pow, derivative_X_sub_C, Nat.add_sub_cancel, hG]
    ring
  -- sign of `G` at the endpoints
  have hGa : G.eval a' = ((m₀ + 1 : ℕ) : R) * (a' - b') * h.eval a' := by
    simp [hG]
  have hGb : G.eval b' = ((n₀ + 1 : ℕ) : R) * (b' - a') * h.eval b' := by
    simp [hG]
  have hsgn : sgn (h.eval a') = sgn (h.eval b') := sgn_eval_eq_of_no_root_uIcc hhnoroot
  have hhpos : 0 < h.eval a' * h.eval b' := mul_pos_of_sgn_eq hsgn hha'
  have hprod : G.eval a' * G.eval b' < 0 := by
    have hexp : G.eval a' * G.eval b'
        = -(((m₀ + 1 : ℕ) : R) * ((n₀ + 1 : ℕ) : R) * (h.eval a' * h.eval b')
            * (b' - a') ^ 2) := by
      rw [hGa, hGb]; ring
    rw [hexp, neg_lt, neg_zero]
    have hm : (0 : R) < ((m₀ + 1 : ℕ) : R) := by exact_mod_cast Nat.succ_pos m₀
    have hn : (0 : R) < ((n₀ + 1 : ℕ) : R) := by exact_mod_cast Nat.succ_pos n₀
    exact mul_pos (mul_pos (mul_pos hm hn) hhpos) (pow_pos (sub_pos.mpr ha'b') 2)
  -- a root of `G` strictly between the consecutive roots kills `p'`
  obtain ⟨c, hc₁, hc₂, hcroot⟩ := exists_isRoot_of_eval_mul_neg ha'b' hprod
  refine ⟨c, lt_of_le_of_lt haa' hc₁, lt_of_lt_of_le hc₂ hb'b, ?_⟩
  rw [IsRoot, hd, eval_mul, hcroot, mul_zero]

end Sturm
