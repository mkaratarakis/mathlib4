/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Monovary
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# The weighted Lagrange identity and converse Cauchy–Schwarz inequalities

For weights `w i` and families `a i`, `b i` indexed by a finset `s`, write
`A = ∑ i ∈ s, w i * a i ^ 2`, `B = ∑ i ∈ s, w i * b i ^ 2`, `C = ∑ i ∈ s, w i * (a i * b i)` and
`W = ∑ i ∈ s, w i`. For nonnegative weights, `A * B - C ^ 2` is the Gram determinant of the
vectors `(√(w i) * a i)ᵢ` and `(√(w i) * b i)ᵢ`, and the Cauchy–Schwarz inequality says that it is
nonnegative (`Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul`). This file proves upper bounds for it.

## Main results

* `Finset.two_mul_sum_mul_sq_mul_sum_mul_sq_sub_sq`: the weighted Lagrange identity
  `2 * (A * B - C ^ 2) = ∑ i ∈ s, ∑ j ∈ s, w i * w j * (a i * b j - a j * b i) ^ 2`, in any
  commutative ring.
* `Finset.diaz_metcalf`: the **Diaz–Metcalf inequality**: if `r * b i ≤ a i ≤ R * b i`, then
  `A + r * R * B ≤ (r + R) * C`.
* `Finset.polya_szego`: the **Pólya–Szegő inequality**: under the same hypotheses,
  `4 * (r * R) * (A * B) ≤ (r + R) ^ 2 * C ^ 2`.
* `Finset.four_mul_sum_mul_sum_mul_sq_sub_sq_le`: **Popoviciu's inequality** for weighted finite
  sums: if `c i ∈ [lo, hi]`, then `4 * (W * ∑ w c ^ 2 - (∑ w c) ^ 2) ≤ W ^ 2 * (hi - lo) ^ 2`.
* `Finset.four_mul_sum_mul_sq_mul_sum_mul_sq_sub_sq_le_of_sq_le`: if every
  `(a i * b j - a j * b i) ^ 2` is at most `(c i - c j) ^ 2` for some `c` with values in
  `[lo, hi]`, then `4 * (A * B - C ^ 2) ≤ W ^ 2 * (hi - lo) ^ 2`.
* `Finset.four_mul_sum_mul_sq_mul_sum_mul_sq_sub_sq_le_of_monovaryOn`,
  `Finset.four_mul_sum_mul_sq_mul_sum_mul_sq_sub_sq_le_of_mul_add_mul_le`: the **Ozeki**-type
  bound `4 * (A * B - C ^ 2) ≤ W ^ 2 * (M₁ * M₂ - m₁ * m₂) ^ 2` for `a i ∈ [m₁, M₁]`,
  `b i ∈ [m₂, M₂]` when `a` and `b` monovary, or when the points `(a i, b i)` lie below the line
  through `(m₁, M₂)` and `(M₁, m₂)`. For arbitrary families the bound fails, see
  `Counterexamples/Ozeki.lean`.
* `div_mul_le_and_le_div_mul`: box bounds `a ∈ [m₁, M₁]`, `b ∈ [m₂, M₂]` give the ratio bounds
  `m₁ / M₂ * b ≤ a ≤ M₁ / m₂ * b` used in the Diaz–Metcalf and Pólya–Szegő inequalities.

All inequalities except the last two hold in any linearly ordered commutative ring; the last two
hold in any linearly ordered field.

## References

* [T. Popoviciu, *Sur les équations algébriques ayant toutes leurs racines réelles*]
  [popoviciu_1935]
* [N. Ozeki, *On the estimation of the inequalities by the maximum, or minimum values*]
  [ozeki_1968]
* [J. B. Diaz and F. T. Metcalf, *Stronger forms of a class of inequalities of G. Pólya–G. Szegő,
  and L. V. Kantorovich*][diaz_metcalf_1963]
* [G. Pólya and G. Szegő, *Aufgaben und Lehrsätze aus der Analysis. Band I*][polya_szego_1925]
-/

public section

variable {ι α K : Type*}

namespace Finset

section CommRing

variable [CommRing α]

/-- **Weighted Lagrange identity**: twice `(∑ w a ^ 2) * (∑ w b ^ 2) - (∑ w a b) ^ 2` equals
`∑ i ∈ s, ∑ j ∈ s, w i * w j * (a i * b j - a j * b i) ^ 2`. -/
theorem two_mul_sum_mul_sq_mul_sum_mul_sq_sub_sq (s : Finset ι) (w a b : ι → α) :
    2 * ((∑ i ∈ s, w i * a i ^ 2) * (∑ i ∈ s, w i * b i ^ 2) -
        (∑ i ∈ s, w i * (a i * b i)) ^ 2) =
      ∑ i ∈ s, ∑ j ∈ s, w i * w j * (a i * b j - a j * b i) ^ 2 := by
  have h (i j : ι) : w i * w j * (a i * b j - a j * b i) ^ 2 =
      w i * a i ^ 2 * (w j * b j ^ 2) + w j * a j ^ 2 * (w i * b i ^ 2) -
        2 * (w i * (a i * b i) * (w j * (a j * b j))) := by ring
  simp only [h, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul]
  ring

end CommRing

section OrderedCommRing

variable [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] {s : Finset ι} {w a b c : ι → α}
  {lo hi r R m₁ M₁ m₂ M₂ : α}

/-- **Diaz–Metcalf inequality**: if `w i ≥ 0` and `r * b i ≤ a i ≤ R * b i`, then
`∑ w a ^ 2 + r * R * ∑ w b ^ 2 ≤ (r + R) * ∑ w a b`. No sign conditions on `r`, `R` are needed.
-/
theorem diaz_metcalf (hw : ∀ i ∈ s, 0 ≤ w i) (hr : ∀ i ∈ s, r * b i ≤ a i)
    (hR : ∀ i ∈ s, a i ≤ R * b i) :
    ∑ i ∈ s, w i * a i ^ 2 + r * R * ∑ i ∈ s, w i * b i ^ 2 ≤
      (r + R) * ∑ i ∈ s, w i * (a i * b i) := by
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun i hi ↦ ?_
  have := mul_nonneg (hw i hi) (mul_nonneg (sub_nonneg.2 (hr i hi)) (sub_nonneg.2 (hR i hi)))
  linarith

/-- **Pólya–Szegő inequality**: if `w i ≥ 0` and `r * b i ≤ a i ≤ R * b i`, then
`4 * (r * R) * ((∑ w a ^ 2) * (∑ w b ^ 2)) ≤ (r + R) ^ 2 * (∑ w a b) ^ 2`. No sign conditions on
`r`, `R` are needed; for `0 < r * R` this is
`(∑ w a ^ 2) * (∑ w b ^ 2) ≤ (r + R) ^ 2 / (4 * r * R) * (∑ w a b) ^ 2`. -/
theorem polya_szego (hw : ∀ i ∈ s, 0 ≤ w i) (hr : ∀ i ∈ s, r * b i ≤ a i)
    (hR : ∀ i ∈ s, a i ≤ R * b i) :
    4 * (r * R) * ((∑ i ∈ s, w i * a i ^ 2) * ∑ i ∈ s, w i * b i ^ 2) ≤
      (r + R) ^ 2 * (∑ i ∈ s, w i * (a i * b i)) ^ 2 := by
  have hA : 0 ≤ ∑ i ∈ s, w i * a i ^ 2 := sum_nonneg fun i hi ↦ by have := hw i hi; positivity
  have hB : 0 ≤ ∑ i ∈ s, w i * b i ^ 2 := sum_nonneg fun i hi ↦ by have := hw i hi; positivity
  obtain hrR | hrR := lt_or_ge (r * R) 0
  · -- the left-hand side is nonpositive
    exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) (mul_nonneg hA hB)).trans (by positivity)
  have h1 := pow_le_pow_left₀ (add_nonneg hA (mul_nonneg hrR hB)) (diaz_metcalf hw hr hR) 2
  nlinarith [sq_nonneg (∑ i ∈ s, w i * a i ^ 2 - r * R * ∑ i ∈ s, w i * b i ^ 2)]

/-- **Popoviciu's inequality** for weighted finite sums: if `w i ≥ 0` and `c i ∈ [lo, hi]`, then
`4 * ((∑ w) * (∑ w c ^ 2) - (∑ w c) ^ 2) ≤ (∑ w) ^ 2 * (hi - lo) ^ 2`. -/
theorem four_mul_sum_mul_sum_mul_sq_sub_sq_le (hw : ∀ i ∈ s, 0 ≤ w i)
    (hc : ∀ i ∈ s, c i ∈ Set.Icc lo hi) :
    4 * ((∑ i ∈ s, w i) * ∑ i ∈ s, w i * c i ^ 2 - (∑ i ∈ s, w i * c i) ^ 2) ≤
      (∑ i ∈ s, w i) ^ 2 * (hi - lo) ^ 2 := by
  have hpos : 0 ≤ ∑ i ∈ s, w i * ((c i - lo) * (hi - c i)) :=
    sum_nonneg fun i h ↦ mul_nonneg (hw i h)
      (mul_nonneg (sub_nonneg.2 (hc i h).1) (sub_nonneg.2 (hc i h).2))
  have hexp : ∑ i ∈ s, w i * ((c i - lo) * (hi - c i)) =
      (lo + hi) * ∑ i ∈ s, w i * c i - ∑ i ∈ s, w i * c i ^ 2 - lo * hi * ∑ i ∈ s, w i := by
    simp only [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ ↦ by ring
  have hQ : ∑ i ∈ s, w i * c i ^ 2 ≤
      (lo + hi) * ∑ i ∈ s, w i * c i - lo * hi * ∑ i ∈ s, w i := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hQ (sum_nonneg hw),
    sq_nonneg (2 * ∑ i ∈ s, w i * c i - (∑ i ∈ s, w i) * (lo + hi))]

/-- **Lagrange–Popoviciu bound**: if `w i ≥ 0`, every Lagrange term `a i * b j - a j * b i` is
dominated by `c i - c j` in absolute value, and `c i ∈ [lo, hi]`, then
`4 * ((∑ w a ^ 2) * (∑ w b ^ 2) - (∑ w a b) ^ 2) ≤ (∑ w) ^ 2 * (hi - lo) ^ 2`. -/
theorem four_mul_sum_mul_sq_mul_sum_mul_sq_sub_sq_le_of_sq_le (hw : ∀ i ∈ s, 0 ≤ w i)
    (hc : ∀ i ∈ s, c i ∈ Set.Icc lo hi)
    (hdom : ∀ i ∈ s, ∀ j ∈ s, (a i * b j - a j * b i) ^ 2 ≤ (c i - c j) ^ 2) :
    4 * ((∑ i ∈ s, w i * a i ^ 2) * (∑ i ∈ s, w i * b i ^ 2) -
        (∑ i ∈ s, w i * (a i * b i)) ^ 2) ≤ (∑ i ∈ s, w i) ^ 2 * (hi - lo) ^ 2 := by
  have hab := two_mul_sum_mul_sq_mul_sum_mul_sq_sub_sq s w a b
  have hc1 := two_mul_sum_mul_sq_mul_sum_mul_sq_sub_sq s w c 1
  simp only [Pi.one_apply, mul_one, one_pow] at hc1
  have hle : ∑ i ∈ s, ∑ j ∈ s, w i * w j * (a i * b j - a j * b i) ^ 2 ≤
      ∑ i ∈ s, ∑ j ∈ s, w i * w j * (c i - c j) ^ 2 :=
    sum_le_sum fun i hi ↦ sum_le_sum fun j hj ↦
      mul_le_mul_of_nonneg_left (hdom i hi j hj) (mul_nonneg (hw i hi) (hw j hj))
  linarith [four_mul_sum_mul_sum_mul_sq_sub_sq_le hw hc]

/-- **Ozeki-type bound for monovarying families**: if `w i ≥ 0`, `0 ≤ m₁ ≤ a i ≤ M₁`,
`0 ≤ m₂ ≤ b i ≤ M₂` and `a`, `b` monovary on `s`, then
`4 * ((∑ w a ^ 2) * (∑ w b ^ 2) - (∑ w a b) ^ 2) ≤ (∑ w) ^ 2 * (M₁ * M₂ - m₁ * m₂) ^ 2`. -/
theorem four_mul_sum_mul_sq_mul_sum_mul_sq_sub_sq_le_of_monovaryOn (hw : ∀ i ∈ s, 0 ≤ w i)
    (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂) (ha : ∀ i ∈ s, a i ∈ Set.Icc m₁ M₁)
    (hb : ∀ i ∈ s, b i ∈ Set.Icc m₂ M₂) (hab : MonovaryOn a b s) :
    4 * ((∑ i ∈ s, w i * a i ^ 2) * (∑ i ∈ s, w i * b i ^ 2) -
        (∑ i ∈ s, w i * (a i * b i)) ^ 2) ≤ (∑ i ∈ s, w i) ^ 2 * (M₁ * M₂ - m₁ * m₂) ^ 2 := by
  refine four_mul_sum_mul_sq_mul_sum_mul_sq_sub_sq_le_of_sq_le (c := fun i ↦ a i * b i) hw
    (fun i hi ↦ ⟨mul_le_mul (ha i hi).1 (hb i hi).1 hm₂ (hm₁.trans (ha i hi).1),
      mul_le_mul (ha i hi).2 (hb i hi).2 (hm₂.trans (hb i hi).1)
        (hm₁.trans ((ha i hi).1.trans (ha i hi).2))⟩) fun i hi j hj ↦ ?_
  have := mul_nonneg (mul_nonneg (add_nonneg (hm₁.trans (ha i hi).1) (hm₁.trans (ha j hj).1))
    (add_nonneg (hm₂.trans (hb i hi).1) (hm₂.trans (hb j hj).1)))
    (monovaryOn_iff_forall_mul_nonneg.1 hab hj hi)
  linear_combination this

end OrderedCommRing

section OrderedField

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s : Finset ι} {w a b : ι → K}
  {m₁ M₁ m₂ M₂ : K}

/-- **Ozeki-type bound below the anti-diagonal**: if `w i ≥ 0`, `0 < m₁ ≤ a i ≤ M₁`,
`0 < m₂ ≤ b i ≤ M₂` and every point `(a i, b i)` lies on or below the line through `(m₁, M₂)` and
`(M₁, m₂)`, then
`4 * ((∑ w a ^ 2) * (∑ w b ^ 2) - (∑ w a b) ^ 2) ≤ (∑ w) ^ 2 * (M₁ * M₂ - m₁ * m₂) ^ 2`. -/
theorem four_mul_sum_mul_sq_mul_sum_mul_sq_sub_sq_le_of_mul_add_mul_le (hw : ∀ i ∈ s, 0 ≤ w i)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (ha : ∀ i ∈ s, a i ∈ Set.Icc m₁ M₁)
    (hb : ∀ i ∈ s, b i ∈ Set.Icc m₂ M₂)
    (hline : ∀ i ∈ s, (M₂ - m₂) * a i + (M₁ - m₁) * b i ≤ M₁ * M₂ - m₁ * m₂) :
    4 * ((∑ i ∈ s, w i * a i ^ 2) * (∑ i ∈ s, w i * b i ^ 2) -
        (∑ i ∈ s, w i * (a i * b i)) ^ 2) ≤ (∑ i ∈ s, w i) ^ 2 * (M₁ * M₂ - m₁ * m₂) ^ 2 := by
  -- We apply `Finset.four_mul_sum_mul_sq_mul_sum_mul_sq_sub_sq_le_of_sq_le` to the projective
  -- coordinate `c i = (m₁ * b i - M₂ * a i) * D / N i`, where `D = M₁ * M₂ - m₁ * m₂` and
  -- `N i = (M₂ - m₂) * a i + (M₁ - m₁) * b i`; it takes values in `[-D, 0]`.
  obtain rfl | ⟨i₀, hi₀⟩ := s.eq_empty_or_nonempty
  · simp
  have h₁ : m₁ ≤ M₁ := (ha i₀ hi₀).1.trans (ha i₀ hi₀).2
  have h₂ : m₂ ≤ M₂ := (hb i₀ hi₀).1.trans (hb i₀ hi₀).2
  obtain hD0 | hD0 : M₁ * M₂ - m₁ * m₂ = 0 ∨ 0 < M₁ * M₂ - m₁ * m₂ := by
    refine (eq_or_lt_of_le ?_).imp Eq.symm id; nlinarith
  · -- degenerate box: `a` and `b` are constant on `s`
    have hM₁ : M₁ = m₁ := by nlinarith
    refine four_mul_sum_mul_sq_mul_sum_mul_sq_sub_sq_le_of_monovaryOn hw hm₁.le hm₂.le ha hb ?_
    refine monovaryOn_iff_forall_mul_nonneg.2 fun i hi j hj ↦ ?_
    have hai := ha i hi; have haj := ha j hj
    rw [Set.mem_Icc, hM₁] at hai haj
    rw [le_antisymm hai.2 hai.1, le_antisymm haj.2 haj.1, sub_self, zero_mul]
  have hN : ∀ i ∈ s, 0 < (M₂ - m₂) * a i + (M₁ - m₁) * b i := fun i hi ↦ by
    have hai := hm₁.trans_le (ha i hi).1
    have hbi := hm₂.trans_le (hb i hi).1
    rcases (sub_nonneg.2 h₂).eq_or_lt with h | h
    · rw [← h, zero_mul, zero_add]
      exact mul_pos (by nlinarith) hbi
    · nlinarith [mul_pos h hai, mul_nonneg (sub_nonneg.2 h₁) hbi.le]
  refine (four_mul_sum_mul_sq_mul_sum_mul_sq_sub_sq_le_of_sq_le
    (c := fun i ↦ (m₁ * b i - M₂ * a i) * (M₁ * M₂ - m₁ * m₂) /
      ((M₂ - m₂) * a i + (M₁ - m₁) * b i)) (lo := -(M₁ * M₂ - m₁ * m₂)) (hi := 0) hw
    (fun i hi ↦ ⟨?_, ?_⟩) fun i hi j hj ↦ ?_).trans_eq (by ring)
  · rw [le_div_iff₀ (hN i hi)]
    nlinarith [mul_nonneg hD0.le (mul_nonneg (hm₁.le.trans h₁) (sub_nonneg.2 (hb i hi).1)),
      mul_nonneg hD0.le (mul_nonneg hm₂.le (sub_nonneg.2 (ha i hi).2))]
  · refine div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg ?_ hD0.le) (hN i hi).le
    nlinarith [(ha i hi).1, (hb i hi).2]
  · have hNi := hN i hi
    have hNj := hN j hj
    have e : (m₁ * b i - M₂ * a i) * (M₁ * M₂ - m₁ * m₂) / ((M₂ - m₂) * a i + (M₁ - m₁) * b i) -
          (m₁ * b j - M₂ * a j) * (M₁ * M₂ - m₁ * m₂) / ((M₂ - m₂) * a j + (M₁ - m₁) * b j) =
          -((M₁ * M₂ - m₁ * m₂) ^ 2 / (((M₂ - m₂) * a i + (M₁ - m₁) * b i) *
            ((M₂ - m₂) * a j + (M₁ - m₁) * b j))) * (a i * b j - a j * b i) := by
      rw [div_sub_div _ _ hNi.ne' hNj.ne']
      ring
    rw [e, mul_pow, neg_sq]
    refine le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ ?_)
    rw [le_div_iff₀ (mul_pos hNi hNj), one_mul, sq]
    exact mul_le_mul (hline i hi) (hline j hj) hNj.le hD0.le

end OrderedField

end Finset

section OrderedField

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- If `0 ≤ m₁ ≤ a ≤ M₁` and `0 < m₂ ≤ b ≤ M₂`, then `m₁ / M₂ * b ≤ a ≤ M₁ / m₂ * b`. -/
theorem div_mul_le_and_le_div_mul {a b m₁ M₁ m₂ M₂ : K} (hm₁ : 0 ≤ m₁) (hm₂ : 0 < m₂)
    (ha : a ∈ Set.Icc m₁ M₁) (hb : b ∈ Set.Icc m₂ M₂) : m₁ / M₂ * b ≤ a ∧ a ≤ M₁ / m₂ * b := by
  have hM₂ : 0 < M₂ := hm₂.trans_le (hb.1.trans hb.2)
  have hM₁ : 0 ≤ M₁ := hm₁.trans (ha.1.trans ha.2)
  constructor
  · calc m₁ / M₂ * b ≤ m₁ / M₂ * M₂ := mul_le_mul_of_nonneg_left hb.2 (div_nonneg hm₁ hM₂.le)
      _ = m₁ := div_mul_cancel₀ _ hM₂.ne'
      _ ≤ a := ha.1
  · calc a ≤ M₁ := ha.2
      _ = M₁ / m₂ * m₂ := (div_mul_cancel₀ _ hm₂.ne').symm
      _ ≤ M₁ / m₂ * b := mul_le_mul_of_nonneg_left hb.1 (div_nonneg hM₁ hm₂.le)

end OrderedField
