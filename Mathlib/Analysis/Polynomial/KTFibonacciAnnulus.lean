/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.Polynomial.KFibonacciAnnulus

/-!
# The `(k, t)`-Fibonacci annulus for the zeros of a polynomial

The `(k, t)`-Fibonacci sequence is defined by `F 0 = 0`, `F 1 = 1` and
`F (n + 2) = k * F (n + 1) + t * F n`; the `k`-Fibonacci sequence is the case `t = 1`,
the Pell numbers the case `(k, t) = (2, 1)`, the Jacobsthal numbers the case
`(k, t) = (1, 2)`, and the Mersenne numbers `2 ^ n - 1` the case `(k, t) = (3, -2)`.

This sequence is *precisely* the fundamental Lucas solution `U(k, t)` of
`Mathlib/Analysis/Polynomial/KFibonacciAnnulus.lean`, so the binomial identity, the
divisibility law and the annulus theorems all hold for it verbatim — this file records the
`(k, t)`-facing statements as instantiations, together with the results whose *statements*
are genuinely new at this level of generality:

* `Polynomial.isRoot_mem_ktFib_annulus_four`: the analogue of Corollary 1.3 of Kaur's
  `k`-Fibonacci paper, whose radii now involve `(t * (k ^ 2 + t)) ^ (n - ℓ)` and
  `(k ^ 3 + 2 * k * t) ^ ℓ` — the factor `t` is invisible at `t = 1`.
* `Polynomial.isRoot_mem_pell_annulus`: the Pell-number annulus, with radii built from
  `5 ^ (n - ℓ) * 12 ^ ℓ` (`(k, t) = (2, 1)`).
* `Polynomial.isRoot_mem_jacobsthal_annulus`: the Jacobsthal-number annulus, with radii
  built from `6 ^ (n - ℓ) * 5 ^ ℓ` (`(k, t) = (1, 2)`).
* `Int.sum_choose_mul_mersenne`: the composition identity for the Mersenne numbers
  `2 ^ n - 1`, an instance with `t = -2 < 0` — a regime the annulus cannot reach but the
  identity covers.

As everywhere in this development, no new definition is introduced: the sequence is carried
by the hypotheses `F 0 = 0`, `F 1 = 1` and the recurrence.
-/

@[expose] public section

open Finset

namespace Real

/-! ### The `(k, t)`-Fibonacci identity and small values -/

variable {k t : ℝ} {F : ℕ → ℝ}

section Recurrence

variable (hF0 : F 0 = 0) (hF1 : F 1 = 1)
  (hrec : ∀ n, F (n + 2) = k * F (n + 1) + t * F n)
include hF0 hF1 hrec

/-- **Theorem 1.1** for the `(k, t)`-Fibonacci sequence: the binomial identity
`∑ ℓ ≤ n, (n.choose ℓ) * (t * F m) ^ (n - ℓ) * F (m + 1) ^ ℓ * F ℓ = F ((m + 1) * n)`.
The case `t = 1` is `Real.sum_choose_mul_kFib`.  No positivity of `k` or `t` is needed. -/
theorem sum_choose_mul_ktFib (m n : ℕ) :
    ∑ ℓ ∈ range (n + 1), (n.choose ℓ : ℝ) * (t * F m) ^ (n - ℓ) * F (m + 1) ^ ℓ * F ℓ
      = F ((m + 1) * n) :=
  LucasU.sum_choose_mul hF0 hF1 hrec m n

/-- The `(k, t)`-Fibonacci value `F 3 = k ^ 2 + t`. -/
theorem ktFib_three : F 3 = k ^ 2 + t :=
  lucas_three hF0 hF1 hrec

/-- The `(k, t)`-Fibonacci value `F 4 = k ^ 3 + 2 * k * t`. -/
theorem ktFib_four : F 4 = k ^ 3 + 2 * k * t :=
  lucas_four hF0 hF1 hrec

end Recurrence

end Real

/-- The composition identity for the **Mersenne numbers** `2 ^ n - 1`: the
`(k, t) = (3, -2)`-Fibonacci sequence over `ℤ`.  This lies in the regime `t < 0`, which the
annulus theorems cannot reach but the algebraic identity covers. -/
theorem Int.sum_choose_mul_mersenne (m n : ℕ) :
    ∑ ℓ ∈ range (n + 1),
        (n.choose ℓ : ℤ) * (-2 * (2 ^ m - 1)) ^ (n - ℓ) * (2 ^ (m + 1) - 1) ^ ℓ
          * (2 ^ ℓ - 1)
      = 2 ^ ((m + 1) * n) - 1 := by
  have h := LucasU.sum_choose_mul (R := ℤ) (p := 3) (q := -2)
    (F := fun j => 2 ^ j - 1) (by norm_num) (by norm_num) (fun j => by ring) m n
  simpa using h

namespace Polynomial

/-! ### The `(k, t)`-Fibonacci annuli -/

variable {K : Type*} [NormedRing K] [NormOneClass K] [NormMulClass K]

section KTFib

variable {p : K[X]} {k t : ℝ} {F : ℕ → ℝ}
variable (hF0 : F 0 = 0) (hF1 : F 1 = 1)
  (hrec : ∀ j, F (j + 2) = k * F (j + 1) + t * F j)
include hF0 hF1 hrec

/-- **Theorem 1.2** for the `(k, t)`-Fibonacci sequence: all zeros of `p` lie in the closed
annulus with the `(k, t)`-Fibonacci radii.  The case `t = 1` is
`Polynomial.isRoot_mem_kFib_annulus`. -/
theorem isRoot_mem_ktFib_annulus (hk : 0 < k) (ht : 0 < t)
    {m : ℕ} (hm : 1 ≤ m) (hdeg : 1 ≤ p.natDegree)
    (ha : ∀ ℓ ∈ Icc 1 p.natDegree, p.coeff ℓ ≠ 0) {z : K} (hz : p.IsRoot z) :
    (Icc 1 p.natDegree).inf' (Finset.nonempty_Icc.2 hdeg) (fun ℓ =>
        ((p.natDegree.choose ℓ : ℝ) * (t * F m) ^ (p.natDegree - ℓ) * F (m + 1) ^ ℓ * F ℓ
            / F ((m + 1) * p.natDegree)
            * (‖p.coeff 0‖ / ‖p.coeff ℓ‖)) ^ ((ℓ : ℝ)⁻¹)) ≤ ‖z‖ ∧
      ‖z‖ ≤ (Icc 1 p.natDegree).sup' (Finset.nonempty_Icc.2 hdeg) fun ℓ =>
        (F ((m + 1) * p.natDegree)
            / ((p.natDegree.choose ℓ : ℝ) * (t * F m) ^ (p.natDegree - ℓ)
                * F (m + 1) ^ ℓ * F ℓ)
            * (‖p.coeff (p.natDegree - ℓ)‖ / ‖p.leadingCoeff‖)) ^ ((ℓ : ℝ)⁻¹) :=
  isRoot_mem_lucas_annulus hF0 hF1 hrec hk ht hm hdeg ha hz

/-- The analogue for `(k, t)`-Fibonacci sequences of Corollary 1.3 of Kaur's `k`-Fibonacci
paper: the case `m = 4` (paper indexing), where `F 3 = k ^ 2 + t` and
`F 4 = k ^ 3 + 2 * k * t`.  The radii involve `(t * (k ^ 2 + t)) ^ (n - ℓ)`, in which the
factor `t` is invisible at `t = 1`. -/
theorem isRoot_mem_ktFib_annulus_four (hk : 0 < k) (ht : 0 < t) (hdeg : 1 ≤ p.natDegree)
    (ha : ∀ ℓ ∈ Icc 1 p.natDegree, p.coeff ℓ ≠ 0) {z : K} (hz : p.IsRoot z) :
    (Icc 1 p.natDegree).inf' (Finset.nonempty_Icc.2 hdeg) (fun ℓ =>
        ((p.natDegree.choose ℓ : ℝ) * (t * (k ^ 2 + t)) ^ (p.natDegree - ℓ)
            * (k ^ 3 + 2 * k * t) ^ ℓ * F ℓ / F (4 * p.natDegree)
            * (‖p.coeff 0‖ / ‖p.coeff ℓ‖)) ^ ((ℓ : ℝ)⁻¹)) ≤ ‖z‖ ∧
      ‖z‖ ≤ (Icc 1 p.natDegree).sup' (Finset.nonempty_Icc.2 hdeg) fun ℓ =>
        (F (4 * p.natDegree)
            / ((p.natDegree.choose ℓ : ℝ) * (t * (k ^ 2 + t)) ^ (p.natDegree - ℓ)
                * (k ^ 3 + 2 * k * t) ^ ℓ * F ℓ)
            * (‖p.coeff (p.natDegree - ℓ)‖ / ‖p.leadingCoeff‖)) ^ ((ℓ : ℝ)⁻¹) := by
  have h := isRoot_mem_ktFib_annulus hF0 hF1 hrec hk ht (m := 3) (by norm_num) hdeg ha hz
  simpa only [Real.ktFib_three hF0 hF1 hrec, Real.ktFib_four hF0 hF1 hrec,
    show (3 : ℕ) + 1 = 4 from rfl] using h

end KTFib

/-- The **Pell-number annulus**: the case `(k, t) = (2, 1)` and `m = 4` (paper indexing),
where `F 3 = 5` and `F 4 = 12` are Pell numbers. -/
theorem isRoot_mem_pell_annulus {p : K[X]} {F : ℕ → ℝ}
    (hF0 : F 0 = 0) (hF1 : F 1 = 1) (hrec : ∀ j, F (j + 2) = 2 * F (j + 1) + F j)
    (hdeg : 1 ≤ p.natDegree)
    (ha : ∀ ℓ ∈ Icc 1 p.natDegree, p.coeff ℓ ≠ 0) {z : K} (hz : p.IsRoot z) :
    (Icc 1 p.natDegree).inf' (Finset.nonempty_Icc.2 hdeg) (fun ℓ =>
        ((p.natDegree.choose ℓ : ℝ) * 5 ^ (p.natDegree - ℓ) * 12 ^ ℓ * F ℓ
            / F (4 * p.natDegree)
            * (‖p.coeff 0‖ / ‖p.coeff ℓ‖)) ^ ((ℓ : ℝ)⁻¹)) ≤ ‖z‖ ∧
      ‖z‖ ≤ (Icc 1 p.natDegree).sup' (Finset.nonempty_Icc.2 hdeg) fun ℓ =>
        (F (4 * p.natDegree)
            / ((p.natDegree.choose ℓ : ℝ) * 5 ^ (p.natDegree - ℓ) * 12 ^ ℓ * F ℓ)
            * (‖p.coeff (p.natDegree - ℓ)‖ / ‖p.leadingCoeff‖)) ^ ((ℓ : ℝ)⁻¹) := by
  have h := isRoot_mem_ktFib_annulus_four (k := 2) (t := 1) hF0 hF1
    (fun j => by rw [hrec j]; ring) two_pos one_pos hdeg ha hz
  simpa only [show (1 : ℝ) * ((2 : ℝ) ^ 2 + 1) = 5 by norm_num,
    show (2 : ℝ) ^ 3 + 2 * 2 * 1 = 12 by norm_num] using h

/-- The **Jacobsthal-number annulus**: the case `(k, t) = (1, 2)` and `m = 4` (paper
indexing), where `F 3 = 3` and `F 4 = 5` are Jacobsthal numbers and `t * F 3 = 6`. -/
theorem isRoot_mem_jacobsthal_annulus {p : K[X]} {F : ℕ → ℝ}
    (hF0 : F 0 = 0) (hF1 : F 1 = 1) (hrec : ∀ j, F (j + 2) = F (j + 1) + 2 * F j)
    (hdeg : 1 ≤ p.natDegree)
    (ha : ∀ ℓ ∈ Icc 1 p.natDegree, p.coeff ℓ ≠ 0) {z : K} (hz : p.IsRoot z) :
    (Icc 1 p.natDegree).inf' (Finset.nonempty_Icc.2 hdeg) (fun ℓ =>
        ((p.natDegree.choose ℓ : ℝ) * 6 ^ (p.natDegree - ℓ) * 5 ^ ℓ * F ℓ
            / F (4 * p.natDegree)
            * (‖p.coeff 0‖ / ‖p.coeff ℓ‖)) ^ ((ℓ : ℝ)⁻¹)) ≤ ‖z‖ ∧
      ‖z‖ ≤ (Icc 1 p.natDegree).sup' (Finset.nonempty_Icc.2 hdeg) fun ℓ =>
        (F (4 * p.natDegree)
            / ((p.natDegree.choose ℓ : ℝ) * 6 ^ (p.natDegree - ℓ) * 5 ^ ℓ * F ℓ)
            * (‖p.coeff (p.natDegree - ℓ)‖ / ‖p.leadingCoeff‖)) ^ ((ℓ : ℝ)⁻¹) := by
  have h := isRoot_mem_ktFib_annulus_four (k := 1) (t := 2) hF0 hF1
    (fun j => by rw [hrec j]; ring) one_pos two_pos hdeg ha hz
  simpa only [show (2 : ℝ) * ((1 : ℝ) ^ 2 + 2) = 6 by norm_num,
    show (1 : ℝ) ^ 3 + 2 * 1 * 2 = 5 by norm_num] using h

end Polynomial
