/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FinCases

/-!
# A Lucas-sequence annulus for the zeros of a polynomial

This file formalises — and generalises — the results of

> S. Kaur, *k-Fibonacci annulus for polynomial zeros*.

No new definition is introduced anywhere: every statement takes an arbitrary sequence
`F : ℕ → R` together with the hypotheses `F 0 = 0`, `F 1 = 1` and the second-order recurrence
`F (n + 2) = p * F (n + 1) + q * F n` (a *Lucas sequence of the first kind* `U(p, q)`) as
explicit assumptions.  The paper's `k`-Fibonacci sequence is the case `q = 1`, and `Nat.fib`
is the case `p = q = 1`.  The hypotheses determine `F` uniquely (`LucasU.unique`), so this is
equivalent to — but strictly more flexible than — fixing a definition.

## Main results

* `LucasU.sum_choose_mul_solution` (generalising **Theorem 1.1** three times over): for any
  Lucas sequence `F` over any commutative semiring and **any** solution `G` of the same
  recurrence — arbitrary initial values, valued in an arbitrary `R`-module —
  `∑ ℓ ≤ n, (n.choose ℓ * (q * F m) ^ (n - ℓ) * F (m + 1) ^ ℓ) • G ℓ = G ((m + 1) * n)`.
  No positivity, no discriminant condition, no real square roots: the Binet formula of the
  paper is replaced by the binomial expansion of `(M ^ (m + 1)) ^ n` for the companion matrix
  `M = !![p, q; 1, 0]`, an operator identity evaluated on the solution space.
* `LucasU.sum_choose_mul`: the case `G := F`; `Real.sum_choose_mul_kFib` (**Theorem 1.1** of
  the paper) is the case `R = ℝ`, `q = 1`, and `Nat.sum_choose_mul_fib` the case `R = ℕ`,
  `p = q = 1` — a cast-free `Nat.fib` identity, not even expressible through the paper's
  real-analytic proof.
* `LucasU.dvd_of_dvd`: the fundamental Lucas divisibility law `a ∣ b → F a ∣ F b`
  (generalising `Nat.fib_dvd` to every Lucas sequence over every commutative semiring), an
  immediate consequence of the identity.
* `LucasU.solution_ext`: solutions are determined by their two initial values, so the
  hypothesis style is fully equivalent to a definition.
* `Polynomial.Chebyshev.sum_choose_mul_U`, `Polynomial.Chebyshev.U_sub_one_dvd`: the case
  `R[X]`, `p = 2 * X`, `q = -1` — composition identity and divisibility for Chebyshev
  polynomials of the second kind, in the `q < 0` regime the annulus cannot reach.
* `Polynomial.norm_le_of_isRoot_of_sum_weights`, `Polynomial.le_norm_of_isRoot_of_sum_weights`:
  the analytic core of Theorem 1.2 over any normed ring with multiplicative norm
  (`NormedRing` + `NormMulClass` + `NormOneClass` — e.g. `ℂ`, any normed field, `ℤ`), for an
  arbitrary weight sequence summing to `1`.
* `Polynomial.isRoot_mem_annulus_of_sum_weights`: the master closed-form annulus — **any**
  partition of unity `A` on `1 ≤ ℓ ≤ n` confines all zeros to
  `min (A ℓ * ‖a₀/aℓ‖)^(1/ℓ) ≤ ‖z‖ ≤ max ((1/A ℓ) * ‖a_{n-ℓ}/aₙ‖)^(1/ℓ)`.
* `Polynomial.isRoot_mem_lucas_annulus` (generalising **Theorem 1.2**): the Lucas-weight
  radii (`P > 0`, `Q > 0`), via `Finset.inf'`/`Finset.sup'` and real `rpow`.
* `Polynomial.isRoot_mem_kFib_annulus` (**Theorem 1.2** of the paper): the case `Q = 1`.
* `Polynomial.isRoot_mem_kFib_annulus_four` (**Corollary 1.3**, Bidkham–Shashahani): the case
  `m = 4` of the paper, with `F 3 = k ^ 2 + 1`, `F 4 = k ^ 3 + 2 * k`.
* `Polynomial.isRoot_mem_fib_annulus` (**Remark 1.4**, Diaz-Barrero): the classical case
  `k = 1`, phrased with `Nat.fib`.

## Implementation notes

Carrying the recurrence as hypotheses rather than as a definition loses nothing:
`LucasU.unique` shows two sequences satisfying the hypotheses agree, so every statement below
is interderivable with its analogue for any concrete definition; conversely the hypothesis
form applies directly to `Nat.fib` and friends with no glue.

The lower bound of Theorem 1.2 is proved directly on the constant coefficient rather than via
the reversed polynomial `zⁿ q(1/z)` used in the paper; this avoids any detour through
`Polynomial.reverse`.

The closed-form radii divide by `F (m - 1)` (in the paper's indexing), which vanishes for
`m = 1`; the hypothesis `1 ≤ m` below (after the index shift `m ↦ m - 1`) makes the paper's
implicit assumption `m ≥ 2` explicit.
-/

@[expose] public section

open Finset

namespace LucasU

/-! ### The Lucas-sequence identity over an arbitrary commutative semiring -/

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] {p q : R} {F : ℕ → R}

/-- Two module-valued solutions of the recurrence with the same two initial values are
equal.  Together with the explicit construction of solutions by `Nat.rec`, this makes the
hypothesis style fully equivalent to introducing a definition. -/
theorem solution_ext {M : Type*} [AddCommMonoid M] [Module R M] {G H : ℕ → M}
    (hG : ∀ j, G (j + 2) = p • G (j + 1) + q • G j)
    (hH : ∀ j, H (j + 2) = p • H (j + 1) + q • H j)
    (h0 : G 0 = H 0) (h1 : G 1 = H 1) : G = H := by
  funext n
  have key : ∀ j, G j = H j ∧ G (j + 1) = H (j + 1) := by
    intro j
    induction j with
    | zero => exact ⟨h0, h1⟩
    | succ j ih => exact ⟨ih.2, by rw [hG j, hH j, ih.1, ih.2]⟩
  exact (key n).1

section Recurrence

variable (hF0 : F 0 = 0) (hF1 : F 1 = 1) (hrec : ∀ n, F (n + 2) = p * F (n + 1) + q * F n)
include hF0 hF1 hrec

/-- The hypotheses `F 0 = 0`, `F 1 = 1` and the recurrence determine `F` uniquely.
Consequently, stating results for an arbitrary `F` satisfying them is equivalent to (and more
flexible than) introducing a definition of the sequence. -/
theorem unique {G : ℕ → R} (hG0 : G 0 = 0) (hG1 : G 1 = 1)
    (hGrec : ∀ n, G (n + 2) = p * G (n + 1) + q * G n) (n : ℕ) : F n = G n := by
  have key : ∀ j, F j = G j ∧ F (j + 1) = G (j + 1) := by
    intro j
    induction j with
    | zero => exact ⟨hF0.trans hG0.symm, hF1.trans hG1.symm⟩
    | succ j ih => exact ⟨ih.2, by rw [hrec j, hGrec j, ih.1, ih.2]⟩
  exact (key n).1

/-- If `α ^ 2 = p • α + q • 1` in an `R`-algebra, then all powers of `α` are the linear
forms `α ^ (j + 1) = F (j + 1) • α + (q * F j) • 1`. -/
theorem pow_succ_smul {α : A} (hα : α ^ 2 = p • α + q • 1) (j : ℕ) :
    α ^ (j + 1) = F (j + 1) • α + (q * F j) • 1 := by
  induction j with
  | zero => simp [hF0, hF1]
  | succ j ih =>
    rw [pow_succ, ih, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, ← pow_two, hα,
      hrec j]
    match_scalars <;> ring

/-- **Theorem 1.1**, maximally generalised: the Lucas-weight sum reproduces **any** solution
`G` of the recurrence — arbitrary initial values `G 0`, `G 1`, no hypotheses on them — at
index `(m + 1) * n`:
`∑ ℓ ≤ n, (n.choose ℓ) * (q * F m) ^ (n - ℓ) * F (m + 1) ^ ℓ * G ℓ = G ((m + 1) * n)`.

`F` must be the fundamental solution (`F 0 = 0`, `F 1 = 1`) since it supplies the weights,
but `G` need only satisfy the recurrence — and may take values in an arbitrary `R`-module,
since the identity is linear in the solution.  `G := F` recovers `LucasU.sum_choose_mul`;
`G 0 = 2`, `G 1 = p` gives the identity for the companion Lucas `V`-sequence,
`G := fun ℓ => F (ℓ + j)` the shifted identities, and vector-valued `G` simultaneous
families — none of which are in the paper.

The underlying reason: the binomial expansion of `(M ^ (m + 1)) ^ n` for the companion
matrix `M = !![p, q; 1, 0]` is an identity of *operators* on the solution space, so it
evaluates on every solution, not just the fundamental one. -/
theorem sum_choose_mul_solution {M : Type*} [AddCommMonoid M] [Module R M] {G : ℕ → M}
    (hG : ∀ j, G (j + 2) = p • G (j + 1) + q • G j) (m n : ℕ) :
    ∑ ℓ ∈ range (n + 1),
        ((n.choose ℓ : R) * (q * F m) ^ (n - ℓ) * F (m + 1) ^ ℓ) • G ℓ
      = G ((m + 1) * n) := by
  set W : Matrix (Fin 2) (Fin 2) R := !![p, q; 1, 0] with hW
  have hα : W ^ 2 = p • W + q • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, hW, Matrix.mul_apply, Fin.sum_univ_two]
  have hpow := pow_succ_smul (A := Matrix (Fin 2) (Fin 2) R) hF0 hF1 hrec hα
  -- the second fundamental solution `E = 1, 0, q, q * p, ...` (initial values `1, 0`)
  obtain ⟨E, hE0, hEs⟩ : ∃ E : ℕ → R, E 0 = 1 ∧ ∀ j, E (j + 1) = q * F j :=
    ⟨fun ℓ => match ℓ with | 0 => 1 | j + 1 => q * F j, rfl, fun _ => rfl⟩
  have hErec : ∀ j, E (j + 2) = p * E (j + 1) + q * E j := by
    intro j
    cases j with
    | zero => rw [hEs 1, hEs 0, hE0, hF0, hF1]; ring
    | succ i => rw [hEs (i + 2), hEs (i + 1), hEs i, hrec i]; ring
  -- the bottom row of `W ^ j` is `(F j, E j)`
  have hentry : ∀ j, (W ^ j) 1 0 = F j ∧ (W ^ j) 1 1 = E j := by
    intro j
    cases j with
    | zero => exact ⟨by simp [hF0], by simp [hE0]⟩
    | succ i => exact ⟨by rw [hpow i]; simp [hW], by rw [hpow i]; simp [hW, hEs i]⟩
  have hcomm : Commute (F (m + 1) • W) ((q * F m) • (1 : Matrix (Fin 2) (Fin 2) R)) :=
    ((Commute.one_right W).smul_right _).smul_left _
  have hcast : ∀ ℓ : ℕ, ((n.choose ℓ : ℕ) : Matrix (Fin 2) (Fin 2) R)
      = (n.choose ℓ : R) • (1 : Matrix (Fin 2) (Fin 2) R) := by
    intro ℓ
    rw [← Algebra.algebraMap_eq_smul_one, map_natCast]
  have expand : (W ^ (m + 1)) ^ n
      = ∑ ℓ ∈ range (n + 1),
          ((n.choose ℓ : R) * F (m + 1) ^ ℓ * (q * F m) ^ (n - ℓ)) • W ^ ℓ := by
    rw [hpow m, hcomm.add_pow]
    refine sum_congr rfl fun ℓ _ => ?_
    rw [smul_pow, smul_pow, one_pow, hcast ℓ]
    simp only [mul_smul_comm, mul_one, smul_smul]
    match_scalars
    ring
  -- the identity, for any sequence realised in the bottom row of the powers of `W`
  have main : ∀ (S : ℕ → R) (i : Fin 2), (∀ j, (W ^ j) 1 i = S j) →
      ∑ ℓ ∈ range (n + 1), (n.choose ℓ : R) * (q * F m) ^ (n - ℓ) * F (m + 1) ^ ℓ * S ℓ
        = S ((m + 1) * n) := by
    intro S i hS
    calc ∑ ℓ ∈ range (n + 1), (n.choose ℓ : R) * (q * F m) ^ (n - ℓ) * F (m + 1) ^ ℓ * S ℓ
        = ∑ ℓ ∈ range (n + 1),
            ((n.choose ℓ : R) * F (m + 1) ^ ℓ * (q * F m) ^ (n - ℓ)) * S ℓ := by
          refine sum_congr rfl fun ℓ _ => ?_
          ring
      _ = ((W ^ (m + 1)) ^ n) 1 i := by
          rw [expand, Matrix.sum_apply]
          exact (sum_congr rfl fun ℓ _ => by
            rw [Matrix.smul_apply, hS ℓ, smul_eq_mul]).symm
      _ = (W ^ ((m + 1) * n)) 1 i := by rw [pow_mul]
      _ = S ((m + 1) * n) := hS _
  -- every solution is a linear combination of the two fundamental ones
  have hGdec : ∀ ℓ, G ℓ = F ℓ • G 1 + E ℓ • G 0 := by
    have key : ∀ j, G j = F j • G 1 + E j • G 0 ∧
        G (j + 1) = F (j + 1) • G 1 + E (j + 1) • G 0 := by
      intro j
      induction j with
      | zero =>
        constructor
        · rw [hF0, hE0]; simp
        · rw [hF1, hEs 0, hF0]; simp
      | succ j ih =>
        refine ⟨ih.2, ?_⟩
        rw [hG j, hrec j, hErec j, ih.1, ih.2]
        module
    exact fun ℓ => (key ℓ).1
  calc ∑ ℓ ∈ range (n + 1),
        ((n.choose ℓ : R) * (q * F m) ^ (n - ℓ) * F (m + 1) ^ ℓ) • G ℓ
      = ∑ ℓ ∈ range (n + 1),
          (((n.choose ℓ : R) * (q * F m) ^ (n - ℓ) * F (m + 1) ^ ℓ * F ℓ) • G 1
            + ((n.choose ℓ : R) * (q * F m) ^ (n - ℓ) * F (m + 1) ^ ℓ * E ℓ) • G 0) := by
        refine sum_congr rfl fun ℓ _ => ?_
        rw [hGdec ℓ, smul_add, smul_smul, smul_smul]
    _ = (∑ ℓ ∈ range (n + 1),
            (n.choose ℓ : R) * (q * F m) ^ (n - ℓ) * F (m + 1) ^ ℓ * F ℓ) • G 1
          + (∑ ℓ ∈ range (n + 1),
              (n.choose ℓ : R) * (q * F m) ^ (n - ℓ) * F (m + 1) ^ ℓ * E ℓ) • G 0 := by
        rw [sum_add_distrib, ← sum_smul, ← sum_smul]
    _ = F ((m + 1) * n) • G 1 + E ((m + 1) * n) • G 0 := by
        rw [main F 0 (fun j => (hentry j).1), main E 1 (fun j => (hentry j).2)]
    _ = G ((m + 1) * n) := (hGdec _).symm

/-- **Theorem 1.1** of the paper, generalised to any Lucas sequence over any commutative
semiring: `∑ ℓ ≤ n, (n.choose ℓ) * (q * F m) ^ (n - ℓ) * F (m + 1) ^ ℓ * F ℓ = F ((m+1)n)`.
No positivity, no discriminant condition, no real square roots.

The index `m` is shifted by one relative to the paper so that all indices are naturals.
This is the case `G := F` of `LucasU.sum_choose_mul_solution`. -/
theorem sum_choose_mul (m n : ℕ) :
    ∑ ℓ ∈ range (n + 1), (n.choose ℓ : R) * (q * F m) ^ (n - ℓ) * F (m + 1) ^ ℓ * F ℓ
      = F ((m + 1) * n) := by
  have h := sum_choose_mul_solution hF0 hF1 hrec (M := R) (G := F)
    (fun j => by rw [hrec j, smul_eq_mul, smul_eq_mul]) m n
  simpa [smul_eq_mul] using h

/-- The fundamental Lucas divisibility law: index divisibility implies sequence
divisibility, `a ∣ b → F a ∣ F b`, over any commutative semiring.  For `Nat.fib` this is
`Nat.fib_dvd`.  It drops out of `LucasU.sum_choose_mul`: the `ℓ = 0` term of the sum
vanishes and every other term contains the factor `F (m + 1)`. -/
theorem dvd_of_dvd {a b : ℕ} (h : a ∣ b) : F a ∣ F b := by
  obtain ⟨k, rfl⟩ := h
  cases a with
  | zero => simp [hF0]
  | succ m =>
    rw [← sum_choose_mul hF0 hF1 hrec m k]
    refine Finset.dvd_sum fun ℓ _ => ?_
    cases ℓ with
    | zero => simp [hF0]
    | succ i =>
      exact ⟨(k.choose (i + 1) : R) * (q * F m) ^ (k - (i + 1)) * F (m + 1) ^ i * F (i + 1),
        by ring⟩

end Recurrence

section Binet

variable {S : Type*} [CommRing S] {p q : S} {F : ℕ → S}

/-- The Binet formula in denominator-free form: for any two roots `α`, `β` of
`X ^ 2 - p * X - q` in a commutative ring, `F j * (α - β) = α ^ j - β ^ j`.  (Not needed for
the results below — a byproduct of `LucasU.pow_succ_smul`.) -/
theorem mul_sub_eq_pow_sub_pow (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hrec : ∀ n, F (n + 2) = p * F (n + 1) + q * F n)
    {α β : S} (hα : α ^ 2 = p * α + q) (hβ : β ^ 2 = p * β + q) (j : ℕ) :
    F j * (α - β) = α ^ j - β ^ j := by
  have hα' : α ^ 2 = p • α + q • (1 : S) := by simpa [smul_eq_mul] using hα
  have hβ' : β ^ 2 = p • β + q • (1 : S) := by simpa [smul_eq_mul] using hβ
  cases j with
  | zero => simp [hF0]
  | succ i =>
    have h1 := pow_succ_smul (A := S) hF0 hF1 hrec hα' i
    have h2 := pow_succ_smul (A := S) hF0 hF1 hrec hβ' i
    simp only [smul_eq_mul, mul_one] at h1 h2
    rw [h1, h2]
    ring

end Binet

end LucasU

/-- **Remark 1.4** upgraded: the Lucas identity specialises to `Nat.fib` over `ℕ` itself —
a cast-free statement that the paper's real-analytic proof cannot even express. -/
theorem Nat.sum_choose_mul_fib (m n : ℕ) :
    ∑ ℓ ∈ range (n + 1), n.choose ℓ * Nat.fib m ^ (n - ℓ) * Nat.fib (m + 1) ^ ℓ * Nat.fib ℓ
      = Nat.fib ((m + 1) * n) := by
  have h := LucasU.sum_choose_mul (R := ℕ) (p := 1) (q := 1) Nat.fib_zero Nat.fib_one
    (fun j => by rw [Nat.fib_add_two]; ring) m n
  simpa using h

namespace Polynomial.Chebyshev

/-- Chebyshev polynomials of the second kind are (up to an index shift) the Lucas sequence
with `p = 2 * X`, `q = -1` over `R[X]`: the Lucas identity becomes a composition identity
for `Polynomial.Chebyshev.U`.  This lies in the `q < 0` regime, where the annulus theorems
below cannot apply but the algebraic identity still does. -/
theorem sum_choose_mul_U (R : Type*) [CommRing R] (m n : ℕ) :
    ∑ ℓ ∈ range (n + 1), (n.choose ℓ : R[X]) * (-U R ((m : ℤ) - 1)) ^ (n - ℓ)
        * U R m ^ ℓ * U R ((ℓ : ℤ) - 1)
      = U R (((m : ℤ) + 1) * n - 1) := by
  have hF0 : U R (((0 : ℕ) : ℤ) - 1) = 0 := by simp
  have hF1 : U R (((1 : ℕ) : ℤ) - 1) = 1 := by simp
  have hrec : ∀ j : ℕ, U R (((j + 2 : ℕ) : ℤ) - 1)
      = 2 * X * U R (((j + 1 : ℕ) : ℤ) - 1) + -1 * U R (((j : ℕ) : ℤ) - 1) := by
    intro j
    have h := U_add_two R ((j : ℤ) - 1)
    have e2 : ((j : ℤ) - 1) + 2 = ((j + 2 : ℕ) : ℤ) - 1 := by push_cast; ring
    have e1 : ((j : ℤ) - 1) + 1 = ((j + 1 : ℕ) : ℤ) - 1 := by push_cast; ring
    rw [e2, e1] at h
    rw [h]
    ring
  have h := LucasU.sum_choose_mul (p := 2 * X) (q := -1)
    (F := fun j => U R ((j : ℤ) - 1)) hF0 hF1 hrec m n
  have em : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by push_cast; ring
  have eN : ((((m + 1) * n : ℕ)) : ℤ) - 1 = ((m : ℤ) + 1) * n - 1 := by push_cast; ring
  simpa [em, eN, neg_one_mul] using h

/-- The Lucas divisibility law for Chebyshev-`U`: `a ∣ b → U (a - 1) ∣ U (b - 1)`. -/
theorem U_sub_one_dvd (R : Type*) [CommRing R] {a b : ℕ} (h : a ∣ b) :
    U R ((a : ℤ) - 1) ∣ U R ((b : ℤ) - 1) := by
  have hF0 : U R (((0 : ℕ) : ℤ) - 1) = 0 := by simp
  have hF1 : U R (((1 : ℕ) : ℤ) - 1) = 1 := by simp
  have hrec : ∀ j : ℕ, U R (((j + 2 : ℕ) : ℤ) - 1)
      = 2 * X * U R (((j + 1 : ℕ) : ℤ) - 1) + -1 * U R (((j : ℕ) : ℤ) - 1) := by
    intro j
    have hj := U_add_two R ((j : ℤ) - 1)
    have e2 : ((j : ℤ) - 1) + 2 = ((j + 2 : ℕ) : ℤ) - 1 := by push_cast; ring
    have e1 : ((j : ℤ) - 1) + 1 = ((j + 1 : ℕ) : ℤ) - 1 := by push_cast; ring
    rw [e2, e1] at hj
    rw [hj]
    ring
  exact LucasU.dvd_of_dvd (p := 2 * X) (q := -1)
    (F := fun j => U R ((j : ℤ) - 1)) hF0 hF1 hrec h

end Polynomial.Chebyshev

namespace Real

/-! ### Positivity and small values, over `ℝ` -/

variable {P Q : ℝ} {F : ℕ → ℝ}

section Recurrence

variable (hF0 : F 0 = 0) (hF1 : F 1 = 1) (hrec : ∀ n, F (n + 2) = P * F (n + 1) + Q * F n)
include hF0 hF1 hrec

/-- For `P > 0`, `Q ≥ 0`, a Lucas sequence is nonnegative, and strictly positive from
index `1` onwards. -/
theorem lucas_nonneg_and_pos (hP : 0 < P) (hQ : 0 ≤ Q) (j : ℕ) :
    0 ≤ F j ∧ 0 < F (j + 1) := by
  induction j with
  | zero => exact ⟨hF0.ge, by rw [hF1]; norm_num⟩
  | succ j ih =>
    refine ⟨ih.2.le, ?_⟩
    rw [hrec j]
    nlinarith [ih.1, ih.2]

theorem lucas_nonneg (hP : 0 < P) (hQ : 0 ≤ Q) (j : ℕ) : 0 ≤ F j :=
  (lucas_nonneg_and_pos hF0 hF1 hrec hP hQ j).1

theorem lucas_pos (hP : 0 < P) (hQ : 0 ≤ Q) (j : ℕ) : 0 < F (j + 1) :=
  (lucas_nonneg_and_pos hF0 hF1 hrec hP hQ j).2

theorem lucas_two : F 2 = P := by
  have := hrec 0; rw [hF0, hF1] at this; linarith

theorem lucas_three : F 3 = P ^ 2 + Q := by
  have h2 := lucas_two hF0 hF1 hrec
  have := hrec 1; rw [hF1, h2] at this; nlinarith

theorem lucas_four : F 4 = P ^ 3 + 2 * P * Q := by
  have h2 := lucas_two hF0 hF1 hrec
  have h3 := lucas_three hF0 hF1 hrec
  have := hrec 2; rw [h2, h3] at this; nlinarith

end Recurrence

/-- **Theorem 1.1** of the paper: the `k`-Fibonacci case `Q = 1` of
`LucasU.sum_choose_mul`, over `ℝ`.  Note that no positivity of `k` is needed. -/
theorem sum_choose_mul_kFib {k : ℝ} {F : ℕ → ℝ} (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hrec : ∀ n, F (n + 2) = k * F (n + 1) + F n) (m n : ℕ) :
    ∑ ℓ ∈ range (n + 1), (n.choose ℓ : ℝ) * F m ^ (n - ℓ) * F (m + 1) ^ ℓ * F ℓ
      = F ((m + 1) * n) := by
  have h := LucasU.sum_choose_mul (p := k) (q := 1) hF0 hF1
    (fun j => by rw [hrec j]; ring) m n
  simpa using h

/-- The `k`-Fibonacci value `F 3 = k ^ 2 + 1` (the paper's `F_{k,3}`). -/
theorem kFib_three {k : ℝ} {F : ℕ → ℝ} (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hrec : ∀ n, F (n + 2) = k * F (n + 1) + F n) : F 3 = k ^ 2 + 1 := by
  have h := lucas_three (P := k) (Q := 1) hF0 hF1 (fun j => by rw [hrec j]; ring)
  linarith

/-- The `k`-Fibonacci value `F 4 = k ^ 3 + 2 * k` (the paper's `F_{k,4}`). -/
theorem kFib_four {k : ℝ} {F : ℕ → ℝ} (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hrec : ∀ n, F (n + 2) = k * F (n + 1) + F n) : F 4 = k ^ 3 + 2 * k := by
  have h := lucas_four (P := k) (Q := 1) hF0 hF1 (fun j => by rw [hrec j]; ring)
  linarith

end Real

namespace Polynomial

open Finset

variable {K : Type*} [NormedRing K] [NormOneClass K] [NormMulClass K]

/-- The analytic core of Theorem 1.2: if the weights `A ℓ` are nonnegative, sum to `1` over
`1 ≤ ℓ ≤ n`, and dominate the coefficient ratios `‖a (n - ℓ)‖ / ‖a n‖` at scale `R`, then
every root of `p` has norm at most `R`.

This is stated over any normed division ring and for an arbitrary weight sequence `A`;
`LucasU.sum_choose_mul` supplies the Lucas weights
`A ℓ = (n.choose ℓ) * (Q * F m) ^ (n - ℓ) * F (m + 1) ^ ℓ * F ℓ / F ((m + 1) * n)`. -/
theorem norm_le_of_isRoot_of_sum_weights {p : K[X]} {A : ℕ → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hA : ∀ ℓ ∈ Icc 1 p.natDegree, 0 ≤ A ℓ)
    (hsum : ∑ ℓ ∈ Icc 1 p.natDegree, A ℓ = 1)
    (hcoeff : ∀ ℓ ∈ Icc 1 p.natDegree,
      ‖p.coeff (p.natDegree - ℓ)‖ ≤ A ℓ * ‖p.leadingCoeff‖ * R ^ ℓ)
    {z : K} (hz : p.IsRoot z) : ‖z‖ ≤ R := by
  set n := p.natDegree with hn
  by_contra hcon
  push Not at hcon
  have hz0 : 0 < ‖z‖ := hR.trans_lt hcon
  -- The weights sum to `1`, so `Icc 1 n` is nonempty and hence `p ≠ 0`.
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at hsum; simp at hsum
    · exact h
  have hp0 : p ≠ 0 := by
    intro h
    rw [hn, h, natDegree_zero] at hn1
    exact absurd hn1 (by norm_num)
  have hlc : 0 < ‖p.leadingCoeff‖ := by simpa using leadingCoeff_ne_zero.2 hp0
  -- Some weight is strictly positive, since the weights sum to `1`.
  obtain ⟨j, hj, hjpos⟩ : ∃ j ∈ Icc 1 n, 0 < A j := by
    by_contra hall
    push Not at hall
    have : ∑ ℓ ∈ Icc 1 n, A ℓ = 0 :=
      sum_eq_zero fun ℓ hℓ => le_antisymm (hall ℓ hℓ) (hA ℓ hℓ)
    rw [hsum] at this
    exact one_ne_zero this
  -- Split the leading term off the evaluation of `p` at `z`.
  have heval : p.leadingCoeff * z ^ n = -∑ i ∈ range n, p.coeff i * z ^ i := by
    have := hz
    rw [IsRoot.def, eval_eq_sum_range, ← hn, range_add_one, sum_insert (by simp)] at this
    rw [← coeff_natDegree, ← hn, eq_neg_iff_add_eq_zero]
    exact this
  -- Reindex `range n` as `Icc 1 n` via `i ↦ n - i`.
  have hreindex : ∑ i ∈ range n, ‖p.coeff i‖ * ‖z‖ ^ i
      = ∑ ℓ ∈ Icc 1 n, ‖p.coeff (n - ℓ)‖ * ‖z‖ ^ (n - ℓ) := by
    refine sum_nbij' (fun i => n - i) (fun ℓ => n - ℓ) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      simp only [mem_range] at hi
      simp only [mem_Icc]
      omega
    · intro ℓ hℓ
      simp only [mem_Icc] at hℓ
      simp only [mem_range]
      omega
    · intro i hi
      simp only [mem_range] at hi
      omega
    · intro ℓ hℓ
      simp only [mem_Icc] at hℓ
      omega
    · intro i hi
      simp only [mem_range] at hi
      rw [Nat.sub_sub_self hi.le]
  -- The tail is strictly dominated by the leading term.
  have hkey : ∑ ℓ ∈ Icc 1 n, ‖p.coeff (n - ℓ)‖ * ‖z‖ ^ (n - ℓ)
      < ‖p.leadingCoeff‖ * ‖z‖ ^ n := by
    have hlt : ∑ ℓ ∈ Icc 1 n, ‖p.coeff (n - ℓ)‖ * ‖z‖ ^ (n - ℓ)
        < ∑ ℓ ∈ Icc 1 n,
            A ℓ * ‖p.leadingCoeff‖ * ‖z‖ ^ ℓ * ‖z‖ ^ (n - ℓ) := by
      refine sum_lt_sum (fun ℓ hℓ => ?_) ⟨j, hj, ?_⟩
      · have h1 := hcoeff ℓ hℓ
        have h2 : R ^ ℓ ≤ ‖z‖ ^ ℓ := pow_le_pow_left₀ hR hcon.le ℓ
        have h3 : A ℓ * ‖p.leadingCoeff‖ * R ^ ℓ
            ≤ A ℓ * ‖p.leadingCoeff‖ * ‖z‖ ^ ℓ :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg (hA ℓ hℓ) (norm_nonneg _))
        nlinarith [pow_pos hz0 (n - ℓ), norm_nonneg (p.coeff (n - ℓ))]
      · have h1 := hcoeff j hj
        have h2 : R ^ j < ‖z‖ ^ j := by
          refine pow_lt_pow_left₀ hcon hR ?_
          simp only [mem_Icc] at hj
          omega
        have h3 : A j * ‖p.leadingCoeff‖ * R ^ j < A j * ‖p.leadingCoeff‖ * ‖z‖ ^ j :=
          mul_lt_mul_of_pos_left h2 (by positivity)
        nlinarith [pow_pos hz0 (n - j)]
    refine hlt.trans_le (le_of_eq ?_)
    have hrw :
        ∑ ℓ ∈ Icc 1 n, A ℓ * ‖p.leadingCoeff‖ * ‖z‖ ^ ℓ * ‖z‖ ^ (n - ℓ)
          = ∑ ℓ ∈ Icc 1 n, A ℓ * (‖p.leadingCoeff‖ * ‖z‖ ^ n) := by
      refine sum_congr rfl fun ℓ hℓ => ?_
      simp only [mem_Icc] at hℓ
      rw [mul_assoc, mul_assoc, ← pow_add, Nat.add_sub_cancel' hℓ.2]
    rw [hrw, ← sum_mul, hsum, one_mul]
  -- Contradiction.
  have : ‖p.leadingCoeff‖ * ‖z‖ ^ n < ‖p.leadingCoeff‖ * ‖z‖ ^ n := by
    calc ‖p.leadingCoeff‖ * ‖z‖ ^ n = ‖p.leadingCoeff * z ^ n‖ := by
          rw [norm_mul, norm_pow]
      _ = ‖∑ i ∈ range n, p.coeff i * z ^ i‖ := by rw [heval, norm_neg]
      _ ≤ ∑ i ∈ range n, ‖p.coeff i * z ^ i‖ := norm_sum_le _ _
      _ = ∑ i ∈ range n, ‖p.coeff i‖ * ‖z‖ ^ i := by
          refine sum_congr rfl fun i _ => ?_
          rw [norm_mul, norm_pow]
      _ = ∑ ℓ ∈ Icc 1 n, ‖p.coeff (n - ℓ)‖ * ‖z‖ ^ (n - ℓ) := hreindex
      _ < ‖p.leadingCoeff‖ * ‖z‖ ^ n := hkey
  exact absurd this (lt_irrefl _)

/-- The analytic core of the lower bound in Theorem 1.2: if the weights `A ℓ` are nonnegative,
sum to `1` over `1 ≤ ℓ ≤ n`, and `‖a ℓ‖ * r ^ ℓ ≤ A ℓ * ‖a 0‖` for all `1 ≤ ℓ ≤ n`, then
every root of `p` has norm at least `r`.

The paper deduces this from the upper bound applied to the reversed polynomial
`Q(z) = zⁿ q(1/z)`; here we simply run the same estimate directly on the constant term. -/
theorem le_norm_of_isRoot_of_sum_weights {p : K[X]} {A : ℕ → ℝ} {r : ℝ}
    (hA : ∀ ℓ ∈ Icc 1 p.natDegree, 0 ≤ A ℓ)
    (hsum : ∑ ℓ ∈ Icc 1 p.natDegree, A ℓ = 1)
    (hcoeff : ∀ ℓ ∈ Icc 1 p.natDegree,
      ‖p.coeff ℓ‖ * r ^ ℓ ≤ A ℓ * ‖p.coeff 0‖)
    {z : K} (hz : p.IsRoot z) : r ≤ ‖z‖ := by
  set n := p.natDegree with hn
  by_contra hcon
  push Not at hcon
  have hr0 : 0 < r := (norm_nonneg z).trans_lt hcon
  -- The weights sum to `1`, so `Icc 1 n` is nonempty and hence `p ≠ 0`.
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at hsum; simp at hsum
    · exact h
  have hp0 : p ≠ 0 := by
    intro h
    rw [hn, h, natDegree_zero] at hn1
    exact absurd hn1 (by norm_num)
  have hlc : 0 < ‖p.leadingCoeff‖ := by simpa using leadingCoeff_ne_zero.2 hp0
  have hins : range (n + 1) = insert 0 (Icc 1 n) := by
    ext x; simp only [mem_range, mem_insert, mem_Icc]; omega
  -- If the constant coefficient vanishes, the hypothesis at `ℓ = n` is already contradictory.
  rcases eq_or_ne (p.coeff 0) 0 with h0 | h0
  · have h := hcoeff n (mem_Icc.2 ⟨hn1, le_rfl⟩)
    rw [h0, norm_zero, mul_zero] at h
    simp only [hn, coeff_natDegree] at h
    exact absurd h (not_le.2 (mul_pos hlc (pow_pos hr0 _)))
  have h0' : 0 < ‖p.coeff 0‖ := norm_pos_iff.2 h0
  -- Some weight is strictly positive, since the weights sum to `1`.
  obtain ⟨j, hj, hjpos⟩ : ∃ j ∈ Icc 1 n, 0 < A j := by
    by_contra hall
    push Not at hall
    have : ∑ ℓ ∈ Icc 1 n, A ℓ = 0 :=
      sum_eq_zero fun ℓ hℓ => le_antisymm (hall ℓ hℓ) (hA ℓ hℓ)
    rw [hsum] at this
    exact one_ne_zero this
  -- Isolate the constant term in the evaluation of `p` at `z`.
  have heval : p.coeff 0 = -∑ ℓ ∈ Icc 1 n, p.coeff ℓ * z ^ ℓ := by
    have h := hz
    rw [IsRoot.def, eval_eq_sum_range, ← hn, hins, sum_insert (by simp)] at h
    rw [pow_zero, mul_one] at h
    exact eq_neg_of_add_eq_zero_left h
  -- The constant term is strictly dominated by the tail, a contradiction.
  have hbound : ‖p.coeff 0‖ < ∑ ℓ ∈ Icc 1 n, A ℓ * ‖p.coeff 0‖ := by
    calc ‖p.coeff 0‖
        = ‖∑ ℓ ∈ Icc 1 n, p.coeff ℓ * z ^ ℓ‖ := by rw [heval, norm_neg]
      _ ≤ ∑ ℓ ∈ Icc 1 n, ‖p.coeff ℓ * z ^ ℓ‖ := norm_sum_le _ _
      _ = ∑ ℓ ∈ Icc 1 n, ‖p.coeff ℓ‖ * ‖z‖ ^ ℓ := by
          refine sum_congr rfl fun ℓ _ => ?_
          rw [norm_mul, norm_pow]
      _ < ∑ ℓ ∈ Icc 1 n, A ℓ * ‖p.coeff 0‖ := ?_
    refine sum_lt_sum (fun ℓ hℓ => ?_) ⟨j, hj, ?_⟩
    · have h2 : ‖z‖ ^ ℓ ≤ r ^ ℓ := pow_le_pow_left₀ (norm_nonneg z) hcon.le ℓ
      have h1 := hcoeff ℓ hℓ
      nlinarith [norm_nonneg (p.coeff ℓ)]
    · have hj1 : j ≠ 0 := by simp only [mem_Icc] at hj; omega
      rcases eq_or_ne (p.coeff j) 0 with hcj | hcj
      · simpa [hcj] using mul_pos hjpos h0'
      · have h2 : ‖z‖ ^ j < r ^ j := pow_lt_pow_left₀ hcon (norm_nonneg z) hj1
        have h1 := hcoeff j hj
        have hcj' : 0 < ‖p.coeff j‖ := norm_pos_iff.2 hcj
        nlinarith
  rw [← sum_mul, hsum, one_mul] at hbound
  exact absurd hbound (lt_irrefl _)

/-- **Theorem 1.2** (upper bound), generalised to Lucas weights: if `R ≥ 0` satisfies
`‖a (n - ℓ)‖ * F ((m + 1) * n)`
`  ≤ (n.choose ℓ) * (Q * F m) ^ (n - ℓ) * F (m + 1) ^ ℓ * F ℓ * (‖a n‖ * R ^ ℓ)`
for `1 ≤ ℓ ≤ n`, then every zero of `p` lies in the closed disc of radius `R`. -/
theorem norm_le_of_isRoot_lucas {p : K[X]} {P Q : ℝ} {F : ℕ → ℝ} (hP : 0 < P) (hQ : 0 ≤ Q)
    (hF0 : F 0 = 0) (hF1 : F 1 = 1) (hrec : ∀ j, F (j + 2) = P * F (j + 1) + Q * F j)
    (m : ℕ) (hdeg : 1 ≤ p.natDegree) {R : ℝ} (hR : 0 ≤ R)
    (hcoeff : ∀ ℓ ∈ Icc 1 p.natDegree,
      ‖p.coeff (p.natDegree - ℓ)‖ * F ((m + 1) * p.natDegree)
        ≤ (p.natDegree.choose ℓ : ℝ) * (Q * F m) ^ (p.natDegree - ℓ) * F (m + 1) ^ ℓ * F ℓ
            * (‖p.leadingCoeff‖ * R ^ ℓ))
    {z : K} (hz : p.IsRoot z) : ‖z‖ ≤ R := by
  set n := p.natDegree with hn
  have hFnn := Real.lucas_nonneg hF0 hF1 hrec hP hQ
  -- `F ((m + 1) * n)` is positive, since `(m + 1) * n ≥ 1`.
  obtain ⟨t, ht⟩ : ∃ t, (m + 1) * n = t + 1 := ⟨(m + 1) * n - 1, by
    have : 1 ≤ (m + 1) * n := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega⟩
  have hD : 0 < F ((m + 1) * n) := by
    rw [ht]; exact Real.lucas_pos hF0 hF1 hrec hP hQ t
  -- The numerators of the weights are nonnegative.
  have hNnn : ∀ ℓ, 0 ≤ (n.choose ℓ : ℝ) * (Q * F m) ^ (n - ℓ) * F (m + 1) ^ ℓ * F ℓ :=
    fun ℓ => mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (mul_nonneg hQ (hFnn m)) _)) (pow_nonneg (hFnn (m + 1)) _)) (hFnn ℓ)
  refine norm_le_of_isRoot_of_sum_weights
    (A := fun ℓ =>
      (n.choose ℓ : ℝ) * (Q * F m) ^ (n - ℓ) * F (m + 1) ^ ℓ * F ℓ / F ((m + 1) * n))
    hR (fun ℓ _ => div_nonneg (hNnn ℓ) hD.le) ?_ ?_ hz
  · -- The weights sum to `1`: the `ℓ = 0` term of the identity vanishes because `F 0 = 0`.
    have hthm := LucasU.sum_choose_mul hF0 hF1 hrec m n
    have hins : range (n + 1) = insert 0 (Icc 1 n) := by
      ext x; simp only [mem_range, mem_insert, mem_Icc]; omega
    rw [hins, sum_insert (by simp)] at hthm
    have hzero : (n.choose 0 : ℝ) * (Q * F m) ^ (n - 0) * F (m + 1) ^ 0 * F 0 = 0 := by
      rw [hF0, mul_zero]
    rw [hzero, zero_add] at hthm
    rw [← sum_div, hthm, div_self hD.ne']
  · intro ℓ hℓ
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hD, mul_assoc]
    exact hcoeff ℓ hℓ

/-- **Theorem 1.2** (lower bound), generalised to Lucas weights: if
`‖a ℓ‖ * F ((m + 1) * n) * r ^ ℓ`
`  ≤ (n.choose ℓ) * (Q * F m) ^ (n - ℓ) * F (m + 1) ^ ℓ * F ℓ * ‖a 0‖`
for `1 ≤ ℓ ≤ n`, then every zero of `p` has norm at least `r`. -/
theorem le_norm_of_isRoot_lucas {p : K[X]} {P Q : ℝ} {F : ℕ → ℝ} (hP : 0 < P) (hQ : 0 ≤ Q)
    (hF0 : F 0 = 0) (hF1 : F 1 = 1) (hrec : ∀ j, F (j + 2) = P * F (j + 1) + Q * F j)
    (m : ℕ) (hdeg : 1 ≤ p.natDegree) {r : ℝ}
    (hcoeff : ∀ ℓ ∈ Icc 1 p.natDegree,
      ‖p.coeff ℓ‖ * F ((m + 1) * p.natDegree) * r ^ ℓ
        ≤ (p.natDegree.choose ℓ : ℝ) * (Q * F m) ^ (p.natDegree - ℓ) * F (m + 1) ^ ℓ * F ℓ
            * ‖p.coeff 0‖)
    {z : K} (hz : p.IsRoot z) : r ≤ ‖z‖ := by
  set n := p.natDegree with hn
  have hFnn := Real.lucas_nonneg hF0 hF1 hrec hP hQ
  obtain ⟨t, ht⟩ : ∃ t, (m + 1) * n = t + 1 := ⟨(m + 1) * n - 1, by
    have : 1 ≤ (m + 1) * n := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega⟩
  have hD : 0 < F ((m + 1) * n) := by
    rw [ht]; exact Real.lucas_pos hF0 hF1 hrec hP hQ t
  have hNnn : ∀ ℓ, 0 ≤ (n.choose ℓ : ℝ) * (Q * F m) ^ (n - ℓ) * F (m + 1) ^ ℓ * F ℓ :=
    fun ℓ => mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (mul_nonneg hQ (hFnn m)) _)) (pow_nonneg (hFnn (m + 1)) _)) (hFnn ℓ)
  refine le_norm_of_isRoot_of_sum_weights
    (A := fun ℓ =>
      (n.choose ℓ : ℝ) * (Q * F m) ^ (n - ℓ) * F (m + 1) ^ ℓ * F ℓ / F ((m + 1) * n))
    (fun ℓ _ => div_nonneg (hNnn ℓ) hD.le) ?_ ?_ hz
  · have hthm := LucasU.sum_choose_mul hF0 hF1 hrec m n
    have hins : range (n + 1) = insert 0 (Icc 1 n) := by
      ext x; simp only [mem_range, mem_insert, mem_Icc]; omega
    rw [hins, sum_insert (by simp)] at hthm
    have hzero : (n.choose 0 : ℝ) * (Q * F m) ^ (n - 0) * F (m + 1) ^ 0 * F 0 = 0 := by
      rw [hF0, mul_zero]
    rw [hzero, zero_add] at hthm
    rw [← sum_div, hthm, div_self hD.ne']
  · intro ℓ hℓ
    rw [div_mul_eq_mul_div, le_div_iff₀ hD]
    calc ‖p.coeff ℓ‖ * r ^ ℓ * F ((m + 1) * n)
        = ‖p.coeff ℓ‖ * F ((m + 1) * n) * r ^ ℓ := by ring
      _ ≤ _ := hcoeff ℓ hℓ

/-- Auxiliary `rpow` computation for the upper radius: if `R` dominates the `ℓ`-th root of
`D / Nl * (a / c)`, then `a * D ≤ Nl * (c * R ^ ℓ)`. -/
private lemma mul_le_of_rpow_le {D Nl a c R : ℝ} {ℓ : ℕ} (hD : 0 ≤ D) (hN : 0 < Nl)
    (ha : 0 ≤ a) (hc : 0 < c) (hℓ : ℓ ≠ 0)
    (hR : (D / Nl * (a / c)) ^ ((ℓ : ℝ)⁻¹) ≤ R) :
    a * D ≤ Nl * (c * R ^ ℓ) := by
  have hb0 : 0 ≤ D / Nl * (a / c) := by positivity
  have hpow : D / Nl * (a / c) ≤ R ^ ℓ :=
    calc D / Nl * (a / c) = ((D / Nl * (a / c)) ^ ((ℓ : ℝ)⁻¹)) ^ ℓ :=
          (Real.rpow_inv_natCast_pow hb0 hℓ).symm
      _ ≤ R ^ ℓ := pow_le_pow_left₀ (Real.rpow_nonneg hb0 _) hR ℓ
  calc a * D = Nl * c * (D / Nl * (a / c)) := by field_simp [hN.ne', hc.ne']
    _ ≤ Nl * c * R ^ ℓ := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = Nl * (c * R ^ ℓ) := by ring

/-- Auxiliary `rpow` computation for the lower radius: if `r` is below the `ℓ`-th root of
`Nl / D * (a / c)`, then `c * D * r ^ ℓ ≤ Nl * a`. -/
private lemma mul_rpow_le_of_le {D Nl a c r : ℝ} {ℓ : ℕ} (hD : 0 < D) (hN : 0 ≤ Nl)
    (ha : 0 ≤ a) (hc : 0 < c) (hℓ : ℓ ≠ 0) (hr0 : 0 ≤ r)
    (hr : r ≤ (Nl / D * (a / c)) ^ ((ℓ : ℝ)⁻¹)) :
    c * D * r ^ ℓ ≤ Nl * a := by
  have hb0 : 0 ≤ Nl / D * (a / c) := by positivity
  have hpow : r ^ ℓ ≤ Nl / D * (a / c) :=
    calc r ^ ℓ
        ≤ ((Nl / D * (a / c)) ^ ((ℓ : ℝ)⁻¹)) ^ ℓ := pow_le_pow_left₀ hr0 hr ℓ
      _ = Nl / D * (a / c) := Real.rpow_inv_natCast_pow hb0 hℓ
  calc c * D * r ^ ℓ ≤ c * D * (Nl / D * (a / c)) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = Nl * a := by field_simp [hD.ne', hc.ne']

section MasterAnnulus

variable {p : K[X]} {A : ℕ → ℝ}

/-- Master closed-form upper radius: for **any** weights positive on `1 ≤ ℓ ≤ n` and summing
to `1` there, every root satisfies
`‖z‖ ≤ max_{1 ≤ ℓ ≤ n} (1 / A ℓ * ‖a (n - ℓ) / a n‖) ^ (1 / ℓ)`.

Any combinatorial identity producing a partition of unity therefore yields an annulus; the
Lucas radii below are the instance whose weights come from `LucasU.sum_choose_mul`. -/
theorem norm_le_sup_of_isRoot_of_sum_weights
    (hA : ∀ ℓ ∈ Icc 1 p.natDegree, 0 < A ℓ)
    (hsum : ∑ ℓ ∈ Icc 1 p.natDegree, A ℓ = 1)
    (hdeg : 1 ≤ p.natDegree) {z : K} (hz : p.IsRoot z) :
    ‖z‖ ≤ (Icc 1 p.natDegree).sup' (Finset.nonempty_Icc.2 hdeg) fun ℓ =>
      (1 / A ℓ * (‖p.coeff (p.natDegree - ℓ)‖ / ‖p.leadingCoeff‖)) ^ ((ℓ : ℝ)⁻¹) := by
  set n := p.natDegree with hn
  have hp0 : p ≠ 0 := by
    intro h
    rw [hn, h, natDegree_zero] at hdeg
    exact absurd hdeg (by norm_num)
  have hlc : 0 < ‖p.leadingCoeff‖ := by simpa using leadingCoeff_ne_zero.2 hp0
  refine norm_le_of_isRoot_of_sum_weights ?_ (fun ℓ hℓ => (hA ℓ hℓ).le) hsum ?_ hz
  · have hmem : n ∈ Icc 1 n := mem_Icc.2 ⟨hdeg, le_rfl⟩
    refine le_trans ?_ (Finset.le_sup' _ hmem)
    exact Real.rpow_nonneg (mul_nonneg (div_nonneg zero_le_one (hA n hmem).le)
      (div_nonneg (norm_nonneg _) (norm_nonneg _))) _
  · intro ℓ hℓ
    have hℓ0 : ℓ ≠ 0 := by simp only [mem_Icc] at hℓ; omega
    have hle := Finset.le_sup' (s := Icc 1 n) (f := fun ℓ =>
      (1 / A ℓ * (‖p.coeff (n - ℓ)‖ / ‖p.leadingCoeff‖)) ^ ((ℓ : ℝ)⁻¹)) hℓ
    have h := mul_le_of_rpow_le zero_le_one (hA ℓ hℓ) (norm_nonneg (p.coeff (n - ℓ)))
      hlc hℓ0 hle
    rw [mul_one] at h
    rw [mul_assoc]
    exact h

/-- Master closed-form lower radius: for **any** weights positive on `1 ≤ ℓ ≤ n` and summing
to `1` there, and `a ℓ ≠ 0` on that range, every root satisfies
`min_{1 ≤ ℓ ≤ n} (A ℓ * ‖a 0 / a ℓ‖) ^ (1 / ℓ) ≤ ‖z‖`. -/
theorem inf_le_norm_of_isRoot_of_sum_weights
    (hA : ∀ ℓ ∈ Icc 1 p.natDegree, 0 < A ℓ)
    (hsum : ∑ ℓ ∈ Icc 1 p.natDegree, A ℓ = 1)
    (hdeg : 1 ≤ p.natDegree)
    (ha : ∀ ℓ ∈ Icc 1 p.natDegree, p.coeff ℓ ≠ 0) {z : K} (hz : p.IsRoot z) :
    (Icc 1 p.natDegree).inf' (Finset.nonempty_Icc.2 hdeg) (fun ℓ =>
      (A ℓ * (‖p.coeff 0‖ / ‖p.coeff ℓ‖)) ^ ((ℓ : ℝ)⁻¹)) ≤ ‖z‖ := by
  set n := p.natDegree with hn
  have hr0 : 0 ≤ (Icc 1 n).inf' (Finset.nonempty_Icc.2 hdeg) (fun ℓ =>
      (A ℓ * (‖p.coeff 0‖ / ‖p.coeff ℓ‖)) ^ ((ℓ : ℝ)⁻¹)) := by
    refine Finset.le_inf' _ _ fun ℓ hℓ => ?_
    exact Real.rpow_nonneg (mul_nonneg (hA ℓ hℓ).le
      (div_nonneg (norm_nonneg _) (norm_nonneg _))) _
  refine le_norm_of_isRoot_of_sum_weights (fun ℓ hℓ => (hA ℓ hℓ).le) hsum ?_ hz
  intro ℓ hℓ
  have hℓ0 : ℓ ≠ 0 := by simp only [mem_Icc] at hℓ; omega
  have hc : 0 < ‖p.coeff ℓ‖ := norm_pos_iff.2 (ha ℓ hℓ)
  have hb0 : 0 ≤ A ℓ * (‖p.coeff 0‖ / ‖p.coeff ℓ‖) :=
    mul_nonneg (hA ℓ hℓ).le (div_nonneg (norm_nonneg _) (norm_nonneg _))
  have hle := Finset.inf'_le (s := Icc 1 n) (f := fun ℓ =>
    (A ℓ * (‖p.coeff 0‖ / ‖p.coeff ℓ‖)) ^ ((ℓ : ℝ)⁻¹)) hℓ
  have hpow : ((Icc 1 n).inf' (Finset.nonempty_Icc.2 hdeg) fun ℓ =>
      (A ℓ * (‖p.coeff 0‖ / ‖p.coeff ℓ‖)) ^ ((ℓ : ℝ)⁻¹)) ^ ℓ
      ≤ A ℓ * (‖p.coeff 0‖ / ‖p.coeff ℓ‖) :=
    calc _ ≤ ((A ℓ * (‖p.coeff 0‖ / ‖p.coeff ℓ‖)) ^ ((ℓ : ℝ)⁻¹)) ^ ℓ :=
          pow_le_pow_left₀ hr0 hle ℓ
      _ = _ := Real.rpow_inv_natCast_pow hb0 hℓ0
  refine le_trans (mul_le_mul_of_nonneg_left hpow (norm_nonneg _)) (le_of_eq ?_)
  field_simp [hc.ne']

/-- Master annulus: for **any** weights positive on `1 ≤ ℓ ≤ n` summing to `1` there (and
`a ℓ ≠ 0` on that range), all zeros of `p` lie in the closed annulus with radii
`r₁ = min (A ℓ * ‖a 0 / a ℓ‖)^(1/ℓ)` and `r₂ = max ((1 / A ℓ) * ‖a (n-ℓ) / a n‖)^(1/ℓ)`. -/
theorem isRoot_mem_annulus_of_sum_weights
    (hA : ∀ ℓ ∈ Icc 1 p.natDegree, 0 < A ℓ)
    (hsum : ∑ ℓ ∈ Icc 1 p.natDegree, A ℓ = 1)
    (hdeg : 1 ≤ p.natDegree)
    (ha : ∀ ℓ ∈ Icc 1 p.natDegree, p.coeff ℓ ≠ 0) {z : K} (hz : p.IsRoot z) :
    (Icc 1 p.natDegree).inf' (Finset.nonempty_Icc.2 hdeg) (fun ℓ =>
        (A ℓ * (‖p.coeff 0‖ / ‖p.coeff ℓ‖)) ^ ((ℓ : ℝ)⁻¹)) ≤ ‖z‖ ∧
      ‖z‖ ≤ (Icc 1 p.natDegree).sup' (Finset.nonempty_Icc.2 hdeg) fun ℓ =>
        (1 / A ℓ * (‖p.coeff (p.natDegree - ℓ)‖ / ‖p.leadingCoeff‖)) ^ ((ℓ : ℝ)⁻¹) :=
  ⟨inf_le_norm_of_isRoot_of_sum_weights hA hsum hdeg ha hz,
    norm_le_sup_of_isRoot_of_sum_weights hA hsum hdeg hz⟩

end MasterAnnulus

section Annulus

variable {p : K[X]} {P Q : ℝ} {F : ℕ → ℝ}

/-- **Theorem 1.2**, upper radius in closed form, for Lucas weights: every zero of `p` has
norm at most
`r₂ = max_{1 ≤ ℓ ≤ n} (F ((m+1)n) / ((n.choose ℓ) * (Q * F m) ^ (n-ℓ) * F (m+1) ^ ℓ * F ℓ)`
`      * ‖a (n-ℓ) / a n‖) ^ (1/ℓ)`.

Here `m` is one less than the paper's parameter, and the hypothesis `1 ≤ m` corresponds to
the paper's implicit assumption that its radii do not divide by `F 0 = 0`. -/
theorem norm_le_lucas_sup_of_isRoot (hP : 0 < P) (hQ0 : 0 < Q)
    (hF0 : F 0 = 0) (hF1 : F 1 = 1) (hrec : ∀ j, F (j + 2) = P * F (j + 1) + Q * F j)
    {m : ℕ} (hm : 1 ≤ m) (hdeg : 1 ≤ p.natDegree) {z : K} (hz : p.IsRoot z) :
    ‖z‖ ≤ (Icc 1 p.natDegree).sup' (Finset.nonempty_Icc.2 hdeg) fun ℓ =>
      (F ((m + 1) * p.natDegree)
          / ((p.natDegree.choose ℓ : ℝ) * (Q * F m) ^ (p.natDegree - ℓ)
              * F (m + 1) ^ ℓ * F ℓ)
          * (‖p.coeff (p.natDegree - ℓ)‖ / ‖p.leadingCoeff‖)) ^ ((ℓ : ℝ)⁻¹) := by
  set n := p.natDegree with hn
  have hFnn := Real.lucas_nonneg hF0 hF1 hrec hP hQ0.le
  have hp0 : p ≠ 0 := by
    intro h
    rw [hn, h, natDegree_zero] at hdeg
    exact absurd hdeg (by norm_num)
  have hlc : 0 < ‖p.leadingCoeff‖ := by simpa using leadingCoeff_ne_zero.2 hp0
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hNpos : ∀ ℓ ∈ Icc 1 n,
      0 < (n.choose ℓ : ℝ) * (Q * F (m' + 1)) ^ (n - ℓ) * F (m' + 1 + 1) ^ ℓ * F ℓ := by
    intro ℓ hℓ
    simp only [mem_Icc] at hℓ
    obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
    have hFm : 0 < F (m' + 1) := Real.lucas_pos hF0 hF1 hrec hP hQ0.le m'
    have hFm1 : 0 < F (m' + 1 + 1) := Real.lucas_pos hF0 hF1 hrec hP hQ0.le (m' + 1)
    have hFℓ : 0 < F (ℓ' + 1) := Real.lucas_pos hF0 hF1 hrec hP hQ0.le ℓ'
    have hch : 0 < (n.choose (ℓ' + 1) : ℝ) := by exact_mod_cast Nat.choose_pos hℓ.2
    positivity
  refine norm_le_of_isRoot_lucas hP hQ0.le hF0 hF1 hrec (m' + 1) hdeg ?_ ?_ hz
  · refine le_trans ?_ (Finset.le_sup' _ (mem_Icc.2 ⟨hdeg, le_rfl⟩))
    exact Real.rpow_nonneg (mul_nonneg (div_nonneg (hFnn _) (hNpos n (mem_Icc.2
      ⟨hdeg, le_rfl⟩)).le) (div_nonneg (norm_nonneg _) (norm_nonneg _))) _
  · intro ℓ hℓ
    have hℓ0 : ℓ ≠ 0 := by simp only [mem_Icc] at hℓ; omega
    have hle := Finset.le_sup' (s := Icc 1 n) (f := fun ℓ =>
      (F ((m' + 1 + 1) * n)
          / ((n.choose ℓ : ℝ) * (Q * F (m' + 1)) ^ (n - ℓ) * F (m' + 1 + 1) ^ ℓ * F ℓ)
          * (‖p.coeff (n - ℓ)‖ / ‖p.leadingCoeff‖)) ^ ((ℓ : ℝ)⁻¹)) hℓ
    exact mul_le_of_rpow_le (hFnn _) (hNpos ℓ hℓ) (norm_nonneg _) hlc hℓ0 hle

/-- **Theorem 1.2**, lower radius in closed form, for Lucas weights: every zero of `p` has
norm at least
`r₁ = min_{1 ≤ ℓ ≤ n} ((n.choose ℓ) * (Q * F m) ^ (n-ℓ) * F (m+1) ^ ℓ * F ℓ / F ((m+1)n)`
`      * ‖a 0 / a ℓ‖) ^ (1/ℓ)`.

The hypothesis `ha` (`a ℓ ≠ 0` for `1 ≤ ℓ ≤ n`) is the paper's standing assumption. -/
theorem lucas_inf_le_norm_of_isRoot (hP : 0 < P) (hQ0 : 0 < Q)
    (hF0 : F 0 = 0) (hF1 : F 1 = 1) (hrec : ∀ j, F (j + 2) = P * F (j + 1) + Q * F j)
    {m : ℕ} (hm : 1 ≤ m) (hdeg : 1 ≤ p.natDegree)
    (ha : ∀ ℓ ∈ Icc 1 p.natDegree, p.coeff ℓ ≠ 0) {z : K} (hz : p.IsRoot z) :
    (Icc 1 p.natDegree).inf' (Finset.nonempty_Icc.2 hdeg) (fun ℓ =>
      ((p.natDegree.choose ℓ : ℝ) * (Q * F m) ^ (p.natDegree - ℓ) * F (m + 1) ^ ℓ * F ℓ
          / F ((m + 1) * p.natDegree)
          * (‖p.coeff 0‖ / ‖p.coeff ℓ‖)) ^ ((ℓ : ℝ)⁻¹)) ≤ ‖z‖ := by
  set n := p.natDegree with hn
  have hFnn := Real.lucas_nonneg hF0 hF1 hrec hP hQ0.le
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨t, ht⟩ : ∃ t, (m' + 1 + 1) * n = t + 1 := ⟨(m' + 1 + 1) * n - 1, by
    have : 1 ≤ (m' + 1 + 1) * n := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega⟩
  have hD : 0 < F ((m' + 1 + 1) * n) := by
    rw [ht]; exact Real.lucas_pos hF0 hF1 hrec hP hQ0.le t
  have hr0 : 0 ≤ (Icc 1 n).inf' (Finset.nonempty_Icc.2 hdeg) (fun ℓ =>
      ((n.choose ℓ : ℝ) * (Q * F (m' + 1)) ^ (n - ℓ) * F (m' + 1 + 1) ^ ℓ * F ℓ
        / F ((m' + 1 + 1) * n) * (‖p.coeff 0‖ / ‖p.coeff ℓ‖)) ^ ((ℓ : ℝ)⁻¹)) := by
    refine Finset.le_inf' _ _ fun ℓ hℓ => ?_
    have hNnn :
        0 ≤ (n.choose ℓ : ℝ) * (Q * F (m' + 1)) ^ (n - ℓ) * F (m' + 1 + 1) ^ ℓ * F ℓ :=
      mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
        (pow_nonneg (mul_nonneg hQ0.le (hFnn _)) _)) (pow_nonneg (hFnn _) _)) (hFnn ℓ)
    exact Real.rpow_nonneg (mul_nonneg (div_nonneg hNnn hD.le)
      (div_nonneg (norm_nonneg _) (norm_nonneg _))) _
  refine le_norm_of_isRoot_lucas hP hQ0.le hF0 hF1 hrec (m' + 1) hdeg ?_ hz
  intro ℓ hℓ
  have hℓ0 : ℓ ≠ 0 := by simp only [mem_Icc] at hℓ; omega
  have hNnn :
      0 ≤ (n.choose ℓ : ℝ) * (Q * F (m' + 1)) ^ (n - ℓ) * F (m' + 1 + 1) ^ ℓ * F ℓ :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (mul_nonneg hQ0.le (hFnn _)) _)) (pow_nonneg (hFnn _) _)) (hFnn ℓ)
  have hc : 0 < ‖p.coeff ℓ‖ := norm_pos_iff.2 (ha ℓ hℓ)
  exact mul_rpow_le_of_le hD hNnn (norm_nonneg _) hc hℓ0 hr0 (Finset.inf'_le _ hℓ)

/-- **Theorem 1.2**, generalised: all zeros of `p` lie in the closed annulus
`r₁ ≤ ‖z‖ ≤ r₂` with the Lucas-weight radii (see `lucas_inf_le_norm_of_isRoot` and
`norm_le_lucas_sup_of_isRoot` for the two halves). -/
theorem isRoot_mem_lucas_annulus (hP : 0 < P) (hQ0 : 0 < Q)
    (hF0 : F 0 = 0) (hF1 : F 1 = 1) (hrec : ∀ j, F (j + 2) = P * F (j + 1) + Q * F j)
    {m : ℕ} (hm : 1 ≤ m) (hdeg : 1 ≤ p.natDegree)
    (ha : ∀ ℓ ∈ Icc 1 p.natDegree, p.coeff ℓ ≠ 0) {z : K} (hz : p.IsRoot z) :
    (Icc 1 p.natDegree).inf' (Finset.nonempty_Icc.2 hdeg) (fun ℓ =>
        ((p.natDegree.choose ℓ : ℝ) * (Q * F m) ^ (p.natDegree - ℓ) * F (m + 1) ^ ℓ * F ℓ
            / F ((m + 1) * p.natDegree)
            * (‖p.coeff 0‖ / ‖p.coeff ℓ‖)) ^ ((ℓ : ℝ)⁻¹)) ≤ ‖z‖ ∧
      ‖z‖ ≤ (Icc 1 p.natDegree).sup' (Finset.nonempty_Icc.2 hdeg) fun ℓ =>
        (F ((m + 1) * p.natDegree)
            / ((p.natDegree.choose ℓ : ℝ) * (Q * F m) ^ (p.natDegree - ℓ)
                * F (m + 1) ^ ℓ * F ℓ)
            * (‖p.coeff (p.natDegree - ℓ)‖ / ‖p.leadingCoeff‖)) ^ ((ℓ : ℝ)⁻¹) :=
  ⟨lucas_inf_le_norm_of_isRoot hP hQ0 hF0 hF1 hrec hm hdeg ha hz,
    norm_le_lucas_sup_of_isRoot hP hQ0 hF0 hF1 hrec hm hdeg hz⟩

/-- **Theorem 1.2** of the paper: the `k`-Fibonacci case `Q = 1` of
`isRoot_mem_lucas_annulus`. -/
theorem isRoot_mem_kFib_annulus {k : ℝ} (hk : 0 < k)
    (hF0 : F 0 = 0) (hF1 : F 1 = 1) (hrec : ∀ j, F (j + 2) = k * F (j + 1) + F j)
    {m : ℕ} (hm : 1 ≤ m) (hdeg : 1 ≤ p.natDegree)
    (ha : ∀ ℓ ∈ Icc 1 p.natDegree, p.coeff ℓ ≠ 0) {z : K} (hz : p.IsRoot z) :
    (Icc 1 p.natDegree).inf' (Finset.nonempty_Icc.2 hdeg) (fun ℓ =>
        ((p.natDegree.choose ℓ : ℝ) * F m ^ (p.natDegree - ℓ) * F (m + 1) ^ ℓ * F ℓ
            / F ((m + 1) * p.natDegree)
            * (‖p.coeff 0‖ / ‖p.coeff ℓ‖)) ^ ((ℓ : ℝ)⁻¹)) ≤ ‖z‖ ∧
      ‖z‖ ≤ (Icc 1 p.natDegree).sup' (Finset.nonempty_Icc.2 hdeg) fun ℓ =>
        (F ((m + 1) * p.natDegree)
            / ((p.natDegree.choose ℓ : ℝ) * F m ^ (p.natDegree - ℓ) * F (m + 1) ^ ℓ * F ℓ)
            * (‖p.coeff (p.natDegree - ℓ)‖ / ‖p.leadingCoeff‖)) ^ ((ℓ : ℝ)⁻¹) := by
  have h := isRoot_mem_lucas_annulus (P := k) (Q := 1) hk one_pos hF0 hF1
    (fun j => by rw [hrec j]; ring) hm hdeg ha hz
  simpa using h

/-- **Corollary 1.3** of the paper (the main result of Bidkham–Shashahani): the case `m = 4`
in the paper's indexing, where `F 3 = k ^ 2 + 1` and `F 4 = k ^ 3 + 2 * k`. -/
theorem isRoot_mem_kFib_annulus_four {k : ℝ} (hk : 0 < k)
    (hF0 : F 0 = 0) (hF1 : F 1 = 1) (hrec : ∀ j, F (j + 2) = k * F (j + 1) + F j)
    (hdeg : 1 ≤ p.natDegree)
    (ha : ∀ ℓ ∈ Icc 1 p.natDegree, p.coeff ℓ ≠ 0) {z : K} (hz : p.IsRoot z) :
    (Icc 1 p.natDegree).inf' (Finset.nonempty_Icc.2 hdeg) (fun ℓ =>
        ((p.natDegree.choose ℓ : ℝ) * (k ^ 2 + 1) ^ (p.natDegree - ℓ)
            * (k ^ 3 + 2 * k) ^ ℓ * F ℓ / F (4 * p.natDegree)
            * (‖p.coeff 0‖ / ‖p.coeff ℓ‖)) ^ ((ℓ : ℝ)⁻¹)) ≤ ‖z‖ ∧
      ‖z‖ ≤ (Icc 1 p.natDegree).sup' (Finset.nonempty_Icc.2 hdeg) fun ℓ =>
        (F (4 * p.natDegree)
            / ((p.natDegree.choose ℓ : ℝ) * (k ^ 2 + 1) ^ (p.natDegree - ℓ)
                * (k ^ 3 + 2 * k) ^ ℓ * F ℓ)
            * (‖p.coeff (p.natDegree - ℓ)‖ / ‖p.leadingCoeff‖)) ^ ((ℓ : ℝ)⁻¹) := by
  have h := isRoot_mem_kFib_annulus hk hF0 hF1 hrec (m := 3) (by norm_num) hdeg ha hz
  simpa only [Real.kFib_three hF0 hF1 hrec, Real.kFib_four hF0 hF1 hrec,
    show (3 : ℕ) + 1 = 4 from rfl] using h

/-- **Remark 1.4**: Diaz-Barrero's classical Fibonacci annulus, the case `k = 1`, `m = 4`
(paper indexing) of Theorem 1.2.  `Nat.fib` satisfies all the hypotheses, so no new
definition is required. -/
theorem isRoot_mem_fib_annulus (hdeg : 1 ≤ p.natDegree)
    (ha : ∀ ℓ ∈ Icc 1 p.natDegree, p.coeff ℓ ≠ 0) {z : K} (hz : p.IsRoot z) :
    (Icc 1 p.natDegree).inf' (Finset.nonempty_Icc.2 hdeg) (fun ℓ =>
        ((p.natDegree.choose ℓ : ℝ) * 2 ^ (p.natDegree - ℓ) * 3 ^ ℓ * Nat.fib ℓ
            / Nat.fib (4 * p.natDegree)
            * (‖p.coeff 0‖ / ‖p.coeff ℓ‖)) ^ ((ℓ : ℝ)⁻¹)) ≤ ‖z‖ ∧
      ‖z‖ ≤ (Icc 1 p.natDegree).sup' (Finset.nonempty_Icc.2 hdeg) fun ℓ =>
        ((Nat.fib (4 * p.natDegree) : ℝ)
            / ((p.natDegree.choose ℓ : ℝ) * 2 ^ (p.natDegree - ℓ) * 3 ^ ℓ * Nat.fib ℓ)
            * (‖p.coeff (p.natDegree - ℓ)‖ / ‖p.leadingCoeff‖)) ^ ((ℓ : ℝ)⁻¹) := by
  have f3 : Nat.fib 3 = 2 := by decide
  have f4 : Nat.fib 4 = 3 := by decide
  have h := isRoot_mem_kFib_annulus (k := 1) (F := fun j => (Nat.fib j : ℝ)) one_pos
    (by exact_mod_cast Nat.fib_zero) (by exact_mod_cast Nat.fib_one)
    (fun j => by push_cast [Nat.fib_add_two]; ring) (m := 3) (by norm_num) hdeg ha hz
  simpa only [show (3 : ℕ) + 1 = 4 from rfl, f3, f4, Nat.cast_ofNat] using h

end Annulus

end Polynomial
