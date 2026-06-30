/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.Ring.SumsOfSquares
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Ring.Semireal.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

set_option linter.style.show false
/-!
# Hilbert's 17th problem for matrices (Hillar–Nie)

This file works towards the matrix analogue of Artin's theorem, following the short elementary
proof of Hillar and Nie, *An elementary and constructive solution to Hilbert's 17th problem for
matrices* (arXiv:math/0610388):

> **Theorem 3.** Let `F` be a (formally) real field and `A` a symmetric matrix over `F`.
> If every principal minor of `A` is a sum of squares in `F`, then `A` is a sum of squares of
> symmetric matrices over `F`.

## Structure of the proof and current status

The Hillar–Nie argument splits cleanly into a *pure algebra* part and a *real-closed-field* part.

**Pure algebra (proved here, no real-closure input needed).**
Working inside the commutative subalgebra `F[A] = Algebra.adjoin F {A}` (every element of which is a
*symmetric* matrix, since it is a polynomial in the symmetric matrix `A`), the final identity (1)
of the paper exhibits `A = B * C` with `B` and `C` sums of squares *in `F[A]`*. As products of
sums of squares in a commutative ring are again sums of squares (`IsSumSq.mul`), `A` itself is a
sum of squares in `F[A]`, hence a sum of squares of symmetric matrices.  This reduction is
captured by `Matrix.isSumSqSymm_of_factor`.

**Real-closed-field input.**
Producing the factorisation `A = B * C` is exactly Lemma 4 of the paper: the minimal polynomial of
`A` has the form `t^m - a_{m-1} t^{m-1} + ⋯ + (-1)^m a_0` with every `aᵢ` a sum of squares and
`a₁ ≠ 0`. Its proof — formalised in `Hilbert17Blueprint.lean` and assembled in `Hilbert17Lemma4.lean`
— uses the easy Artin–Schreier characterisation, existence of a real closure of an ordered field,
and the algebraic spectral theorem over a real closed field.

## Main definitions

* `Matrix.IsSumSqSymm A` : `A` is a (finite) sum of squares of symmetric matrices.

## Main results

* `Matrix.isSumSqSymm_of_factor` : the pure-algebra engine turning a factorisation `A = B * C` with
  `B`, `C` sums of squares in `F[A]` into `A.IsSumSqSymm`.

## References

* C. J. Hillar, J. Nie, *An elementary and constructive solution to Hilbert's 17th problem for
  matrices*, Proc. Amer. Math. Soc. 136 (2008), arXiv:math/0610388.
-/

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {F : Type*} [Field F]

/-- `A` is a sum of squares of symmetric matrices: there is a finite list of symmetric matrices
whose squares sum to `A`. -/
def IsSumSqSymm (A : Matrix n n F) : Prop :=
  ∃ l : List (Matrix n n F), (∀ B ∈ l, B.IsSymm) ∧ A = (l.map (· ^ 2)).sum

namespace IsSumSqSymm

/-- The zero matrix is a sum of squares of symmetric matrices (the empty sum). -/
theorem zero : IsSumSqSymm (0 : Matrix n n F) := ⟨[], by simp, by simp⟩

/-- A square of a symmetric matrix is a sum of squares of symmetric matrices. -/
theorem of_sq {B : Matrix n n F} (hB : B.IsSymm) : IsSumSqSymm (B ^ 2) :=
  ⟨[B], by intro B' hB'; rw [List.mem_singleton] at hB'; exact hB' ▸ hB, by simp⟩

/-- Sums of squares of symmetric matrices are closed under addition (concatenate the lists). -/
theorem add {A A' : Matrix n n F} (hA : IsSumSqSymm A) (hA' : IsSumSqSymm A') :
    IsSumSqSymm (A + A') := by
  obtain ⟨l, hl, rfl⟩ := hA
  obtain ⟨l', hl', rfl⟩ := hA'
  refine ⟨l ++ l', ?_, ?_⟩
  · intro B hB
    rcases List.mem_append.1 hB with h | h
    · exact hl B h
    · exact hl' B h
  · rw [List.map_append, List.sum_append]

end IsSumSqSymm

/-- Every element of `F[A] = Algebra.adjoin F {A}` is symmetric, because it is a polynomial in the
symmetric matrix `A` and the subalgebra is commutative (so products of symmetric elements stay
symmetric). -/
theorem isSymm_of_mem_adjoin {A : Matrix n n F} (hA : A.IsSymm) {x : Matrix n n F}
    (hx : x ∈ Algebra.adjoin F ({A} : Set (Matrix n n F))) : x.IsSymm := by
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
      rw [Set.mem_singleton_iff] at hy
      exact hy ▸ hA
  | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one]
      show (r • (1 : Matrix n n F))ᵀ = r • 1
      rw [Matrix.transpose_smul, Matrix.transpose_one]
  | add x y hx hy ihx ihy =>
      show (x + y)ᵀ = x + y
      rw [Matrix.transpose_add, ihx.eq, ihy.eq]
  | mul x y hx hy ihx ihy =>
      -- `x` and `y` commute as elements of the commutative ring `F[A]`.
      have hcomm : x * y = y * x := by
        have h := mul_comm (⟨x, hx⟩ : Algebra.adjoin F ({A} : Set (Matrix n n F))) ⟨y, hy⟩
        simpa using congrArg (Subtype.val) h
      show (x * y)ᵀ = x * y
      rw [Matrix.transpose_mul, ihx.eq, ihy.eq, hcomm]

/-- Bridge: a sum of squares *inside the subalgebra* `F[A]` is, as a matrix, a sum of squares of
symmetric matrices. -/
theorem isSumSqSymm_of_isSumSq_adjoin {A : Matrix n n F} (hA : A.IsSymm)
    {x : Algebra.adjoin F ({A} : Set (Matrix n n F))} (hx : IsSumSq x) :
    (x : Matrix n n F).IsSumSqSymm := by
  induction hx with
  | zero => simpa using IsSumSqSymm.zero
  | sq_add a hs ih =>
      rename_i s
      have ha : ((a : Matrix n n F)).IsSymm := isSymm_of_mem_adjoin hA a.2
      have hcoe : ((a * a + s : Algebra.adjoin F ({A} : Set (Matrix n n F))) : Matrix n n F)
          = (a : Matrix n n F) ^ 2 + (s : Matrix n n F) := by
        simp [Subalgebra.coe_add, Subalgebra.coe_mul, sq]
      rw [hcoe]
      exact (IsSumSqSymm.of_sq ha).add ih

/-- **Pure-algebra engine of Hillar–Nie.**
If a symmetric matrix `A` factors as `A = B * C` with `B`, `C` in the commutative subalgebra `F[A]`
generated by `A`, and both `B` and `C` are sums of squares in `F[A]`, then `A` is a sum of squares
of symmetric matrices. This step needs no input from the theory of real closed fields. -/
theorem isSumSqSymm_of_factor {A : Matrix n n F} (hA : A.IsSymm)
    {B C : Algebra.adjoin F ({A} : Set (Matrix n n F))}
    (hB : IsSumSq B) (hC : IsSumSq C)
    (hfac : (A : Matrix n n F) = (B : Matrix n n F) * C) :
    A.IsSumSqSymm := by
  have hBC : IsSumSq (B * C) := hB.mul hC
  have hbridge :
      ((B * C : Algebra.adjoin F ({A} : Set (Matrix n n F))) : Matrix n n F).IsSumSqSymm :=
    isSumSqSymm_of_isSumSq_adjoin hA hBC
  rwa [Subalgebra.coe_mul, ← hfac] at hbridge

open Polynomial in
/-- **The signed coefficients of the characteristic polynomial are sums of squares**, when all
principal minors are. This is immediate from `Matrix.charpoly_coeff_eq_sum_minors`
(`(-1)ᵏ · χ_A.coeff (n - k) = ∑_{|s|=k} minorₛ A`) and closure of sums of squares under `+`.

This **replaces the entire spectral detour** (no real closed fields, no spectral theorem, no real
closure, no algebraic FTA): the coefficient shape that Hillar–Nie's identity (1) consumes is
available directly over the formally real field `F`. -/
theorem isSumSq_signed_charpoly_coeff {A : Matrix n n F}
    (hminor : ∀ s : Finset n,
      IsSumSq (A.submatrix (fun i : s => (i : n)) (fun i : s => (i : n))).det)
    (k : ℕ) (hk : k ≤ Fintype.card n) :
    IsSumSq ((-1) ^ k * A.charpoly.coeff (Fintype.card n - k)) := by
  rw [Matrix.charpoly_coeff_eq_sum_minors A k hk, ← mul_assoc, ← pow_add, ← two_mul, pow_mul,
    neg_one_sq, one_pow, one_mul]
  exact IsSumSq.sum (fun s _ => hminor s)

end Matrix
