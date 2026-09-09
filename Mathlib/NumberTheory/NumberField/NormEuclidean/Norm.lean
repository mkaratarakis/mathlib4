/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RingTheory.Polynomial.Nilpotent
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Norms modulo a totally ramified element

Let `B` be a free `A`-algebra with basis indexed by a finite type of cardinality `n`, and let
`p : A` be an element such that `A ⧸ (p)` is reduced (for instance, a prime element).  If `t : B`
satisfies `p ∣ t ^ n` in `B`, then multiplication by `t` is nilpotent modulo `p`, so it has
characteristic polynomial `X ^ n` there, and therefore

`Algebra.norm A (x + t) ≡ x ^ n  [mod p]`   for every `x : A`.

The intended application is a prime number `p` which is totally ramified in a number field `K` of
degree `n`, say `(p) = 𝔭 ^ n`: taking `t ∈ 𝔭` gives `p ∣ t ^ n`, so the norm map induces the
`n`-th power map on the residue field `𝓞 K ⧸ 𝔭 = ZMod p`.  This is the key input to Heilbronn's
criterion; it replaces the classical argument through the conjugates of an element, which only
makes sense inside a Galois closure.

## Main results

* `Algebra.dvd_norm_add_sub_pow`: the congruence `norm A (x + t) ≡ x ^ n [mod p]` above.
* `Algebra.dvd_norm_sub_pow`: the same congruence for `ρ` congruent to `x` modulo an ideal `I`
  with `I ^ n ≤ (p)`, which is the form used for a totally ramified prime.
-/

public section

open Matrix Polynomial

namespace Algebra

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- Let `B` be a free `A`-algebra with basis indexed by a finite type of cardinality `n`, let
`p : A` be such that `A ⧸ (p)` is reduced, and let `t : B` satisfy `p ∣ t ^ n`.  Then
`norm A (x + t) ≡ x ^ n` modulo `p`, for every `x : A`.

Multiplication by `t` is nilpotent modulo `p`, so its characteristic polynomial there is `X ^ n`,
and the determinant of `x + t` reduces to `x ^ n`. -/
theorem dvd_norm_add_sub_pow {ι : Type*} [Fintype ι] (b : Module.Basis ι A B) {p : A}
    (hp : IsReduced (A ⧸ Ideal.span {p})) {t : B} (ht : algebraMap A B p ∣ t ^ Fintype.card ι)
    (x : A) : p ∣ Algebra.norm A (algebraMap A B x + t) - x ^ Fintype.card ι := by
  classical
  have : IsReduced (A ⧸ Ideal.span {p}) := hp
  set φ : A →+* A ⧸ Ideal.span {p} := Ideal.Quotient.mk _ with hφ
  have hp0 : φ p = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self p)
  set N : Matrix ι ι (A ⧸ Ideal.span {p}) := φ.mapMatrix (leftMulMatrix b t) with hN
  -- `N` is nilpotent, because `p ∣ t ^ n`
  have hNpow : N ^ Fintype.card ι = 0 := by
    obtain ⟨y, hy⟩ := ht
    rw [hN, ← map_pow, ← map_pow, hy, map_mul, map_mul, AlgHom.commutes]
    convert zero_mul _
    ext i j
    simp [Matrix.algebraMap_eq_diagonal, RingHom.mapMatrix_apply, Matrix.diagonal, hp0,
      apply_ite φ]
  have hNnil : IsNilpotent (-N) := IsNilpotent.neg ⟨_, hNpow⟩
  -- hence its characteristic polynomial is `X ^ n`
  have hchar : (-N).charpoly = X ^ Fintype.card ι := by
    have h := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hNnil
    have h0 : (-N).charpoly - X ^ Fintype.card ι = 0 := by
      ext k
      simpa using IsNilpotent.eq_zero ((Polynomial.isNilpotent_iff.1 h) k)
    linear_combination (norm := ring_nf) h0
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero,
    Algebra.norm_eq_matrix_det b, RingHom.map_det]
  have hsplit : φ.mapMatrix (leftMulMatrix b (algebraMap A B x + t)) =
      Matrix.scalar ι (φ x) - (-N) := by
    rw [map_add, map_add, sub_neg_eq_add, hN]
    congr 1
    rw [AlgHom.commutes]
    ext i j
    simp [Matrix.algebraMap_eq_diagonal, RingHom.mapMatrix_apply, Matrix.diagonal,
      Matrix.scalar, apply_ite φ]
  rw [hsplit, ← Matrix.eval_charpoly, hchar]
  simp [hφ]

/-- Version of `Algebra.dvd_norm_add_sub_pow` for an ideal `I` with `I ^ n ≤ (p)`: if `ρ` is
congruent to `x : A` modulo `I`, then `norm A ρ ≡ x ^ n` modulo `p`.

For a prime `p` totally ramified in a number field `K`, so that `(p) = 𝔭 ^ n`, this says that the
norm map induces the `n`-th power map on the residue field at `𝔭`. -/
theorem dvd_norm_sub_pow {ι : Type*} [Fintype ι] (b : Module.Basis ι A B) {p : A}
    (hp : IsReduced (A ⧸ Ideal.span {p})) {I : Ideal B}
    (hI : I ^ Fintype.card ι ≤ Ideal.span {algebraMap A B p}) {ρ : B} {x : A}
    (h : ρ - algebraMap A B x ∈ I) : p ∣ Algebra.norm A ρ - x ^ Fintype.card ι := by
  classical
  have hdvd : algebraMap A B p ∣ (ρ - algebraMap A B x) ^ Fintype.card ι :=
    Ideal.mem_span_singleton.1 (hI (Ideal.pow_mem_pow h _))
  simpa using dvd_norm_add_sub_pow b hp hdvd x

variable (A B) in
/-- The rank-indexed form of `Algebra.dvd_norm_sub_pow` for a finite free algebra. -/
theorem dvd_norm_sub_pow_finrank [Nontrivial A] [Module.Free A B] [Module.Finite A B] {p : A}
    (hp : IsReduced (A ⧸ Ideal.span {p})) {I : Ideal B}
    (hI : I ^ Module.finrank A B ≤ Ideal.span {algebraMap A B p}) {ρ : B} {x : A}
    (h : ρ - algebraMap A B x ∈ I) : p ∣ Algebra.norm A ρ - x ^ Module.finrank A B := by
  classical
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex A B) = Module.finrank A B :=
    (Module.finrank_eq_card_chooseBasisIndex A B).symm
  have := dvd_norm_sub_pow (Module.Free.chooseBasis A B) hp (I := I) (by rwa [hcard]) h
  rwa [hcard] at this

end Algebra
