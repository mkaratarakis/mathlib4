/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.Hilbert17Matrices
import Mathlib.NumberTheory.Transcendental.Hilbert17Blueprint
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Hillar–Nie Lemma 4 and the identity (1)

This file formalises Hillar–Nie's **identity (1)** — the factorisation `A = B · C` of a symmetric
matrix into sums of squares in the commutative algebra `F[A]` — and **Lemma 4**, following the paper
*An elementary and constructive solution to Hilbert's 17th problem for matrices*. The identity-(1)
half is real-closure-free; Lemma 4's coefficient input comes from the real-closed-field spectral
theory in `Hilbert17Blueprint.lean`.

## The architecture, and where real closed fields are genuinely needed

The proof splits cleanly into a **real-closure-free factorisation** (the identity (1)) and a
**real-closed-field input** (Lemma 4's coefficient shape):

* **Factorisation (real-closure-free).** Given the minimal polynomial in Lemma-4 shape
  `p(t) = tᵐ - a_{m-1}tᵐ⁻¹ + ⋯ + (-1)ᵐ a₀` with every `aᵢ` a sum of squares and `a₁ ≠ 0`, set
  `B = Aᵐ⁻¹ + a_{m-2}Aᵐ⁻³ + ⋯ + a₁ I` (the odd-power part) and `R = a_{m-1}Aᵐ⁻¹ + ⋯ + a₀ I`. Then
  `A·B = R` (Cayley–Hamilton, parity split), `B` is a sum of squares in `F[A]`, `B` is invertible
  — and this is the one place the paper uses real closures, *but it is avoidable*: `B` is invertible
  directly over the formally real field `F`, because `v ⬝ᵥ B *ᵥ v = a₁·(v ⬝ᵥ v) + (sum of squares)`,
  so `B v = 0` forces `a₁·(v ⬝ᵥ v) = 0` (`isSumSq_eq_zero_of_add`) hence `v = 0`
  (`dotProduct_self_eq_zero_semireal`). Finally `A = B·(B⁻²R)` with `B⁻²R` a sum of squares.
* **Lemma 4 (needs real closed fields).** That `p` has the displayed shape — each `aᵢ` a sum of
  squares and `a₁ ≠ 0` — is exactly where real-closed-field theory enters: for every ordering of
  `F`, pass to a real closure `R ⊇ F` (Khovanov, **Lemma 34**, Sturm-free: Zorn + Theorem 28), where
  `A` is diagonalisable with nonnegative eigenvalues (spectral theorem over a real closed field), so
  `aᵢ ≥ 0` and `p` is squarefree; then `aᵢ` nonnegative in every ordering ⇒ a sum of squares (easy
  Artin–Schreier, `RingPreordering.isSumSq_of_forall_mem`).

The two real-closed-field inputs (real-closure existence; the spectral theorem over a real closed
field) are **not yet in Mathlib**; they are the genuine remaining work, mapped to Khovanov's
blueprint. Everything else below is real-closure-free.

## Pieces

* `isSumSq_eq_zero_of_add`, `dotProduct_self_eq_zero_semireal` — formally-real workhorses (proved).
* `isUnit_det_of_dotProduct_self_imp` — a symmetric form that is "anisotropic" is invertible.
  **Proved.**
* `signedCoeff`, `B`, `R` — the data of identity (1).
* `evalEvenPow_isSumSq` — an even-power polynomial in `A` with sum-of-squares coefficients is a sum
  of squares in `F[A]`.  ⇒ `B`, `R` are sums of squares.
* `A_mul_B_eq_R` — the Cayley–Hamilton parity identity.
* `B_dotProduct_self` — `v ⬝ᵥ B *ᵥ v = a₁·(v ⬝ᵥ v) + (sum of squares)`.
* `B_isUnit` — `B` invertible (from the previous two + the workhorses). **Real-closure-free.**
* `exists_factor_of_minpoly_shape` — identity (1): assembles `A = B·C`.
* `minpoly_lemma4` — Lemma 4 (the real-closed-field input).
-/

open Matrix Polynomial

namespace Hilbert17Lemma4

variable {F : Type*} [Field F] [IsSemireal F]

/-! ### Anisotropic symmetric forms are invertible (real-closure-free) -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A symmetric matrix whose quadratic form is anisotropic (`v ⬝ᵥ M *ᵥ v = 0 → v = 0`) is
invertible. This replaces the paper's real-closure argument for invertibility of `B`. -/
theorem isUnit_det_of_dotProduct_self_imp {M : Matrix n n F}
    (h : ∀ v : n → F, v ⬝ᵥ M *ᵥ v = 0 → v = 0) : IsUnit M.det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  exact hv0 (h v (by rw [hMv, dotProduct_zero]))

/-! ### The identity (1) assembly (real-closure-free) -/

/-- **Identity (1), assembled.** If `A · B = R` in the commutative algebra `F[A]`, with `B` and `R`
sums of squares and `B` a unit, then `A` is a sum of squares of symmetric matrices: `A = B · C` with
`C = B⁻² R` a sum of squares. This is the real-closure-free core of Hillar–Nie's Theorem 3 (given
the Lemma-4 data). **Proved.** -/
theorem factor_of_relation {A : Matrix n n F} (hA : A.IsSymm)
    {B R : Algebra.adjoin F ({A} : Set (Matrix n n F))}
    (hrel : (⟨A, Algebra.self_mem_adjoin_singleton F A⟩ :
      Algebra.adjoin F ({A} : Set (Matrix n n F))) * B = R)
    (hB : IsSumSq B) (hR : IsSumSq R) (hBu : IsUnit B) :
    A.IsSumSqSymm := by
  obtain ⟨u, rfl⟩ := hBu
  set Ae : Algebra.adjoin F ({A} : Set (Matrix n n F)) :=
    ⟨A, Algebra.self_mem_adjoin_singleton F A⟩ with hAe
  have hAeq : (↑u * ((↑u⁻¹ * ↑u⁻¹) * R) :
      Algebra.adjoin F ({A} : Set (Matrix n n F))) = Ae := by
    rw [show (↑u * ((↑u⁻¹ * ↑u⁻¹) * R) :
        Algebra.adjoin F ({A} : Set (Matrix n n F)))
        = (↑u * ↑u⁻¹) * (↑u⁻¹ * R) by ring, Units.mul_inv, one_mul, ← hrel,
      show (↑u⁻¹ * (Ae * ↑u) :
        Algebra.adjoin F ({A} : Set (Matrix n n F))) = (↑u⁻¹ * ↑u) * Ae by ring,
      Units.inv_mul, one_mul]
  refine Matrix.isSumSqSymm_of_factor hA (B := (u : _)) (C := (↑u⁻¹ * ↑u⁻¹) * R)
    hB ((IsSumSq.mul_self _).mul hR) ?_
  have := congrArg (Subalgebra.val _) hAeq
  simpa using this.symm

/-! ### The data of identity (1): `B`, `R`, and the Cayley–Hamilton relation (real-closure-free) -/

/-- The signed coefficient `aᵢ = (-1)^(m-i)·(minpoly).coeff i` of the minimal polynomial of `A`
(`m = deg minpoly`). Lemma 4 asserts these are sums of squares with `a₁ ≠ 0`. -/
noncomputable def signedCoeff (A : Matrix n n F) (i : ℕ) : F :=
  (-1 : F) ^ ((minpoly F A).natDegree - i) * (minpoly F A).coeff i

/-- `B = ∑_{i odd} aᵢ Aⁱ⁻¹`, the odd-power part of identity (1). -/
noncomputable def factorB (A : Matrix n n F) : Matrix n n F :=
  ∑ i ∈ (Finset.range ((minpoly F A).natDegree + 1)).filter (fun i => ¬ Even i),
    signedCoeff A i • A ^ (i - 1)

/-- `R = ∑_{i even} aᵢ Aⁱ`, the even-power part of identity (1). -/
noncomputable def factorR (A : Matrix n n F) : Matrix n n F :=
  ∑ i ∈ (Finset.range ((minpoly F A).natDegree + 1)).filter (fun i => Even i),
    signedCoeff A i • A ^ i

/-- **The Cayley–Hamilton parity identity** `A · B = R`. Uniform in the parity of `m = deg minpoly`,
since `∑ᵢ (-1)ⁱ aᵢ Aⁱ = (-1)ᵐ · (minpoly A)(A) = 0` by Cayley–Hamilton, and splitting by the parity
of `i` equates the even-power and odd-power parts. **Proved, real-closure-free.** -/
theorem A_mul_factorB_eq_factorR (A : Matrix n n F) : A * factorB A = factorR A := by
  simp only [factorB, factorR, signedCoeff]
  set m := (minpoly F A).natDegree with hm
  set sc : ℕ → F := fun i => (-1 : F) ^ (m - i) * (minpoly F A).coeff i with hsc
  have hCH : ∑ i ∈ Finset.range (m + 1), (minpoly F A).coeff i • A ^ i = 0 := by
    have := minpoly.aeval F A; rwa [aeval_eq_sum_range] at this
  have hterm : ∀ i ∈ Finset.range (m + 1),
      ((-1 : F) ^ i • (sc i • A ^ i)) = (-1 : F) ^ m • ((minpoly F A).coeff i • A ^ i) := by
    intro i hi
    have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    simp only [hsc, smul_smul]
    rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hi']
  have h0 : ∑ i ∈ Finset.range (m + 1), ((-1 : F) ^ i • (sc i • A ^ i)) = 0 := by
    rw [Finset.sum_congr rfl hterm, ← Finset.smul_sum, hCH, smul_zero]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (m + 1)) (fun i => Even i)] at h0
  have hEven : ∑ i ∈ (Finset.range (m + 1)).filter (fun i => Even i),
      ((-1 : F) ^ i • (sc i • A ^ i)) = ∑ i ∈ (Finset.range (m + 1)).filter (fun i => Even i),
        sc i • A ^ i :=
    Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.1 hi).2.neg_one_pow, one_smul])
  have hOdd : ∑ i ∈ (Finset.range (m + 1)).filter (fun i => ¬ Even i),
      ((-1 : F) ^ i • (sc i • A ^ i)) = -∑ i ∈ (Finset.range (m + 1)).filter (fun i => ¬ Even i),
        sc i • A ^ i := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i hi => by
      rw [(Nat.not_even_iff_odd.1 (Finset.mem_filter.1 hi).2).neg_one_pow, neg_one_smul])
  rw [hEven, hOdd] at h0
  rw [Finset.mul_sum]
  have hLHS : ∀ i ∈ (Finset.range (m + 1)).filter (fun i => ¬ Even i),
      A * (sc i • A ^ (i - 1)) = sc i • A ^ i := fun i hi => by
    have hi1 : 1 ≤ i := (Nat.not_even_iff_odd.1 (Finset.mem_filter.1 hi).2).pos
    rw [mul_smul_comm, ← pow_succ', Nat.sub_add_cancel hi1]
  rw [Finset.sum_congr rfl hLHS]
  exact (add_neg_eq_zero.1 h0).symm

/-! ### `B` and `R` as elements of the commutative algebra `F[A]` (real-closure-free) -/

/-- `B = ∑_{i odd} aᵢ Aⁱ⁻¹` as an element of the subalgebra `F[A]`. -/
noncomputable def factorBe (A : Matrix n n F) : Algebra.adjoin F ({A} : Set (Matrix n n F)) :=
  ∑ i ∈ (Finset.range ((minpoly F A).natDegree + 1)).filter (fun i => ¬ Even i),
    signedCoeff A i • (⟨A, Algebra.self_mem_adjoin_singleton F A⟩ :
      Algebra.adjoin F ({A} : Set (Matrix n n F))) ^ (i - 1)

/-- `R = ∑_{i even} aᵢ Aⁱ` as an element of the subalgebra `F[A]`. -/
noncomputable def factorRe (A : Matrix n n F) : Algebra.adjoin F ({A} : Set (Matrix n n F)) :=
  ∑ i ∈ (Finset.range ((minpoly F A).natDegree + 1)).filter (fun i => Even i),
    signedCoeff A i • (⟨A, Algebra.self_mem_adjoin_singleton F A⟩ :
      Algebra.adjoin F ({A} : Set (Matrix n n F))) ^ i

@[simp] theorem val_factorBe (A : Matrix n n F) :
    (factorBe A : Matrix n n F) = factorB A := by
  rw [factorBe, factorB, AddSubmonoidClass.coe_finsetSum]
  exact Finset.sum_congr rfl (fun i _ => by
    rw [Subalgebra.coe_smul, SubmonoidClass.coe_pow])

@[simp] theorem val_factorRe (A : Matrix n n F) :
    (factorRe A : Matrix n n F) = factorR A := by
  rw [factorRe, factorR, AddSubmonoidClass.coe_finsetSum]
  exact Finset.sum_congr rfl (fun i _ => by
    rw [Subalgebra.coe_smul, SubmonoidClass.coe_pow])

/-! ### Sum-of-squares structure of `B` and `R` (real-closure-free) -/

/-- A ring-hom (here `algebraMap`) carries a sum of squares to a sum of squares. -/
theorem isSumSq_algebraMap {S : Type*} [CommSemiring S] [Algebra F S] {c : F}
    (hc : IsSumSq c) : IsSumSq (algebraMap F S c) := by
  induction hc with
  | zero => simpa using IsSumSq.zero
  | sq_add a hs ih => rw [map_add, map_mul]; exact (IsSumSq.mul_self _).add ih

/-- `R` is a sum of squares in `F[A]`: every power occurring is even, `A^(2k) = (Aᵏ)²`, and the
coefficients are sums of squares. -/
theorem factorRe_isSumSq (A : Matrix n n F) (hsos : ∀ i, IsSumSq (signedCoeff A i)) :
    IsSumSq (factorRe A) := by
  rw [factorRe]
  refine IsSumSq.sum (fun i hi => ?_)
  rw [Algebra.smul_def]
  refine (isSumSq_algebraMap (hsos i)).mul ?_
  obtain ⟨k, hk⟩ := (Finset.mem_filter.1 hi).2
  rw [hk, pow_add]
  exact IsSumSq.mul_self _

/-- `B` is a sum of squares in `F[A]`: every odd index `i` gives an even power `A^(i-1) = (Aᵏ)²`. -/
theorem factorBe_isSumSq (A : Matrix n n F) (hsos : ∀ i, IsSumSq (signedCoeff A i)) :
    IsSumSq (factorBe A) := by
  rw [factorBe]
  refine IsSumSq.sum (fun i hi => ?_)
  rw [Algebra.smul_def]
  refine (isSumSq_algebraMap (hsos i)).mul ?_
  obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.1 (Finset.mem_filter.1 hi).2
  rw [hk, show 2 * k + 1 - 1 = k + k by omega, pow_add]
  exact IsSumSq.mul_self _

/-- The relation `A · B = R` lifted into the subalgebra `F[A]`. -/
theorem Ae_mul_factorBe_eq_factorRe (A : Matrix n n F) :
    (⟨A, Algebra.self_mem_adjoin_singleton F A⟩ :
      Algebra.adjoin F ({A} : Set (Matrix n n F))) * factorBe A = factorRe A := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, val_factorBe, val_factorRe]
  exact A_mul_factorB_eq_factorR A

/-- The quadratic form of an *even* power of a symmetric matrix is a genuine self dot product:
`v ⬝ᵥ A^(2k) *ᵥ v = (A^k v) ⬝ᵥ (A^k v)`. -/
theorem dotProduct_self_even_pow {A : Matrix n n F} (hA : A.IsSymm) (k : ℕ) (v : n → F) :
    v ⬝ᵥ A ^ (2 * k) *ᵥ v = (A ^ k *ᵥ v) ⬝ᵥ (A ^ k *ᵥ v) := by
  rw [two_mul, pow_add, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose, (hA.pow k).eq]

omit [IsSemireal F] [DecidableEq n] in
/-- A self dot product is a sum of squares (`v ⬝ᵥ v = ∑ vᵢ²`). -/
theorem isSumSq_dotProduct_self (v : n → F) : IsSumSq (v ⬝ᵥ v) := by
  rw [dotProduct]
  exact IsSumSq.sum (fun i _ => IsSumSq.mul_self (v i))

/-- The contribution of a single odd-index term of `B` to the quadratic form is
`aᵢ · ((A^k v) ⬝ᵥ (A^k v))` with `k = (i-1)/2` — a sum of squares times `aᵢ`. -/
theorem dotProduct_factorB_term {A : Matrix n n F} (hA : A.IsSymm) {i : ℕ} (hi : ¬ Even i)
    (v : n → F) :
    v ⬝ᵥ (signedCoeff A i • A ^ (i - 1)) *ᵥ v
      = signedCoeff A i * ((A ^ ((i - 1) / 2) *ᵥ v) ⬝ᵥ (A ^ ((i - 1) / 2) *ᵥ v)) := by
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul]
  congr 1
  have he : Even (i - 1) := Nat.Odd.sub_odd (Nat.not_even_iff_odd.1 hi) odd_one
  conv_lhs => rw [← Nat.two_mul_div_two_of_even he]
  exact dotProduct_self_even_pow hA _ v

/-- **`B` is anisotropic** (real-closure-free): `v ⬝ᵥ B *ᵥ v = 0 → v = 0`, when each `aᵢ` is a sum
of squares and `a₁ ≠ 0`. Writing the quadratic form as `a₁·(v ⬝ᵥ v) + (sum of squares)`, a vanishing
forces `a₁·(v ⬝ᵥ v) = 0` (`isSumSq_eq_zero_of_add`), hence `v ⬝ᵥ v = 0` and `v = 0`. -/
theorem factorB_anisotropic {A : Matrix n n F} (hA : A.IsSymm)
    (hsos : ∀ i, IsSumSq (signedCoeff A i)) (ha1 : signedCoeff A 1 ≠ 0) (v : n → F)
    (hv : v ⬝ᵥ factorB A *ᵥ v = 0) : v = 0 := by
  set s := (Finset.range ((minpoly F A).natDegree + 1)).filter (fun i => ¬ Even i) with hs
  set g : ℕ → F := fun i => signedCoeff A i * ((A ^ ((i - 1) / 2) *ᵥ v) ⬝ᵥ (A ^ ((i - 1) / 2) *ᵥ v))
    with hg
  -- rewrite the quadratic form as `∑ i ∈ s, g i`
  have hsum : v ⬝ᵥ factorB A *ᵥ v = ∑ i ∈ s, g i := by
    rw [factorB, ← hs, sum_mulVec, dotProduct_sum]
    exact Finset.sum_congr rfl (fun i hi => dotProduct_factorB_term hA (Finset.mem_filter.1 hi).2 v)
  -- each `g i` is a sum of squares
  have hgsos : ∀ i, IsSumSq (g i) := fun i => (hsos i).mul (isSumSq_dotProduct_self _)
  -- `1 ∈ s`, since `a₁ ≠ 0` forces `deg minpoly ≥ 1`
  have hmpos : 1 ≤ (minpoly F A).natDegree := by
    by_contra h
    refine ha1 ?_
    rw [signedCoeff, (minpoly F A).coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
  have h1s : (1 : ℕ) ∈ s := by
    rw [hs, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by decide⟩
  -- peel off the `i = 1` term
  rw [hsum, ← Finset.add_sum_erase s g h1s] at hv
  -- `g 1 = a₁ · (v ⬝ᵥ v)`, so `v ⬝ᵥ v = 0`, hence `v = 0`
  have hg1 : signedCoeff A 1 * (v ⬝ᵥ v) = 0 := by
    have h := Hilbert17Blueprint.isSumSq_eq_zero_of_add (hgsos 1)
      (IsSumSq.sum (fun i _ => hgsos i)) hv
    simpa [hg, show (1 - 1) / 2 = 0 from rfl, pow_zero, one_mulVec] using h
  exact Hilbert17Blueprint.dotProduct_self_eq_zero_semireal
    (by have := (mul_eq_zero.1 hg1).resolve_left ha1; rwa [dotProduct] at this)

/-- **`B` is a unit in `F[A]`** (real-closure-free): `B` is anisotropic, hence invertible as a
matrix, and since `F[A]` is a finite-dimensional commutative `F`-algebra, multiplication by `B` is
an injective — therefore bijective — endomorphism, so `B` is a unit in `F[A]`. -/
theorem factorBe_isUnit {A : Matrix n n F} (hA : A.IsSymm)
    (hsos : ∀ i, IsSumSq (signedCoeff A i)) (ha1 : signedCoeff A 1 ≠ 0) :
    IsUnit (factorBe A) := by
  have hBmat : IsUnit (factorB A) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_det_of_dotProduct_self_imp (factorB_anisotropic hA hsos ha1)
  rw [← Algebra.lmul_isUnit_iff (R := F), Module.End.isUnit_iff]
  have hinj : Function.Injective (Algebra.lmul F _ (factorBe A)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have hz0 : factorBe A * z = 0 := hz
    refine Subtype.val_injective ?_
    rw [ZeroMemClass.coe_zero]
    have hz' : factorB A * (z : Matrix n n F) = 0 := by
      have := congrArg (Subalgebra.val _) hz0
      simpa using this
    exact (hBmat.mul_right_eq_zero).1 hz'
  exact ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩

/-- **Identity (1) as an explicit factorisation (real-closure-free).** From the Lemma-4 shape of
`minpoly F A`, the matrix factors as `A = B · C` with `B = factorBe A` and `C = B⁻² R` both sums of
squares in `F[A]`. This is exactly the existential consumed by `Matrix.isSumSqSymm_of_factor`
(equivalently, the conclusion of Hillar–Nie's `exists_isSumSq_factor`). -/
theorem exists_isSumSq_factor_of_minpoly_shape {A : Matrix n n F} (hA : A.IsSymm)
    (hsos : ∀ i, IsSumSq (signedCoeff A i)) (ha1 : signedCoeff A 1 ≠ 0) :
    ∃ B C : Algebra.adjoin F ({A} : Set (Matrix n n F)),
      IsSumSq B ∧ IsSumSq C ∧ (A : Matrix n n F) = (B : Matrix n n F) * C := by
  obtain ⟨u, hu⟩ := factorBe_isUnit hA hsos ha1
  set Ae : Algebra.adjoin F ({A} : Set (Matrix n n F)) :=
    ⟨A, Algebra.self_mem_adjoin_singleton F A⟩ with hAe
  refine ⟨factorBe A, (↑u⁻¹ * ↑u⁻¹) * factorRe A, factorBe_isSumSq A hsos,
    (IsSumSq.mul_self _).mul (factorRe_isSumSq A hsos), ?_⟩
  have hrel : Ae * (u : Algebra.adjoin F ({A} : Set (Matrix n n F))) = factorRe A := by
    rw [hu]; exact Ae_mul_factorBe_eq_factorRe A
  have key : Ae = factorBe A * ((↑u⁻¹ * ↑u⁻¹) * factorRe A) := by
    rw [← hu, ← hrel,
      show (↑u : Algebra.adjoin F ({A} : Set (Matrix n n F)))
          * ((↑u⁻¹ * ↑u⁻¹) * (Ae * ↑u)) = (↑u * ↑u⁻¹) * ((↑u⁻¹ * ↑u) * Ae) by ring,
      Units.mul_inv, Units.inv_mul, one_mul, one_mul]
  have := congrArg (Subalgebra.val _) key
  simpa using this

/-- **Identity (1), from the Lemma-4 data (real-closure-free).** If `minpoly F A` has the Lemma-4
shape — every signed coefficient `aᵢ = (-1)^(m-i)·coeffᵢ` a sum of squares, and `a₁ ≠ 0` — then the
symmetric matrix `A` is a sum of squares of symmetric matrices. This is the entire real-closure-free
half of Hillar–Nie's Theorem 3: `A = B·C` with `B = ∑_{i odd} aᵢ Aⁱ⁻¹`, `C = B⁻²R`. -/
theorem isSumSqSymm_of_minpoly_shape {A : Matrix n n F} (hA : A.IsSymm)
    (hsos : ∀ i, IsSumSq (signedCoeff A i)) (ha1 : signedCoeff A 1 ≠ 0) :
    A.IsSumSqSymm :=
  factor_of_relation hA (Ae_mul_factorBe_eq_factorRe A) (factorBe_isSumSq A hsos)
    (factorRe_isSumSq A hsos) (factorBe_isUnit hA hsos ha1)

/-! ### Hillar–Nie Lemma 4 (the real-closed-field input)

Everything above is real-closure-free: given the Lemma-4 shape of `minpoly F A`,
`isSumSqSymm_of_minpoly_shape` proves `A.IsSumSqSymm`.

**Lemma 4** itself states that for a symmetric `A` all of whose principal minors are sums of squares,
the signed coefficients `aᵢ = (-1)^(m-i)·(minpoly F A).coeff i` are sums of squares and `a₁ ≠ 0`. The
proof passes, for each ordering of `F`, to a real closure `R ⊇ F`, where the spectral theorem over a
real closed field makes `A` diagonalisable with nonnegative eigenvalues, so `aᵢ` is an elementary
symmetric function of nonnegative numbers (hence `≥ 0`) and `a₁ ≠ 0`; nonnegativity in every ordering
then gives a sum of squares by the easy Artin–Schreier theorem (`RingPreordering.isSumSq_of_forall_mem`).
This is provided by `Hilbert17Blueprint.isSumSq_minpoly_signedCoeff` and
`Hilbert17Blueprint.minpoly_coeff_one_ne_zero`. -/

/-- **Hillar–Nie Lemma 4.** For a symmetric matrix `A` (over a nonempty index type) whose principal
minors are all sums of squares, the signed coefficients of the minimal polynomial are sums of
squares, and the linear one `a₁` is nonzero. The real-closed-field input is supplied by the spectral
theory in `Hilbert17Blueprint` (`isSumSq_minpoly_signedCoeff` and `minpoly_coeff_one_ne_zero`). -/
theorem minpoly_lemma4 [Nonempty n] {A : Matrix n n F} (hA : A.IsSymm)
    (hminor : ∀ s : Finset n,
      IsSumSq (A.submatrix (fun i : s => (i : n)) (fun i : s => (i : n))).det) :
    (∀ i, IsSumSq (signedCoeff A i)) ∧ signedCoeff A 1 ≠ 0 :=
  ⟨fun i => Hilbert17Blueprint.isSumSq_minpoly_signedCoeff hA hminor i,
    Hilbert17Blueprint.minpoly_coeff_one_ne_zero hA hminor⟩

/-- **Hilbert's 17th problem for matrices, via identity (1).** Combining the real-closure-free
factorisation `isSumSqSymm_of_minpoly_shape` with Lemma 4: a symmetric matrix whose principal minors
are sums of squares is a sum of squares of symmetric matrices. -/
theorem isSumSqSymm_of_principalMinors {A : Matrix n n F} (hA : A.IsSymm)
    (hminor : ∀ s : Finset n,
      IsSumSq (A.submatrix (fun i : s => (i : n)) (fun i : s => (i : n))).det) :
    A.IsSumSqSymm := by
  rcases isEmpty_or_nonempty n with _ | hn
  · rw [Subsingleton.elim A 0]; exact Matrix.IsSumSqSymm.zero
  · obtain ⟨hsos, ha1⟩ := minpoly_lemma4 hA hminor
    exact isSumSqSymm_of_minpoly_shape hA hsos ha1

end Hilbert17Lemma4
