/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.Hilbert17PSD

/-!
# Spectral theorem over a real closed field

Part of the real-closed-field input to Hilbert's 17th problem for matrices
(see `Mathlib.NumberTheory.Transcendental.Hilbert17`).

For a symmetric matrix over a real closed field, the minimal polynomial splits
(`splits_minpoly_of_isSymm`), is squarefree (`squarefree_minpoly_of_isSymm`), and — when the
principal minors are nonnegative — has nonnegative roots and nonnegative signed coefficients
(`minpoly_signedCoeff_nonneg`), via Vieta's formulas.
-/

namespace Hilbert17Blueprint

open Polynomial Matrix

/-! ### (B) Spectral core — pieces (over a real closed field) -/
section Spectral
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **B1a.** Over `R[i]` the minimal polynomial splits — immediate from `isAlgClosed_adjoinRoot`
(A, now proved): every polynomial over an algebraically closed field splits (`IsAlgClosed.splits`).
**Proved.** -/
theorem splits_minpoly_map_adjoinRoot [Fact (Irreducible (X ^ 2 + 1 : R[X]))]
    {A : Matrix n n R} (hA : A.IsSymm) :
    ((minpoly R A).map (algebraMap R (AdjoinRoot (X ^ 2 + 1 : R[X])))).Splits := by
  haveI : IsAlgClosed (AdjoinRoot (X ^ 2 + 1 : R[X])) := isAlgClosed_adjoinRoot
  exact IsAlgClosed.splits _

/-- **B1b** (eigenvalues are real — the genuine content of B1). Every root of `minpoly R A` in
`R[i]` already lies in (the image of) `R`: the conjugation `a + b·i ↦ a - b·i` of `R[i]` fixes it,
shown by the Hermitian argument `(A v̄)ᵀ v = v̄ᵀ (A v)` for an eigenvector `v` over `R[i]`. -/
theorem roots_minpoly_adjoinRoot_mem_range [Fact (Irreducible (X ^ 2 + 1 : R[X]))]
    {A : Matrix n n R} (hA : A.IsSymm)
    {z : AdjoinRoot (X ^ 2 + 1 : R[X])}
    (hz : ((minpoly R A).map (algebraMap R (AdjoinRoot (X ^ 2 + 1 : R[X])))).IsRoot z) :
    z ∈ (algebraMap R (AdjoinRoot (X ^ 2 + 1 : R[X]))).range := roots_real hA hz

/-- **B1** (assembly). The minimal polynomial of a symmetric matrix over a real closed field splits
over `R`. From B1a (splits over `R[i]`) and B1b (its `R[i]`-roots are real), the splitting descends
to `R`. (Alternatively, port the repo's irreducible-polynomial classification.) -/
theorem splits_minpoly_of_isSymm {A : Matrix n n R} (hA : A.IsSymm) :
    (minpoly R A).Splits := by
  haveI : Fact (Irreducible (X ^ 2 + 1 : R[X])) := ⟨irreducible_X_sq_add_one⟩
  refine Splits.of_splits_map (algebraMap R (AdjoinRoot (X ^ 2 + 1 : R[X])))
    (splits_minpoly_map_adjoinRoot hA) (fun a ha => ?_)
  exact roots_minpoly_adjoinRoot_mem_range hA (isRoot_of_mem_roots ha)

/-- A nonzero matrix moves some vector. -/
theorem exists_mulVec_ne_zero {M : Matrix n n R} (hM : M ≠ 0) : ∃ v, M *ᵥ v ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hM
  ext i j
  have h := hcon (Pi.single j 1)
  have : (M *ᵥ Pi.single j 1) i = M i j := by rw [Matrix.mulVec_single_one]; rfl
  rw [h] at this
  simpa using this.symm

/-- **B2.** The minimal polynomial of a symmetric matrix is squarefree (no nontrivial Jordan
blocks). Since `R` is a perfect field (char 0) and `minpoly R A` splits (B1),
`Squarefree (minpoly R A) ↔ (minpoly R A).roots.Nodup`. A repeated root `μ` would give
`(X - C μ)² ∣ minpoly R A`; writing `minpoly = (X - C μ)·p` with `p = (X - C μ)·g`, minimality
forces `aeval A p ≠ 0`, so some `v` has `w := p(A) v ≠ 0`. But `w = (A - μ)·(g(A) v)` and
`(A - μ)·w = minpoly(A) v = 0`, so the generalised-eigenvector lemma
`Matrix.IsSymm.sub_smul_one_mulVec_eq_zero_of_sq` forces `w = 0` — a contradiction. -/
theorem squarefree_minpoly_of_isSymm {A : Matrix n n R} (hA : A.IsSymm) :
    Squarefree (minpoly R A) := by
  have hne : minpoly R A ≠ 0 := (minpoly.monic (Matrix.isIntegral A)).ne_zero
  rw [← PerfectField.separable_iff_squarefree,
    ← nodup_roots_iff_of_splits hne (splits_minpoly_of_isSymm hA),
    Multiset.nodup_iff_count_le_one]
  intro μ
  rw [count_roots]
  by_contra h
  push Not at h
  have hdvd : (X - C μ) ^ 2 ∣ minpoly R A := (le_rootMultiplicity_iff hne).mp (by omega)
  obtain ⟨g, hg⟩ := hdvd
  set p : R[X] := (X - C μ) * g with hp
  have hfact : minpoly R A = (X - C μ) * p := by rw [hp, hg]; ring
  have hpne : p ≠ 0 := by intro h0; rw [h0, mul_zero] at hfact; exact hne hfact
  have hdeg : (minpoly R A).natDegree = p.natDegree + 1 := by
    rw [hfact, natDegree_mul (X_sub_C_ne_zero μ) hpne, natDegree_X_sub_C]; ring
  have haeval : (aeval A) p ≠ 0 := by
    intro hz
    have := Polynomial.natDegree_le_of_dvd (minpoly.dvd R A hz) hpne
    omega
  obtain ⟨v, hv⟩ := exists_mulVec_ne_zero haeval
  set Aμ : Matrix n n R := A - μ • 1 with hAμ
  have hXC : (aeval A) (X - C μ) = Aμ := by
    rw [map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
  set u : n → R := (aeval A) g *ᵥ v with hu
  set w : n → R := (aeval A) p *ᵥ v with hw
  have hwu : w = Aμ *ᵥ u := by rw [hw, hu, Matrix.mulVec_mulVec, ← hXC, hp, map_mul]
  have hAμw : Aμ *ᵥ w = 0 := by
    have h0 : (aeval A) (minpoly R A) *ᵥ v = 0 := by rw [minpoly.aeval]; simp
    rw [hfact, map_mul, hXC, ← Matrix.mulVec_mulVec] at h0
    rw [hw]; exact h0
  have hsq : Aμ *ᵥ (Aμ *ᵥ u) = 0 := by rw [← hwu]; exact hAμw
  have hzero := hA.sub_smul_one_mulVec_eq_zero_of_sq μ hsq
  rw [← hwu] at hzero
  exact hv hzero

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- **B3-eig** (eigenvector from a root of the minimal polynomial). A root `μ` of `minpoly R A` is
an eigenvalue: since `minpoly R A ∣ charpoly A` (Cayley–Hamilton, `minpoly.dvd` +
`aeval_self_charpoly`), `μ` is a root of `charpoly`, so `det (μ • 1 - A) = 0` (`eval_charpoly`),
giving a nonzero `v` with
`(μ • 1 - A) *ᵥ v = 0` (`Matrix.exists_mulVec_eq_zero_iff`). **Proved.** -/
theorem exists_eigenvector_of_isRoot_minpoly {A : Matrix n n R} (μ : R)
    (hμ : (minpoly R A).IsRoot μ) : ∃ v : n → R, v ≠ 0 ∧ A *ᵥ v = μ • v := by
  have hdvd : minpoly R A ∣ A.charpoly := minpoly.dvd R A (aeval_self_charpoly A)
  have hcroot : A.charpoly.IsRoot μ := by
    obtain ⟨g, hg⟩ := hdvd; simp [IsRoot, hg, IsRoot.def.1 hμ]
  have hdet : (Matrix.scalar n μ - A).det = 0 := by rw [← eval_charpoly]; exact hcroot
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  refine ⟨v, hv0, ?_⟩
  have hsc : (Matrix.scalar n μ) *ᵥ v = μ • v := by
    ext i; simp [Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  rw [Matrix.sub_mulVec, hsc, sub_eq_zero] at hv
  exact hv.symm

/-- **B3.** With all principal minors `≥ 0`, every eigenvalue (root of the minimal polynomial) is
`≥ 0`. **Proved** from B3-eig and the Rayleigh quotient: `A *ᵥ v = μ • v` and positive
semidefiniteness (C3) give `0 ≤ v ⬝ᵥ A *ᵥ v = μ * (v ⬝ᵥ v)` with `v ⬝ᵥ v > 0`, so `0 ≤ μ`. -/
theorem roots_minpoly_nonneg_of_isSymm {A : Matrix n n R} (hA : A.IsSymm)
    (hminor : ∀ s : Finset n,
      0 ≤ (A.submatrix (fun i : s => (i : n)) (fun i : s => (i : n))).det) :
    ∀ μ ∈ (minpoly R A).roots, 0 ≤ μ := by
  intro μ hμ
  obtain ⟨v, hv0, hv⟩ :=
    exists_eigenvector_of_isRoot_minpoly μ (isRoot_of_mem_roots hμ)
  have key : 0 ≤ v ⬝ᵥ A *ᵥ v := (isPSDForm_of_forall_principalMinor_nonneg hA hminor).2 v
  rw [hv, dotProduct_smul, smul_eq_mul] at key
  have hvv : 0 < v ⬝ᵥ v :=
    lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (v i))
      fun h => hv0 (dotProduct_self_eq_zero.mp h.symm)
  exact (mul_nonneg_iff_of_pos_right hvv).mp key

omit [IsRealClosed R] in
/-- The elementary symmetric functions of a multiset of nonnegative elements are nonnegative. -/
theorem esymm_nonneg (s : Multiset R) (h : ∀ x ∈ s, 0 ≤ x) (k : ℕ) : 0 ≤ s.esymm k := by
  refine Multiset.sum_nonneg fun y hy => ?_
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hy
  exact Multiset.prod_nonneg fun z hz =>
    h z (Multiset.mem_of_le (Multiset.mem_powersetCard.1 ht).1 hz)

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- **B-monic.** The minimal polynomial of a matrix over a field is monic
(`minpoly.monic` applied to integrality of `A`). -/
theorem monic_minpoly (A : Matrix n n R) : (minpoly R A).Monic :=
  minpoly.monic (Matrix.isIntegral A)

/-- **B-prod** (Vieta, step 1). From B1 (splits) and monicity, the minimal polynomial is the product
of its linear factors `X - μ` over the multiset of its roots
(`Polynomial.eq_prod_roots_of_monic_of_splits_id`). -/
theorem minpoly_eq_prod_roots {A : Matrix n n R} (hA : A.IsSymm) :
    minpoly R A = ((minpoly R A).roots.map fun μ => X - C μ).prod :=
  (splits_minpoly_of_isSymm hA).eq_prod_roots_of_monic (monic_minpoly A)

/-- **B-esymm** (Vieta, step 2). For `i ≤ deg`, the signed `i`-th coefficient of the (monic, split)
minimal polynomial equals the `(deg - i)`-th elementary symmetric function of its roots
(`Polynomial.coeff_eq_esymm_roots_of_splits`, with the sign squared away by `Even.neg_one_pow`).
**Proved** from B1. -/
theorem signedCoeff_eq_esymm_roots {A : Matrix n n R} (hA : A.IsSymm) {i : ℕ}
    (hi : i ≤ (minpoly R A).natDegree) :
    (-1) ^ ((minpoly R A).natDegree - i) * (minpoly R A).coeff i =
      ((minpoly R A).roots).esymm ((minpoly R A).natDegree - i) := by
  rw [coeff_eq_esymm_roots_of_splits (splits_minpoly_of_isSymm hA) hi,
      (monic_minpoly A).leadingCoeff, one_mul, ← mul_assoc, ← pow_add, ← two_mul,
      pow_mul, neg_one_sq, one_pow, one_mul]

/-- **B4** (spectral core). By Vieta (`signedCoeff_eq_esymm_roots`) the signed coefficients are
elementary symmetric functions of the roots, which are nonnegative since all roots are nonnegative
(B3, `roots_minpoly_nonneg_of_isSymm`); for `i > deg` the coefficient vanishes. -/
theorem minpoly_signedCoeff_nonneg {A : Matrix n n R} (hA : A.IsSymm)
    (hminor : ∀ s : Finset n,
      0 ≤ (A.submatrix (fun i : s => (i : n)) (fun i : s => (i : n))).det) (i : ℕ) :
    0 ≤ (-1) ^ ((minpoly R A).natDegree - i) * (minpoly R A).coeff i := by
  rcases Nat.lt_or_ge (minpoly R A).natDegree i with hi | hi
  · simp [coeff_eq_zero_of_natDegree_lt hi]
  · rw [signedCoeff_eq_esymm_roots hA hi]
    exact esymm_nonneg _ (roots_minpoly_nonneg_of_isSymm hA hminor) _

/-- Every root of the **characteristic** polynomial of a symmetric matrix with nonnegative principal
minors is nonnegative (eigenvalue is `≥ 0` by the Rayleigh quotient). -/
theorem charpoly_roots_nonneg_of_isSymm {A : Matrix n n R} (hA : A.IsSymm)
    (hminor : ∀ s : Finset n,
      0 ≤ (A.submatrix (fun i : s => (i : n)) (fun i : s => (i : n))).det) :
    ∀ μ ∈ A.charpoly.roots, 0 ≤ μ := by
  intro μ hμ
  have hdet : (Matrix.scalar n μ - A).det = 0 := by rw [← eval_charpoly]; exact isRoot_of_mem_roots hμ
  obtain ⟨v, hv0, hv'⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hv : A *ᵥ v = μ • v := by
    have hsc : (Matrix.scalar n μ) *ᵥ v = μ • v := by
      ext i; simp [Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    rw [Matrix.sub_mulVec, hsc, sub_eq_zero] at hv'; exact hv'.symm
  have key : 0 ≤ v ⬝ᵥ A *ᵥ v := (isPSDForm_of_forall_principalMinor_nonneg hA hminor).2 v
  rw [hv, dotProduct_smul, smul_eq_mul] at key
  have hvv : 0 < v ⬝ᵥ v :=
    lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (v i))
      fun h => hv0 (dotProduct_self_eq_zero.mp h.symm)
  exact (mul_nonneg_iff_of_pos_right hvv).mp key

/-- The characteristic polynomial of a symmetric matrix splits over a real closed field
(same `R[i]`-descent as `splits_minpoly_of_isSymm`). -/
theorem splits_charpoly_of_isSymm {A : Matrix n n R} (hA : A.IsSymm) : A.charpoly.Splits := by
  haveI : Fact (Irreducible (X ^ 2 + 1 : R[X])) := ⟨irreducible_X_sq_add_one⟩
  haveI : IsAlgClosed (AdjoinRoot (X ^ 2 + 1 : R[X])) := isAlgClosed_adjoinRoot
  have hsplit : (A.charpoly.map (algebraMap R (AdjoinRoot (X ^ 2 + 1 : R[X])))).Splits := by
    rw [← Matrix.charpoly_map]; exact IsAlgClosed.splits _
  refine Splits.of_splits_map (algebraMap R (AdjoinRoot (X ^ 2 + 1 : R[X]))) hsplit (fun a ha => ?_)
  exact charpoly_root_real hA (by rw [Matrix.charpoly_map]; exact isRoot_of_mem_roots ha)

/-- **Vieta for a monic split polynomial**: signed coefficient = elementary symmetric of the
roots. -/
theorem signedCoeff_eq_esymm_of_monic_splits {p : R[X]} (hpm : p.Monic) (hsp : p.Splits) {i : ℕ}
    (hi : i ≤ p.natDegree) :
    (-1) ^ (p.natDegree - i) * p.coeff i = p.roots.esymm (p.natDegree - i) := by
  rw [coeff_eq_esymm_roots_of_splits hsp hi, hpm.leadingCoeff, one_mul, ← mul_assoc, ← pow_add,
      ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

/-- **Master spectral inequality.** For a symmetric `A` over a real closed field with nonnegative
principal minors, every monic divisor `p` of `charpoly A` has nonnegative signed coefficients
(its roots are among the nonnegative eigenvalues, and it splits). -/
theorem signedCoeff_dvd_charpoly_nonneg {A : Matrix n n R} (hA : A.IsSymm)
    (hminor : ∀ s : Finset n,
      0 ≤ (A.submatrix (fun i : s => (i : n)) (fun i : s => (i : n))).det)
    {p : R[X]} (hpm : p.Monic) (hdvd : p ∣ A.charpoly) (i : ℕ) :
    0 ≤ (-1) ^ (p.natDegree - i) * p.coeff i := by
  have hcne : A.charpoly ≠ 0 := A.charpoly_monic.ne_zero
  rcases Nat.lt_or_ge p.natDegree i with hi | hi
  · simp [coeff_eq_zero_of_natDegree_lt hi]
  · have hsp : p.Splits := (splits_charpoly_of_isSymm hA).of_dvd hcne hdvd
    rw [signedCoeff_eq_esymm_of_monic_splits hpm hsp hi]
    refine esymm_nonneg _ (fun μ hμ => ?_) _
    exact charpoly_roots_nonneg_of_isSymm hA hminor μ
      (Multiset.mem_of_le (Polynomial.roots.le_of_dvd hcne hdvd) hμ)

end Spectral

end Hilbert17Blueprint
