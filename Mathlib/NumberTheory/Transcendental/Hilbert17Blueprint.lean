/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.Hilbert17RealClosureOrder

/-!
# Hilbert's 17th for matrices: transfer to a formally real field (Hillar–Nie Lemma 4)

This is the top of the real-closed-field development behind Hilbert's 17th problem for matrices
(see `Mathlib.NumberTheory.Transcendental.Hilbert17`). It imports the pieces

* `Hilbert17FTA` — `R[i]` is algebraically closed;
* `Hilbert17PSD` — Sylvester's positive-semidefiniteness criterion;
* `Hilbert17Spectral` — the spectral theorem over a real closed field;
* `Hilbert17RealClosure`, `Hilbert17RealClosureOrder` — existence of a real closure of an ordered
  field;

and assembles **Lemma 4**: for a symmetric matrix over a formally real field whose principal minors
are sums of squares, the signed coefficients of its minimal polynomial are sums of squares
(`isSumSq_minpoly_signedCoeff`) with nonzero linear term (`minpoly_coeff_one_ne_zero`). These are
consumed by `Hilbert17Lemma4`.
-/

namespace Hilbert17Blueprint

open Polynomial Matrix

universe u

/-! ### (D-transfer) From the real-closed case to a formally real field -/

section DTransfer
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Core of D-transfer.** Embedding a symmetric matrix `A` over `F` into a real closed field `C`
via a ring hom `emb`, if `A`'s principal minors are sums of squares then the image under `emb` of
each signed coefficient of `minpoly F A` is nonnegative: over `C`, `(minpoly F A).map emb` is a
monic divisor of `charpoly`, so `signedCoeff_dvd_charpoly_nonneg` applies, and coefficients map. -/
theorem emb_signedCoeff_nonneg {F : Type*} [Field F] {C : Type*} [Field C] [LinearOrder C]
    [IsStrictOrderedRing C] [IsRealClosed C] (emb : F →+* C) {A : Matrix n n F} (hA : A.IsSymm)
    (hminor : ∀ s : Finset n,
      IsSumSq (A.submatrix (fun i : s => (i : n)) (fun i : s => (i : n))).det) (i : ℕ) :
    0 ≤ emb ((-1) ^ ((minpoly F A).natDegree - i) * (minpoly F A).coeff i) := by
  have hAB : (A.map emb).IsSymm := hA.map emb
  have hminorB : ∀ s : Finset n,
      0 ≤ ((A.map emb).submatrix (fun j : s => (j : n)) (fun j : s => (j : n))).det := by
    intro s
    have he : ((A.map emb).submatrix (fun j : s => (j : n)) (fun j : s => (j : n))).det
        = emb ((A.submatrix (fun j : s => (j : n)) (fun j : s => (j : n))).det) := by
      rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [he]
    exact (isSumSq_ringHom_map emb (hminor s)).nonneg
  have hpm : ((minpoly F A).map emb).Monic := (monic_minpoly A).map emb
  have hpdvd : (minpoly F A).map emb ∣ (A.map emb).charpoly := by
    rw [Matrix.charpoly_map]
    exact Polynomial.map_dvd emb (minpoly.dvd F A (aeval_self_charpoly A))
  have hnn := signedCoeff_dvd_charpoly_nonneg hAB hminorB hpm hpdvd i
  rwa [(minpoly F A).natDegree_map_eq_of_injective emb.injective, Polynomial.coeff_map,
    show (-1 : C) ^ ((minpoly F A).natDegree - i) * emb ((minpoly F A).coeff i)
        = emb ((-1) ^ ((minpoly F A).natDegree - i) * (minpoly F A).coeff i) from
      by rw [map_mul, map_pow, map_neg, map_one]] at hnn

variable {F : Type*} [Field F] [IsSemireal F]

/-- **D-transfer** (the bridge from the real-closed case to a formally real field). For a symmetric
`A` over a formally real `F` with all principal minors sums of squares, each signed coefficient of
`minpoly F A` is again a sum of squares. **Proof:** by the easy Artin–Schreier theorem
(`RingPreordering.isSumSq_of_forall_mem`) it suffices to show membership in every ordering `O` of
`F`. Make `(F, O)` an ordered field, embed it into a real closure `R_O` (`exists_realClosure`);
the image of the signed coefficient is `≥ 0` there (`emb_signedCoeff_nonneg`); `emb` is
order-reflecting, so the coefficient lies in `O`. -/
theorem isSumSq_minpoly_signedCoeff {A : Matrix n n F} (hA : A.IsSymm)
    (hminor : ∀ s : Finset n,
      IsSumSq (A.submatrix (fun i : s => (i : n)) (fun i : s => (i : n))).det)
    (i : ℕ) :
    IsSumSq ((-1) ^ ((minpoly F A).natDegree - i) * (minpoly F A).coeff i) := by
  set x := (-1) ^ ((minpoly F A).natDegree - i) * (minpoly F A).coeff i with hx
  apply RingPreordering.isSumSq_of_forall_mem
  intro O hO
  haveI := hO
  letI : LinearOrder F := RingPreordering.toLinearOrder O
  letI : IsStrictOrderedRing F := RingPreordering.toIsStrictOrderedRing O
  obtain ⟨C, emb, hmono⟩ := (exists_realClosure F).some
  have hnn : 0 ≤ emb x := emb_signedCoeff_nonneg emb hA hminor i
  rw [← RingPreordering.toLinearOrder_nonneg_iff (O := O)]
  by_contra hlt
  push Not at hlt
  have hle : emb x ≤ 0 := by have := hmono hlt.le; rwa [map_zero] at this
  exact absurd (emb.injective ((le_antisymm hle hnn).trans (map_zero emb).symm)) (ne_of_lt hlt)

end DTransfer

/-! ### (capstone) `a₁ ≠ 0` and Hilbert's 17th for matrices, sorry-free -/

section Hilbert17Capstone

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Generalised eigenvectors are eigenvectors, over a formally real field (`μ = 0` case). -/
theorem mulVec_eq_zero_of_sq_semireal {F : Type*} [Field F] [IsSemireal F] {A : Matrix n n F}
    (hA : A.IsSymm) {v : n → F} (h : A *ᵥ (A *ᵥ v) = 0) : A *ᵥ v = 0 := by
  have key : (A *ᵥ v) ⬝ᵥ (A *ᵥ v) = 0 := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hA.eq, h, zero_dotProduct]
  exact dotProduct_self_eq_zero_semireal key

/-- The minimal polynomial of a symmetric matrix over a formally real field has `0` as a root of
multiplicity at most one (no nontrivial nilpotent part at `0`). -/
theorem rootMultiplicity_zero_minpoly_le_one {F : Type*} [Field F] [IsSemireal F]
    {A : Matrix n n F} (hA : A.IsSymm) : (minpoly F A).rootMultiplicity 0 ≤ 1 := by
  by_contra hc
  push Not at hc
  have hne : minpoly F A ≠ 0 := (minpoly.monic (Matrix.isIntegral A)).ne_zero
  have hdvd : (X - C (0 : F)) ^ 2 ∣ minpoly F A := (le_rootMultiplicity_iff hne).mp (by omega)
  rw [C_0, sub_zero] at hdvd
  obtain ⟨g, hg⟩ := hdvd
  set p₁ : F[X] := X * g with hp1
  have hfact : minpoly F A = X * p₁ := by rw [hp1, hg]; ring
  have hp1ne : p₁ ≠ 0 := fun h0 => hne (by rw [hfact, h0, mul_zero])
  have hdeg : (minpoly F A).natDegree = p₁.natDegree + 1 := by
    rw [hfact, natDegree_mul X_ne_zero hp1ne, natDegree_X]; ring
  have haeval : (aeval A) p₁ ≠ 0 := fun hz => by
    have := Polynomial.natDegree_le_of_dvd (minpoly.dvd F A hz) hp1ne; omega
  obtain ⟨v, hv⟩ : ∃ v, (aeval A) p₁ *ᵥ v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply haeval
    ext i j
    have hh := hcon (Pi.single j 1)
    have he : ((aeval A) p₁ *ᵥ Pi.single j 1) i = (aeval A) p₁ i j := by
      rw [Matrix.mulVec_single_one]; rfl
    rw [hh] at he
    simpa using he.symm
  set u : n → F := (aeval A) g *ᵥ v with hu
  set w : n → F := (aeval A) p₁ *ᵥ v with hw
  have hwu : w = A *ᵥ u := by rw [hw, hu, Matrix.mulVec_mulVec, hp1, map_mul, aeval_X]
  have hAw : A *ᵥ w = 0 := by
    have h0 : (aeval A) (minpoly F A) *ᵥ v = 0 := by rw [minpoly.aeval]; simp
    rw [hfact, map_mul, aeval_X, ← Matrix.mulVec_mulVec] at h0
    rw [hw]; exact h0
  have hsq : A *ᵥ (A *ᵥ u) = 0 := by rw [← hwu]; exact hAw
  have hu0 := mulVec_eq_zero_of_sq_semireal hA hsq
  rw [← hwu] at hu0
  exact hv hu0

/-- `esymm (card - 1)` of a nonnegative multiset with at most one zero is nonzero (positive):
the term obtained by deleting the unique zero (or, if none, any element) is a product of strictly
positive numbers. -/
theorem esymm_card_sub_one_ne_zero {C : Type*} [Field C] [LinearOrder C] [IsStrictOrderedRing C]
    {s : Multiset C} (hnn : ∀ x ∈ s, 0 ≤ x) (hz : s.count 0 ≤ 1) (hcard : 0 < Multiset.card s) :
    s.esymm (Multiset.card s - 1) ≠ 0 := by
  obtain ⟨z, hzs, hpos⟩ : ∃ z ∈ s, ∀ x ∈ s.erase z, 0 < x := by
    by_cases h0 : (0 : C) ∈ s
    · refine ⟨0, h0, fun x hx => ?_⟩
      have hcount0 : (s.erase 0).count 0 = 0 := by rw [Multiset.count_erase_self]; omega
      refine lt_of_le_of_ne (hnn x (Multiset.mem_of_mem_erase hx)) (fun he => ?_)
      exact (Multiset.count_eq_zero.mp hcount0) (he ▸ hx)
    · obtain ⟨z, hzs⟩ := Multiset.card_pos_iff_exists_mem.mp hcard
      exact ⟨z, hzs, fun x hx =>
        lt_of_le_of_ne (hnn x (Multiset.mem_of_mem_erase hx))
          (fun he => h0 (he ▸ Multiset.mem_of_mem_erase hx))⟩
  apply ne_of_gt
  have hterm : (s.erase z).prod ∈ (Multiset.powersetCard (Multiset.card s - 1) s).map Multiset.prod :=
    Multiset.mem_map_of_mem _ (Multiset.mem_powersetCard.mpr
      ⟨Multiset.erase_le z s, Multiset.card_erase_of_mem hzs⟩)
  calc (0 : C) < (s.erase z).prod := Multiset.prod_pos hpos
    _ ≤ s.esymm (Multiset.card s - 1) := by
        refine Multiset.single_le_sum (fun y hy => ?_) _ hterm
        obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hy
        exact Multiset.prod_nonneg fun x hx =>
          hnn x (Multiset.mem_of_le (Multiset.mem_powersetCard.1 ht).1 hx)

/-- **The linear signed coefficient `a₁` is nonzero** (Hillar–Nie Lemma 4, second part). Over a real
closure, the eigenvalues are nonnegative and `0` occurs with multiplicity `≤ 1` (no nilpotent part),
so `a₁ = esymm` of the eigenvalues is strictly positive. -/
theorem minpoly_coeff_one_ne_zero {F : Type*} [Field F] [IsSemireal F] [Nonempty n]
    {A : Matrix n n F} (hA : A.IsSymm)
    (hminor : ∀ s : Finset n,
      IsSumSq (A.submatrix (fun i : s => (i : n)) (fun i : s => (i : n))).det) :
    (-1) ^ ((minpoly F A).natDegree - 1) * (minpoly F A).coeff 1 ≠ 0 := by
  obtain ⟨R, hRrc⟩ := exists_isRealClosed_extension F
  haveI := hRrc
  letI : LinearOrder ↥R := sosLinearOrder ↥R
  haveI : IsStrictOrderedRing ↥R := sosIsStrictOrderedRing ↥R
  set emb : F →+* ↥R := algebraMap F ↥R with hemb
  have hembinj : Function.Injective emb := emb.injective
  set p : (↥R)[X] := (minpoly F A).map emb with hp
  have hpm : p.Monic := (minpoly.monic (Matrix.isIntegral A)).map emb
  have hAB : (A.map emb).IsSymm := hA.map emb
  have hminorB : ∀ s : Finset n,
      0 ≤ ((A.map emb).submatrix (fun j : s => (j : n)) (fun j : s => (j : n))).det := by
    intro s
    have he : ((A.map emb).submatrix (fun j : s => (j : n)) (fun j : s => (j : n))).det
        = emb ((A.submatrix (fun j : s => (j : n)) (fun j : s => (j : n))).det) := by
      rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [he]; exact (isSumSq_ringHom_map emb (hminor s)).nonneg
  have hpdvd : p ∣ (A.map emb).charpoly := by
    rw [hp, Matrix.charpoly_map]
    exact Polynomial.map_dvd emb (minpoly.dvd F A (aeval_self_charpoly A))
  have hcne : (A.map emb).charpoly ≠ 0 := (A.map emb).charpoly_monic.ne_zero
  have hsp : p.Splits := (splits_charpoly_of_isSymm hAB).of_dvd hcne hpdvd
  have hrootsnn : ∀ μ ∈ p.roots, 0 ≤ μ := fun μ hμ =>
    charpoly_roots_nonneg_of_isSymm hAB hminorB μ
      (Multiset.mem_of_le (Polynomial.roots.le_of_dvd hcne hpdvd) hμ)
  have hcard : p.roots.card = p.natDegree := splits_iff_card_roots.mp hsp
  have hpd1 : 1 ≤ p.natDegree := by
    rw [hp, natDegree_map_eq_of_injective hembinj]
    exact minpoly.natDegree_pos (Matrix.isIntegral A)
  have hcount : p.roots.count 0 ≤ 1 := by
    rw [Polynomial.count_roots]
    have heq : p.rootMultiplicity 0 = (minpoly F A).rootMultiplicity 0 := by
      rw [hp, ← map_zero emb, ← eq_rootMultiplicity_map hembinj]
    rw [heq]; exact rootMultiplicity_zero_minpoly_le_one hA
  have hkey : emb ((-1) ^ ((minpoly F A).natDegree - 1) * (minpoly F A).coeff 1)
      = p.roots.esymm (p.natDegree - 1) := by
    rw [← signedCoeff_eq_esymm_of_monic_splits hpm hsp hpd1,
      map_mul, map_pow, map_neg, map_one, hp, natDegree_map_eq_of_injective hembinj,
      Polynomial.coeff_map]
  have hesymm : p.roots.esymm (p.natDegree - 1) ≠ 0 := by
    rw [← hcard]
    exact esymm_card_sub_one_ne_zero hrootsnn hcount (by rw [hcard]; omega)
  intro hcontra
  exact hesymm (by rw [← hkey, hcontra, map_zero])

end Hilbert17Capstone

end Hilbert17Blueprint
