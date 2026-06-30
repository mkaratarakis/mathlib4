/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.Sylvester
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.NumberTheory.Transcendental.OrderedSylvester
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Sylow
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Order.Zorn
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Order.Ring.Cone
import Mathlib.NumberTheory.Transcendental.ArtinSchreier

/-!
# Algebraic fundamental theorem of algebra (over a real closed field)

Part of the real-closed-field input to Hilbert's 17th problem for matrices
(see `Mathlib.NumberTheory.Transcendental.Hilbert17`).

For a real closed field `R`, the field `R[i] = AdjoinRoot (X ^ 2 + 1)` is algebraically closed
(`isAlgClosed_adjoinRoot`), via a Galois/Sylow argument; the conjugation on `R[i]` then shows the
eigenvalues of a symmetric matrix over `R` are real (`roots_real`, `charpoly_root_real`). Also two
formally-real workhorse lemmas (`isSumSq_eq_zero_of_add`, `dotProduct_self_eq_zero_semireal`).
-/

namespace Hilbert17Blueprint

open Polynomial Matrix

universe u

section Workhorses
/-! ### Formally-real workhorses -/

variable {F : Type*} [Field F] [IsSemireal F]

/-- In a semireal field, a sum of squares whose negative is also a sum of squares is zero:
if `a + b = 0` with `a`, `b` sums of squares, then `a = 0`. -/
theorem isSumSq_eq_zero_of_add {a b : F} (ha : IsSumSq a) (hb : IsSumSq b) (h : a + b = 0) :
    a = 0 := by
  by_contra hne
  refine IsSemireal.not_isSumSq_neg_one F ?_
  have hinv : IsSumSq a⁻¹ := by
    rw [show a⁻¹ = a * (a⁻¹ * a⁻¹) by field_simp]
    exact ha.mul (IsSumSq.mul_self a⁻¹)
  have hb' : b = -a := by linear_combination h
  have : (-1 : F) = b * a⁻¹ := by rw [hb', neg_mul, mul_inv_cancel₀ hne]
  rw [this]; exact hb.mul hinv

/-- Over a semireal field, `∑ᵢ vᵢ² = 0` forces `v = 0`. -/
theorem dotProduct_self_eq_zero_semireal {n : Type*} [Fintype n] {v : n → F}
    (h : ∑ i, v i * v i = 0) : v = 0 := by
  classical
  funext j
  have he := (Finset.add_sum_erase Finset.univ (fun i => v i * v i) (Finset.mem_univ j)).symm
  rw [he] at h
  exact mul_self_eq_zero.1 (isSumSq_eq_zero_of_add (IsSumSq.mul_self (v j))
    (IsSumSq.sum (fun i _ => IsSumSq.mul_self (v i))) h)
end Workhorses

/-! ### (A) Algebraic Fundamental Theorem of Algebra (over a real closed field) -/
section FTA
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **A1.** `X² + 1` is irreducible over a real closed field (`-1` is not a square). **Proved.** -/
theorem irreducible_X_sq_add_one : Irreducible (X ^ 2 + 1 : R[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [← C_1, natDegree_X_pow_add_C]; decide
  · intro x hx
    rw [IsRoot, eval_add, eval_pow, eval_X, eval_one, pow_two] at hx
    have h : (-1 : R) = x * x := by linarith
    exact IsSemireal.not_isSumSq_neg_one R (h ▸ IsSumSq.mul_self x)

/-- **A4** (odd-degree step). Every odd-degree irreducible polynomial over a real closed field is
linear: it has a root by `IsRealClosed.exists_isRoot_of_odd_natDegree`, and an irreducible with a
root has degree 1. This is the "odd part" of the Artin–Schreier induction. -/
theorem natDegree_eq_one_of_irreducible_odd {f : R[X]} (hf : Irreducible f)
    (hodd : Odd f.natDegree) : f.natDegree = 1 := by
  obtain ⟨x, hx⟩ := IsRealClosed.exists_isRoot_of_odd_natDegree hodd
  obtain ⟨c, hc⟩ := dvd_iff_isRoot.2 hx
  rcases hf.isUnit_or_isUnit hc with hu | hu
  · simp [Polynomial.isUnit_iff_degree_eq_zero, degree_X_sub_C] at hu
  · rw [hc, natDegree_mul (X_sub_C_ne_zero x) hu.ne_zero, natDegree_X_sub_C,
        Polynomial.natDegree_eq_zero_of_isUnit hu]

/-- **A2-core** (the real computation behind square roots in `R[i]`). Over a real closed field the
system `c² - d² = a`, `2cd = b` is solvable: set `s = √(a²+b²) ≥ |a|`, then
`c² = (s+a)/2`, `d² = (s-a)/2`
(both nonnegative, hence squares), then fix the sign of `d` so that `2cd = b` (using `(2cd)² = b²`).
**Proved.** -/
theorem exists_sq_sub_sq_and_two_mul (a b : R) :
    ∃ c d : R, c ^ 2 - d ^ 2 = a ∧ 2 * c * d = b := by
  obtain ⟨t, ht⟩ : IsSquare (a ^ 2 + b ^ 2) := IsSquare.of_nonneg (by positivity)
  have hs0 : 0 ≤ |t| := abs_nonneg t
  have hs2 : |t| ^ 2 = a ^ 2 + b ^ 2 := by rw [sq_abs, sq, ← ht]
  have hle : a ^ 2 ≤ |t| ^ 2 := by nlinarith [sq_nonneg b]
  obtain ⟨h1, h2⟩ := abs_le_of_sq_le_sq' hle hs0
  obtain ⟨c, hc⟩ : IsSquare ((|t| + a) / 2) := IsSquare.of_nonneg (by linarith)
  obtain ⟨d, hd⟩ : IsSquare ((|t| - a) / 2) := IsSquare.of_nonneg (by linarith)
  have hc2 : c ^ 2 = (|t| + a) / 2 := by rw [sq]; exact hc.symm
  have hd2 : d ^ 2 = (|t| - a) / 2 := by rw [sq]; exact hd.symm
  have hsub : c ^ 2 - d ^ 2 = a := by rw [hc2, hd2]; ring
  have hprod : (2 * c * d) ^ 2 = b ^ 2 := by
    have h4 : (2 * c * d) ^ 2 = 4 * c ^ 2 * d ^ 2 := by ring
    rw [h4, hc2, hd2]; linear_combination hs2
  rw [sq, sq] at hprod
  rcases mul_self_eq_mul_self_iff.mp hprod with h | h
  · exact ⟨c, d, hsub, h⟩
  · exact ⟨c, -d, by rw [neg_pow]; simpa using hsub, by rw [mul_neg, h]; ring⟩

/-- **A2** (degree-2 step / square-root in `R[i]`). Every element of `R[i] = R[X]/(X²+1)` is a
square. **Proved** by writing `z = of bb + of aa · i` (degree-`< 2` rep via `%ₘ`), solving
`c² - d² = bb`, `2cd = aa` with `exists_sq_sub_sq_and_two_mul`, and squaring `of c + of d · i`
(using `i² = -1`). Equivalently, `R[i]` has no proper degree-2 extension. -/
theorem isSquare_adjoinRoot [Fact (Irreducible (X ^ 2 + 1 : R[X]))]
    (z : AdjoinRoot (X ^ 2 + 1 : R[X])) : IsSquare z := by
  have hgm : (X ^ 2 + 1 : R[X]).Monic := by
    rw [← C_1]; exact monic_X_pow_add_C (a := (1 : R)) two_ne_zero
  have hdeg2 : (X ^ 2 + 1 : R[X]).natDegree = 2 := by rw [← C_1, natDegree_X_pow_add_C]
  have hg1 : (X ^ 2 + 1 : R[X]) ≠ 1 := by
    intro h; rw [h, natDegree_one] at hdeg2; exact absurd hdeg2 (by norm_num)
  have hi : AdjoinRoot.root (X ^ 2 + 1 : R[X]) ^ 2 = -1 := by
    have h := AdjoinRoot.aeval_eq (f := (X ^ 2 + 1 : R[X])) (X ^ 2 + 1)
    rw [AdjoinRoot.mk_self] at h
    simp only [map_add, map_pow, aeval_X, map_one] at h
    exact eq_neg_of_add_eq_zero_left h
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  set q := p %ₘ (X ^ 2 + 1 : R[X]) with hq
  have hmkq : AdjoinRoot.mk (X ^ 2 + 1 : R[X]) p = AdjoinRoot.mk (X ^ 2 + 1 : R[X]) q := by
    rw [hq, AdjoinRoot.mk_eq_mk]
    exact ⟨p /ₘ (X ^ 2 + 1), by rw [modByMonic_eq_sub_mul_div p (X ^ 2 + 1)]; ring⟩
  have hqdeg : q.natDegree ≤ 1 := by
    have h := natDegree_modByMonic_lt p hgm hg1; rw [hdeg2, ← hq] at h; omega
  obtain ⟨aa, bb, hab⟩ := exists_eq_X_add_C_of_natDegree_le_one hqdeg
  obtain ⟨c, d, hc, hd⟩ := exists_sq_sub_sq_and_two_mul bb aa
  refine ⟨AdjoinRoot.of _ c + AdjoinRoot.of _ d * AdjoinRoot.root _, ?_⟩
  rw [hmkq, hab]
  simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X, ← hc, ← hd, map_sub, map_pow,
    map_ofNat]
  linear_combination (-(AdjoinRoot.of (X ^ 2 + 1 : R[X]) d) ^ 2) * hi

/-- In any field of characteristic `≠ 2` in which every element is a square, every degree-2
polynomial has a root — the quadratic formula `z = (-b + √(b²-4ac))/(2a)`. **Proved.** -/
theorem exists_root_deg2 {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (hsq : ∀ x : K, IsSquare x) {p : K[X]} (hp : p.natDegree = 2) : ∃ z, p.IsRoot z := by
  have hp0 : p ≠ 0 := fun h => by simp [h] at hp
  have ha : p.coeff 2 ≠ 0 := by rw [← hp]; exact leadingCoeff_ne_zero.mpr hp0
  set a := p.coeff 2 with haa
  set b := p.coeff 1 with hbb
  set c := p.coeff 0 with hcc
  obtain ⟨s, hs⟩ := hsq (b ^ 2 - 4 * a * c)
  have h2a : 2 * a ≠ 0 := mul_ne_zero h2 ha
  refine ⟨(-b + s) / (2 * a), ?_⟩
  rw [IsRoot, eval_eq_sum_range, hp]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [pow_zero, mul_one, pow_one, ← haa, ← hbb, ← hcc]
  field_simp
  linear_combination -hs

/-- **A2'** (no quadratic extension — the base case). Every degree-2 polynomial over `R[i]` has a
root. **Proved** from A2 (`isSquare_adjoinRoot`: every element of `R[i]` is a square) via the
quadratic formula `exists_root_deg2`. -/
theorem exists_isRoot_of_natDegree_two [Fact (Irreducible (X ^ 2 + 1 : R[X]))]
    {p : (AdjoinRoot (X ^ 2 + 1 : R[X]))[X]} (hp : p.natDegree = 2) : ∃ z, p.IsRoot z := by
  refine exists_root_deg2 ?_ (fun x => isSquare_adjoinRoot x) hp
  have hinj := FaithfulSMul.algebraMap_injective R (AdjoinRoot (X ^ 2 + 1 : R[X]))
  intro h
  exact (two_ne_zero (α := R)) (hinj (by rw [map_ofNat, map_zero, h]))

open Module IntermediateField in
/-- **A-grp** (the mathematical heart of the algebraic FTA). Every finite Galois extension `M` of a
real closed field `R` has degree a power of `2` — equivalently, its Galois group is a `2`-group.
**Proof:** a Sylow `2`-subgroup `P ≤ Gal(M/R)` has odd index, equal to `[fixedField P : R]`
(Galois correspondence + the tower law). A primitive element of `fixedField P / R` then has an
irreducible minimal polynomial of odd degree, which is linear by `A4`
(`natDegree_eq_one_of_irreducible_odd`); so the index is `1`, i.e. `P = ⊤` and `Gal(M/R)` is a
`2`-group. **Proved.** -/
theorem isPGroup_two_galGroup (M : Type*) [Field M] [Algebra R M]
    [FiniteDimensional R M] [IsGalois R M] :
    IsPGroup 2 (M ≃ₐ[R] M) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 (M ≃ₐ[R] M)) := inferInstance
  set E := IntermediateField.fixedField (P : Subgroup (M ≃ₐ[R] M)) with hE
  haveI : Algebra.IsSeparable R M := IsGalois.to_isSeparable
  haveI : Algebra.IsSeparable R E := Algebra.isSeparable_tower_bot_of_isSeparable R E M
  have hfix : finrank E M = Nat.card P := IntermediateField.finrank_fixedField_eq_card _
  have htower : finrank R E * finrank E M = finrank R M := Module.finrank_mul_finrank R E M
  have hcardG : Nat.card (M ≃ₐ[R] M) = finrank R M := IsGalois.card_aut_eq_finrank R M
  have hindex : Nat.card (P : Subgroup (M ≃ₐ[R] M)) * (P : Subgroup (M ≃ₐ[R] M)).index
      = Nat.card (M ≃ₐ[R] M) := Subgroup.card_mul_index _
  have hcardP_pos : 0 < Nat.card P := Nat.card_pos
  have hfinrankE : finrank R E = (P : Subgroup (M ≃ₐ[R] M)).index := by
    have h1 : finrank R E * Nat.card P = (P : Subgroup (M ≃ₐ[R] M)).index * Nat.card P := by
      calc finrank R E * Nat.card P
          = finrank R E * finrank E M := by rw [hfix]
        _ = finrank R M := htower
        _ = Nat.card (M ≃ₐ[R] M) := hcardG.symm
        _ = Nat.card P * (P : Subgroup (M ≃ₐ[R] M)).index := hindex.symm
        _ = (P : Subgroup (M ≃ₐ[R] M)).index * Nat.card P := Nat.mul_comm _ _
    exact Nat.eq_of_mul_eq_mul_right hcardP_pos h1
  haveI : (↑P : Subgroup (M ≃ₐ[R] M)).IsFiniteRelIndex (Subgroup.normalizer ↑P) :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  have hodd : ¬ 2 ∣ finrank R E := by
    rw [hfinrankE]; exact Sylow.not_dvd_index' P Subgroup.relIndex_ne_zero
  obtain ⟨α, hα⟩ := Field.exists_primitive_element R E
  have hint : IsIntegral R α := IsIntegral.of_finite R α
  have hdeg : (minpoly R α).natDegree = finrank R E := by
    rw [← IntermediateField.adjoin.finrank hint, hα]; exact finrank_top R E
  have hirr : Irreducible (minpoly R α) := minpoly.irreducible hint
  have hone : finrank R E = 1 := by
    by_contra h
    have hoddDeg : Odd (minpoly R α).natDegree :=
      Nat.not_even_iff_odd.mp (fun he => hodd (hdeg ▸ even_iff_two_dvd.mp he))
    have := natDegree_eq_one_of_irreducible_odd hirr hoddDeg
    rw [hdeg] at this; exact h this
  have hidx1 : (P : Subgroup (M ≃ₐ[R] M)).index = 1 := by rw [← hfinrankE, hone]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp P.isPGroup'
  refine (IsPGroup.iff_card (p := 2)).mpr ⟨k, ?_⟩
  have : Nat.card (M ≃ₐ[R] M) = Nat.card P := by rw [← hindex, hidx1, mul_one]
  rw [this, hk]

open Module IntermediateField in
/-- **A-noquad.** `R[i] = R[X]/(X²+1)` has no quadratic field extension: a degree-`2` extension `E`
would give a degree-`2` irreducible minimal polynomial of a primitive element over `R[i]`, but `A2'`
(`exists_isRoot_of_natDegree_two`) provides it a root, forcing degree `1`. **Proved.** -/
theorem no_quadratic_ext [Fact (Irreducible (X ^ 2 + 1 : R[X]))]
    (E : Type*) [Field E] [Algebra (AdjoinRoot (X ^ 2 + 1 : R[X])) E]
    [FiniteDimensional (AdjoinRoot (X ^ 2 + 1 : R[X])) E] :
    Module.finrank (AdjoinRoot (X ^ 2 + 1 : R[X])) E ≠ 2 := by
  set K := AdjoinRoot (X ^ 2 + 1 : R[X]) with hK
  intro h2
  haveI : CharZero K := charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective R K)
  haveI : Algebra.IsSeparable K E := inferInstance
  obtain ⟨δ, hδ⟩ := Field.exists_primitive_element K E
  have hint : IsIntegral K δ := IsIntegral.of_finite K δ
  have hdeg : (minpoly K δ).natDegree = 2 := by
    rw [← IntermediateField.adjoin.finrank hint, hδ]
    exact (finrank_top K E).trans h2
  obtain ⟨z, hz⟩ := exists_isRoot_of_natDegree_two (R := R) hdeg
  obtain ⟨c, hc⟩ := dvd_iff_isRoot.2 hz
  rcases (minpoly.irreducible hint).isUnit_or_isUnit hc with hu | hu
  · simp [Polynomial.isUnit_iff_degree_eq_zero, degree_X_sub_C] at hu
  · rw [hc, natDegree_mul (X_sub_C_ne_zero z) hu.ne_zero, natDegree_X_sub_C,
        Polynomial.natDegree_eq_zero_of_isUnit hu] at hdeg
    omega

local notation "K" => AdjoinRoot (X ^ 2 + 1 : R[X])

open Module IntermediateField in
/-- **A-triv.** A finite Galois extension `M` of `K = R[i]` whose degree is a power of `2` is
trivial: a nontrivial one would have an index-`2` subgroup in `Gal(M/K)`
(`Sylow.exists_subgroup_card_pow_prime_of_le_card`), whose fixed field is a degree-`2` extension of
`K`, impossible by `no_quadratic_ext`. **Proved.** -/
theorem galois_trivial_of_pow_two [Fact (Irreducible (X ^ 2 + 1 : R[X]))]
    (M : Type*) [Field M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
    (b : ℕ) (hb : Module.finrank K M = 2 ^ b) : Module.finrank K M = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · rw [hb, hb0, pow_zero]
  · exfalso
    have hG : Nat.card (M ≃ₐ[K] M) = 2 ^ b := by rw [IsGalois.card_aut_eq_finrank, hb]
    haveI hPG : IsPGroup 2 (M ≃ₐ[K] M) := (IsPGroup.iff_card).mpr ⟨b, hG⟩
    obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card (n := b - 1) Nat.prime_two hPG
      (by rw [hG]; exact Nat.pow_le_pow_right (by norm_num) (by omega))
    have hEM : Module.finrank (IntermediateField.fixedField H) M = 2 ^ (b - 1) := by
      rw [IntermediateField.finrank_fixedField_eq_card, hH]
    have htw : Module.finrank K (IntermediateField.fixedField H)
        * Module.finrank (IntermediateField.fixedField H) M = Module.finrank K M :=
      Module.finrank_mul_finrank K (IntermediateField.fixedField H) M
    have hKE : Module.finrank K (IntermediateField.fixedField H) = 2 := by
      rw [hEM, hb] at htw
      have h2 : Module.finrank K (IntermediateField.fixedField H) * 2 ^ (b - 1)
          = 2 * 2 ^ (b - 1) := by rw [htw, ← pow_succ']; congr 1; omega
      exact Nat.eq_of_mul_eq_mul_right (by positivity) h2
    exact no_quadratic_ext (R := R) (IntermediateField.fixedField H) hKE

open Module IntermediateField in
/-- **A.** `R[i] = R[X]/(X²+1)` is algebraically closed (algebraic FTA / Artin–Schreier). **Proved.**
For a monic irreducible `p` over `R[i]`, set `N = AdjoinRoot p` and embed it into the finite Galois
extension `M = normalClosure R N (AlgebraicClosure N)` of `R`. By `isPGroup_two_galGroup`,
`[M : R] = 2ᵃ`, so `[M : R[i]] = 2ᵃ⁻¹` is a power of `2`; `galois_trivial_of_pow_two` forces
`M = R[i]`, whence `[N : R[i]] = 1`, i.e. `p` is linear. `IsAlgClosed.of_exists_root` finishes. -/
theorem isAlgClosed_adjoinRoot [Fact (Irreducible (X ^ 2 + 1 : R[X]))] :
    IsAlgClosed (AdjoinRoot (X ^ 2 + 1 : R[X])) := by
  haveI : CharZero K := charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective R K)
  have hX2ne : (X ^ 2 + 1 : R[X]) ≠ 0 := (Fact.out (p := Irreducible (X ^ 2 + 1 : R[X]))).ne_zero
  haveI : FiniteDimensional R K := (AdjoinRoot.powerBasis hX2ne).finite
  have hKdeg : Module.finrank R K = 2 := by
    rw [(AdjoinRoot.powerBasis hX2ne).finrank, AdjoinRoot.powerBasis_dim, ← C_1,
      natDegree_X_pow_add_C]
  refine IsAlgClosed.of_exists_root K (fun p hpm hpi => ?_)
  suffices hnd : p.natDegree = 1 by
    exact exists_root_of_degree_eq_one (by rw [degree_eq_natDegree hpm.ne_zero, hnd]; rfl)
  haveI : Fact (Irreducible p) := ⟨hpi⟩
  have hpne : p ≠ 0 := hpi.ne_zero
  haveI : FiniteDimensional K (AdjoinRoot p) := (AdjoinRoot.powerBasis hpne).finite
  have hNK : Module.finrank K (AdjoinRoot p) = p.natDegree := by
    rw [(AdjoinRoot.powerBasis hpne).finrank, AdjoinRoot.powerBasis_dim]
  haveI : FiniteDimensional R (AdjoinRoot p) := FiniteDimensional.trans R K (AdjoinRoot p)
  set Ω := AlgebraicClosure (AdjoinRoot p) with hΩ
  set M := normalClosure R (AdjoinRoot p) Ω with hMdef
  haveI : FiniteDimensional R M := normalClosure.is_finiteDimensional R (AdjoinRoot p) Ω
  haveI : IsGalois R M := inferInstance
  -- embeddings `N ↪ M` and `K ↪ M`
  let fΩ : AdjoinRoot p →ₐ[R] Ω := IsScalarTower.toAlgHom R (AdjoinRoot p) Ω
  have hsub : ∀ x, fΩ x ∈ M := fun x => (AlgHom.fieldRange_le_normalClosure fΩ) ⟨x, rfl⟩
  let φ : AdjoinRoot p →ₐ[R] M := fΩ.codRestrict M.toSubalgebra hsub
  let ψ : K →ₐ[R] M := φ.comp (IsScalarTower.toAlgHom R K (AdjoinRoot p))
  letI : Algebra K M := ψ.toAlgebra
  haveI : IsScalarTower R K M := IsScalarTower.of_algebraMap_eq (fun x => (ψ.commutes x).symm)
  haveI : FiniteDimensional K M := FiniteDimensional.right R K M
  haveI : IsGalois K M := IsGalois.tower_top_of_isGalois R K M
  -- `[M : K]` is a power of `2`
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp (isPGroup_two_galGroup (R := R) M)
  rw [IsGalois.card_aut_eq_finrank] at ha
  have hRKM : Module.finrank R K * Module.finrank K M = Module.finrank R M :=
    Module.finrank_mul_finrank R K M
  rw [hKdeg, ha] at hRKM
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | h
    · rw [h0, pow_zero] at hRKM; omega
    · exact h
  have hKMpow : Module.finrank K M = 2 ^ (a - 1) := by
    have h2 : 2 * Module.finrank K M = 2 * 2 ^ (a - 1) := by
      rw [hRKM, ← pow_succ']; congr 1; omega
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
  have hM1 : Module.finrank K M = 1 := galois_trivial_of_pow_two (R := R) M (a - 1) hKMpow
  -- `N ↪ M` is `K`-linear, so `[N : K] ≤ [M : K] = 1`
  let φK : AdjoinRoot p →ₗ[K] M :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun k n => by
        show φ (k • n) = k • φ n
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]; rfl }
  have hinj : Function.Injective φK := φ.injective
  have hle : Module.finrank K (AdjoinRoot p) ≤ Module.finrank K M :=
    φK.finrank_le_finrank_of_injective hinj
  rw [hM1] at hle
  have hN1 : Module.finrank K (AdjoinRoot p) = 1 := le_antisymm hle Module.finrank_pos
  exact hNK.symm.trans hN1


/-! #### Conjugation on `R[i]` and reality of eigenvalues (for B1b) -/

variable [Fact (Irreducible (X ^ 2 + 1 : R[X]))]

theorem root_sq : (AdjoinRoot.root (X ^ 2 + 1 : R[X])) ^ 2 = -1 := by
  have h : aeval (AdjoinRoot.root (X ^ 2 + 1 : R[X])) (X ^ 2 + 1 : R[X]) = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  rw [map_add, map_pow, aeval_X, map_one] at h
  exact eq_neg_of_add_eq_zero_left h

/-- Complex conjugation on `R[i]`, `a + b·i ↦ a - b·i`. -/
noncomputable def conj : K →ₐ[R] K :=
  AdjoinRoot.liftAlgHom (X ^ 2 + 1) (Algebra.ofId R K) (-(AdjoinRoot.root _)) (by
    show aeval (-(AdjoinRoot.root (X ^ 2 + 1 : R[X]))) (X ^ 2 + 1 : R[X]) = 0
    rw [map_add, map_pow, aeval_X, map_one, neg_sq, root_sq]; ring)

@[simp] theorem conj_root : conj (AdjoinRoot.root (X ^ 2 + 1 : R[X])) = -(AdjoinRoot.root _) := by
  simp only [conj, AdjoinRoot.liftAlgHom_root]

theorem conj_algebraMap (r : R) : conj (algebraMap R K r) = algebraMap R K r :=
  conj.commutes r

/-- Every element of `R[i]` is `a·i + b` with `a b : R`. -/
theorem exists_repr (z : K) : ∃ a b : R,
    z = (algebraMap R K a) * (AdjoinRoot.root _) + algebraMap R K b := by
  have hgm : (X ^ 2 + 1 : R[X]).Monic := by
    rw [← C_1]; exact monic_X_pow_add_C (a := (1 : R)) two_ne_zero
  have hdeg2 : (X ^ 2 + 1 : R[X]).natDegree = 2 := by rw [← C_1, natDegree_X_pow_add_C]
  have hg1 : (X ^ 2 + 1 : R[X]) ≠ 1 := by
    intro h; rw [h, natDegree_one] at hdeg2; exact absurd hdeg2 (by norm_num)
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  set q := p %ₘ (X ^ 2 + 1 : R[X]) with hq
  have hmkq : AdjoinRoot.mk (X ^ 2 + 1 : R[X]) p = AdjoinRoot.mk (X ^ 2 + 1 : R[X]) q := by
    rw [hq, AdjoinRoot.mk_eq_mk]
    exact ⟨p /ₘ (X ^ 2 + 1), by rw [modByMonic_eq_sub_mul_div p (X ^ 2 + 1)]; ring⟩
  have hqdeg : q.natDegree ≤ 1 := by
    have h := natDegree_modByMonic_lt p hgm hg1; rw [hdeg2, ← hq] at h; omega
  obtain ⟨aa, bb, hab⟩ := exists_eq_X_add_C_of_natDegree_le_one hqdeg
  refine ⟨aa, bb, ?_⟩
  rw [hmkq, hab]
  simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
  rfl

theorem root_ne_zero : (AdjoinRoot.root (X ^ 2 + 1 : R[X])) ≠ 0 := by
  intro hr; have h := root_sq (R := R); rw [hr] at h; simp at h

/-- A `conj`-fixed element of `R[i]` is real (in the image of `R`). -/
theorem mem_range_of_conj_eq {z : K} (hz : conj z = z) :
    z ∈ (algebraMap R K).range := by
  haveI : CharZero K := charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective R K)
  obtain ⟨a, b, rfl⟩ := exists_repr z
  have hc : conj ((algebraMap R K a) * (AdjoinRoot.root _) + algebraMap R K b)
      = -(algebraMap R K a) * (AdjoinRoot.root _) + algebraMap R K b := by
    rw [map_add, map_mul, conj_root, conj_algebraMap, conj_algebraMap]; ring
  rw [hc] at hz
  have key : (algebraMap R K a) * (AdjoinRoot.root _) * 2 = 0 := by linear_combination -hz
  have ha : a = 0 := by
    have hx : (algebraMap R K a) * (AdjoinRoot.root _) = 0 :=
      (mul_eq_zero.1 key).resolve_right two_ne_zero
    have hz0 : algebraMap R K a = 0 := (mul_eq_zero.1 hx).resolve_right root_ne_zero
    exact FaithfulSMul.algebraMap_injective R K (hz0.trans (map_zero _).symm)
  rw [ha, map_zero, zero_mul, zero_add]
  exact ⟨b, rfl⟩

/-- `conj w * w = (a²+b²)` (real, nonnegative), vanishing only at `w = 0`. -/
theorem conj_mul_self_eq (w : K) :
    ∃ c : R, 0 ≤ c ∧ conj w * w = algebraMap R K c ∧ (c = 0 → w = 0) := by
  obtain ⟨a, b, rfl⟩ := exists_repr w
  refine ⟨a ^ 2 + b ^ 2, by positivity, ?_, ?_⟩
  · rw [map_add, map_mul, conj_root, conj_algebraMap, conj_algebraMap, map_add, map_pow, map_pow]
    linear_combination (-(algebraMap R K a) ^ 2) * root_sq (R := R)
  · intro hc
    have ha2 : a ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg b]) (sq_nonneg a)
    have hb2 : b ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg a]) (sq_nonneg b)
    have ha : a = 0 := pow_eq_zero_iff (by norm_num) |>.mp ha2
    have hb : b = 0 := pow_eq_zero_iff (by norm_num) |>.mp hb2
    rw [ha, hb]; simp

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Hermitian form `vc ⬝ᵥ v` is anisotropic over `R[i]`. -/
theorem dotProduct_conj_self_ne_zero {v : n → K} (hv : v ≠ 0) :
    (fun j => conj (v j)) ⬝ᵥ v ≠ 0 := by
  choose c hc0 hceq hcw using fun j => conj_mul_self_eq (v j)
  have hsum : (fun j => conj (v j)) ⬝ᵥ v = algebraMap R K (∑ j, c j) := by
    rw [map_sum]
    simp only [dotProduct]
    exact Finset.sum_congr rfl (fun j _ => hceq j)
  intro hzero
  rw [hsum] at hzero
  have hcsum : ∑ j, c j = 0 :=
    FaithfulSMul.algebraMap_injective R K (hzero.trans (map_zero _).symm)
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hc0 j)).mp hcsum
  exact hv (funext fun j => hcw j (hall j (Finset.mem_univ j)))

theorem conj_mulVec_map (M : Matrix n n R) (v : n → K) (i : n) :
    conj ((M.map (algebraMap R K) *ᵥ v) i)
      = (M.map (algebraMap R K) *ᵥ (fun j => conj (v j))) i := by
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, conj_algebraMap]

/-- **B1b.** Every `R[i]`-root of `minpoly R A` (for `A` symmetric) is real. -/
theorem roots_real {A : Matrix n n R} (hA : A.IsSymm)
    {z : K} (hz : ((minpoly R A).map (algebraMap R K)).IsRoot z) :
    z ∈ (algebraMap R K).range := by
  have hdvd : (minpoly R A).map (algebraMap R K) ∣ (A.map (algebraMap R K)).charpoly := by
    rw [Matrix.charpoly_map]
    exact Polynomial.map_dvd _ (minpoly.dvd R A (aeval_self_charpoly A))
  have hcroot : (A.map (algebraMap R K)).charpoly.IsRoot z := by
    obtain ⟨g, hg⟩ := hdvd
    rw [IsRoot, hg, eval_mul, IsRoot.def.1 hz, zero_mul]
  have hdet : (Matrix.scalar n z - A.map (algebraMap R K)).det = 0 := by
    rw [← eval_charpoly]; exact hcroot
  obtain ⟨v, hv0, hv'⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hv : (A.map (algebraMap R K)) *ᵥ v = z • v := by
    have hsc : (Matrix.scalar n z) *ᵥ v = z • v := by
      ext i; simp [Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    rw [Matrix.sub_mulVec, hsc, sub_eq_zero] at hv'; exact hv'.symm
  have hAsym : (A.map (algebraMap R K)).IsSymm := by
    rw [Matrix.IsSymm, ← Matrix.transpose_map, hA]
  set vc : n → K := fun j => conj (v j) with hvc
  have hconjeig : (A.map (algebraMap R K)) *ᵥ vc = (conj z) • vc := by
    funext i
    show (A.map (algebraMap R K) *ᵥ (fun j => conj (v j))) i = (conj z • vc) i
    rw [← conj_mulVec_map A v i, congrFun hv i]
    simp [hvc, Pi.smul_apply, smul_eq_mul, map_mul]
  have hL : vc ⬝ᵥ (A.map (algebraMap R K) *ᵥ v) = z * (vc ⬝ᵥ v) := by
    rw [hv, dotProduct_smul, smul_eq_mul]
  have hR : vc ⬝ᵥ (A.map (algebraMap R K) *ᵥ v) = conj z * (vc ⬝ᵥ v) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hAsym.eq, hconjeig, smul_dotProduct, smul_eq_mul]
  have hzz : z = conj z := mul_right_cancel₀ (dotProduct_conj_self_ne_zero hv0) (hL.symm.trans hR)
  exact mem_range_of_conj_eq hzz.symm

/-- Every `R[i]`-root of `charpoly A` (for `A` symmetric) is real (same Hermitian argument as
`roots_real`, but starting from a root of the characteristic polynomial). -/
theorem charpoly_root_real {A : Matrix n n R} (hA : A.IsSymm)
    {z : K} (hz : (A.map (algebraMap R K)).charpoly.IsRoot z) :
    z ∈ (algebraMap R K).range := by
  have hdet : (Matrix.scalar n z - A.map (algebraMap R K)).det = 0 := by
    rw [← eval_charpoly]; exact hz
  obtain ⟨v, hv0, hv'⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hv : (A.map (algebraMap R K)) *ᵥ v = z • v := by
    have hsc : (Matrix.scalar n z) *ᵥ v = z • v := by
      ext i; simp [Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    rw [Matrix.sub_mulVec, hsc, sub_eq_zero] at hv'; exact hv'.symm
  have hAsym : (A.map (algebraMap R K)).IsSymm := by
    rw [Matrix.IsSymm, ← Matrix.transpose_map, hA]
  set vc : n → K := fun j => conj (v j) with hvc
  have hconjeig : (A.map (algebraMap R K)) *ᵥ vc = (conj z) • vc := by
    funext i
    show (A.map (algebraMap R K) *ᵥ (fun j => conj (v j))) i = (conj z • vc) i
    rw [← conj_mulVec_map A v i, congrFun hv i]
    simp [hvc, Pi.smul_apply, smul_eq_mul, map_mul]
  have hL : vc ⬝ᵥ (A.map (algebraMap R K) *ᵥ v) = z * (vc ⬝ᵥ v) := by
    rw [hv, dotProduct_smul, smul_eq_mul]
  have hR : vc ⬝ᵥ (A.map (algebraMap R K) *ᵥ v) = conj z * (vc ⬝ᵥ v) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hAsym.eq, hconjeig, smul_dotProduct, smul_eq_mul]
  have hzz : z = conj z := mul_right_cancel₀ (dotProduct_conj_self_ne_zero hv0) (hL.symm.trans hR)
  exact mem_range_of_conj_eq hzz.symm

end FTA

end Hilbert17Blueprint
