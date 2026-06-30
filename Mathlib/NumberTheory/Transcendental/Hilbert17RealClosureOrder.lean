/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.Hilbert17RealClosure

/-!
# Real closure of an ordered field, II: the order refinement

Part of the real-closed-field input to Hilbert's 17th problem for matrices
(see `Mathlib.NumberTheory.Transcendental.Hilbert17`).

A real closed field carries a canonical order given by its sums of squares (`sosLinearOrder`).
Combined with a weighted-sums-of-squares Zorn argument over an algebraic closure, this yields a
real closure of any ordered field: `exists_realClosure`.
-/

namespace Hilbert17Blueprint

open Polynomial Matrix

universe u

section RealClosedOrder
variable (R : Type*) [Field R] [IsRealClosed R]

/-- The sums of squares of a field form a subsemiring. -/
def sosSubsemiring : Subsemiring R where
  carrier := {x | IsSumSq x}
  mul_mem' ha hb := IsSumSq.mul ha hb
  one_mem' := by simpa using IsSumSq.mul_self (1 : R)
  add_mem' ha hb := IsSumSq.add ha hb
  zero_mem' := IsSumSq.zero

/-- **E4a (cone).** In a real closed field the sums of squares form a (positive) ring cone: a
subsemiring in which `x` and `-x` are both sums of squares only when `x = 0` (formal reality —
otherwise `-1 = (-x)·x·(x⁻¹)²` would be a sum of squares). -/
def sosRingCone : RingCone R where
  __ := sosSubsemiring R
  eq_zero_of_mem_of_neg_mem' {a} ha hna := by
    by_contra h
    have ha' : IsSumSq a := ha
    have hna' : IsSumSq (-a) := hna
    refine IsSemireal.not_isSumSq_neg_one R ?_
    have hxinv : IsSumSq a⁻¹ := by
      have e : a⁻¹ = a * (a⁻¹ * a⁻¹) := by field_simp
      rw [e]; exact ha'.mul (IsSumSq.mul_self _)
    have e2 : (-1 : R) = (-a) * a⁻¹ := by field_simp
    rw [e2]; exact hna'.mul hxinv

/-- The SOS cone of a real closed field is total: every element or its negation is a sum of
squares (indeed a square). -/
instance : HasMemOrNegMem (sosRingCone R) where
  mem_or_neg_mem x := by
    rcases IsRealClosed.isSquare_or_isSquare_neg (R := R) x with h | h
    · exact Or.inl h.isSumSq
    · exact Or.inr h.isSumSq

open scoped Classical in
/-- **E4a (order).** The canonical linear order on a real closed field: `x ≤ y` iff `y - x` is a
sum of squares. -/
noncomputable def sosLinearOrder : LinearOrder R :=
  LinearOrder.mkOfAddGroupCone (sosRingCone R)

open scoped Classical in
/-- **E4a (strict ordered ring).** The canonical order makes a real closed field a strict ordered
ring (`mkOfCone` gives `IsOrderedRing`; a field is a domain, so it upgrades to strict). -/
noncomputable def sosIsStrictOrderedRing :
    letI := sosLinearOrder R; IsStrictOrderedRing R := by
  letI := sosLinearOrder R
  haveI : IsOrderedRing R := IsOrderedRing.mkOfCone (sosRingCone R)
  infer_instance

end RealClosedOrder

section RealClosureExistence
open IntermediateField


variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- **Weighted sums of squares.** Over an `F`-algebra `K`, the elements `∑ pᵢ · zᵢ²` with the
weights `pᵢ` nonnegative elements of the ordered field `F`. This is the cone tracking `F`'s order
through algebraic extensions. -/
inductive IsWSumSq {K : Type*} [CommSemiring K] [Algebra F K] : K → Prop
  | zero : IsWSumSq 0
  | add_wsq (p : F) (hp : 0 ≤ p) (z : K) {s : K} (h : IsWSumSq s) :
      IsWSumSq (algebraMap F K p * (z * z) + s)

namespace IsWSumSq

variable {K : Type*} [CommRing K] [Algebra F K]

theorem add {a b : K} (ha : IsWSumSq (F := F) a) (hb : IsWSumSq (F := F) b) :
    IsWSumSq (F := F) (a + b) := by
  induction ha with
  | zero => rwa [zero_add]
  | add_wsq p hp z h ih => rw [add_assoc]; exact IsWSumSq.add_wsq p hp z ih

theorem sq (z : K) : IsWSumSq (F := F) (z * z) := by
  have := IsWSumSq.add_wsq (K := K) (1 : F) zero_le_one z IsWSumSq.zero
  simpa using this

theorem weight {p : F} (hp : 0 ≤ p) : IsWSumSq (F := F) (algebraMap F K p) := by
  have := IsWSumSq.add_wsq (K := K) p hp 1 IsWSumSq.zero
  simpa using this

theorem mul {a b : K} (ha : IsWSumSq (F := F) a) (hb : IsWSumSq (F := F) b) :
    IsWSumSq (F := F) (a * b) := by
  induction ha with
  | zero => simpa using IsWSumSq.zero
  | add_wsq p hp z h ih =>
      rw [add_mul]
      refine IsWSumSq.add ?_ ih
      clear ih h
      induction hb with
      | zero => simpa using IsWSumSq.zero
      | add_wsq q hq w h2 ih2 =>
          rw [mul_add]
          refine IsWSumSq.add ?_ ih2
          have hpq : (0:F) ≤ p * q := mul_nonneg hp hq
          have key : algebraMap F K p * (z * z) * (algebraMap F K q * (w * w))
              = algebraMap F K (p * q) * ((z * w) * (z * w)) + 0 := by
            rw [map_mul]; ring
          rw [key]
          exact IsWSumSq.add_wsq (p * q) hpq (z * w) IsWSumSq.zero

/-- When every nonnegative weight is a square in `K`, weighted sums of squares are ordinary sums of
squares. -/
theorem isSumSq_of_weights_isSquare {a : K}
    (hsq : ∀ p : F, 0 ≤ p → IsSquare (algebraMap F K p)) (ha : IsWSumSq (F := F) a) :
    IsSumSq a := by
  induction ha with
  | zero => exact IsSumSq.zero
  | add_wsq p hp z h ih =>
      obtain ⟨r, hr⟩ := hsq p hp
      have : algebraMap F K p * (z * z) = (r * z) * (r * z) := by rw [hr]; ring
      rw [this]
      exact IsSumSq.add (IsSumSq.mul_self _) ih

/-- In the ordered field `F` itself, a weighted sum of squares is nonnegative. -/
theorem nonneg_self {a : F} (ha : IsWSumSq (F := F) (K := F) a) : 0 ≤ a := by
  induction ha with
  | zero => exact le_refl 0
  | add_wsq p hp z h ih =>
      have hpp : algebraMap F F p = p := rfl
      have h1 : 0 ≤ algebraMap F F p * (z * z) := by
        rw [hpp]; exact mul_nonneg hp (mul_self_nonneg z)
      linarith

/-- Weighted sums of squares are preserved by `F`-algebra homomorphisms. -/
theorem algHom_map {K L : Type*} [CommRing K] [CommRing L] [Algebra F K] [Algebra F L]
    (φ : K →ₐ[F] L) {a : K} (ha : IsWSumSq (F := F) a) : IsWSumSq (F := F) (φ a) := by
  induction ha with
  | zero => simpa using IsWSumSq.zero
  | add_wsq p hp z h ih =>
      rw [map_add, map_mul, map_mul, AlgHom.commutes]
      exact IsWSumSq.add_wsq p hp (φ z) ih

end IsWSumSq

/-- An `F`-algebra is **good** if `-1` is not a weighted sum of squares
(i.e. `F`'s order extends to it). -/
def Good (K : Type*) [CommRing K] [Algebra F K] : Prop := ¬ IsWSumSq (F := F) (-1 : K)

variable {Ω : Type*} [Field Ω] [Algebra F Ω]

/-- A weighted sum of squares in a directed supremum descends to a member. -/
theorem isWSumSq_iSup_descend {ι : Type*} [Nonempty ι] {E : ι → IntermediateField F Ω}
    (dir : Directed (· ≤ ·) E) {s : ↥(⨆ i, E i)} (hs : IsWSumSq (F := F) s) :
    ∃ i, ∃ t : ↥(E i), IsWSumSq (F := F) t ∧ inclusion (le_iSup E i) t = s := by
  induction hs with
  | zero => exact ⟨Classical.arbitrary ι, 0, IsWSumSq.zero, map_zero _⟩
  | @add_wsq p hp z st h ih =>
      obtain ⟨k, t', ht', hteq⟩ := ih
      obtain ⟨j, hzj⟩ : ∃ j, (z : Ω) ∈ E j := by
        have hz := z.2
        rwa [← SetLike.mem_coe, IntermediateField.coe_iSup_of_directed dir, Set.mem_iUnion] at hz
      obtain ⟨m, hjm, hkm⟩ := dir j k
      refine ⟨m, algebraMap F ↥(E m) p * (inclusion hjm ⟨(z : Ω), hzj⟩ * inclusion hjm ⟨(z : Ω), hzj⟩)
        + inclusion hkm t', IsWSumSq.add_wsq p hp _ (IsWSumSq.algHom_map (inclusion hkm) ht'), ?_⟩
      apply Subtype.ext
      have hz' : ((inclusion (le_iSup E m) (inclusion hjm ⟨(z : Ω), hzj⟩) : ↥(⨆ i, E i)) : Ω)
          = (z : Ω) := by rw [inclusion_inclusion]; rfl
      have ht'' : ((inclusion (le_iSup E m) (inclusion hkm t') : ↥(⨆ i, E i)) : Ω) = (st : Ω) := by
        rw [inclusion_inclusion, coe_inclusion]
        have := congrArg (Subtype.val) hteq
        rwa [coe_inclusion] at this
      push_cast [map_add, map_mul, AlgHom.commutes]
      rw [hz', ht'']

/-- **Chain condition.** A directed family of good intermediate fields has a good supremum. -/
theorem good_iSup_of_directed {ι : Type*} [Nonempty ι] {E : ι → IntermediateField F Ω}
    (dir : Directed (· ≤ ·) E) (hE : ∀ i, Good (F := F) ↥(E i)) : Good (F := F) ↥(⨆ i, E i) := by
  intro hsos
  obtain ⟨i, t, htsos, hteq⟩ := isWSumSq_iSup_descend dir hsos
  have ht1 : t = -1 := inclusion_injective (le_iSup E i) (by rw [hteq, map_neg, map_one])
  rw [ht1] at htsos
  exact hE i htsos

/-- **The preordering of weighted sums of squares** in a good field. -/
def wsosPreordering {K : Type*} [Field K] [Algebra F K] (hgood : Good (F := F) K) :
    RingPreordering K :=
  RingPreordering.mk' {z | IsWSumSq (F := F) z}
    (fun ha hb => IsWSumSq.add ha hb) (fun ha hb => IsWSumSq.mul ha hb)
    (fun x => IsWSumSq.sq x) hgood

theorem mem_wsosPreordering {K : Type*} [Field K] [Algebra F K] (hgood : Good (F := F) K)
    {z : K} : z ∈ wsosPreordering hgood ↔ IsWSumSq (F := F) z := Iff.rfl

/-- The base field `⊥ ≅ F` is good (in `F` a weighted sum of squares is nonnegative, so `≠ -1`). -/
theorem good_bot : Good (F := F) ↥(⊥ : IntermediateField F Ω) := by
  intro h
  have h2 := IsWSumSq.algHom_map (IntermediateField.botEquiv F Ω).toAlgHom h
  rw [map_neg, map_one] at h2
  have := IsWSumSq.nonneg_self h2
  linarith

/-- **The order-tracking Zorn (E4b core).** There is a maximal good intermediate field. -/
theorem exists_maximal_good :
    ∃ R : IntermediateField F Ω, Good (F := F) ↥R ∧
      ∀ E : IntermediateField F Ω, R ≤ E → Good (F := F) ↥E → E = R := by
  obtain ⟨R, hR⟩ := zorn_le₀ {E : IntermediateField F Ω | Good (F := F) ↥E}
    (fun c hcS hchain => by
      rcases c.eq_empty_or_nonempty with rfl | hne
      · exact ⟨⊥, good_bot, by simp⟩
      · refine ⟨sSup c, ?_, fun z hz => le_sSup hz⟩
        rw [Set.mem_setOf_eq, sSup_eq_iSup']
        haveI : Nonempty ↥c := hne.to_subtype
        exact good_iSup_of_directed
          (fun a b => (hchain.total a.2 b.2).elim
            (fun h => ⟨b, h, le_rfl⟩) (fun h => ⟨a, le_rfl, h⟩))
          (fun i => hcS i.2))
  exact ⟨R, hR.1, fun E hRE hE => le_antisymm (hR.2 hE hRE) hRE⟩

variable [IsAlgClosed Ω]

/-- **Good connection lemma** (mirror of `hmax_of_maximal`). A maximal good intermediate field has
no proper good simple algebraic extension. -/
theorem good_hmax_of_maximal {R : IntermediateField F Ω}
    (hRmax : ∀ E : IntermediateField F Ω, R ≤ E → Good (F := F) ↥E → E = R)
    (q : (↥R)[X]) (hqm : q.Monic) (hqirr : Irreducible q) (hq2 : 2 ≤ q.natDegree) :
    ¬ Good (F := F) (AdjoinRoot q) := by
  intro hsemi
  haveI : Fact (Irreducible q) := ⟨hqirr⟩
  have hdeg0 : q.degree ≠ 0 := by
    rw [degree_eq_natDegree hqm.ne_zero]; exact_mod_cast (by omega : q.natDegree ≠ 0)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_aeval_eq_zero (k := Ω) q hdeg0
  have hint : IsIntegral (↥R) α := ⟨q, hqm, hα⟩
  have hminpoly : minpoly (↥R) α = q := (minpoly.eq_of_irreducible_of_monic hqirr hα hqm).symm
  set Rα : IntermediateField (↥R) Ω := IntermediateField.adjoin (↥R) {α} with hRα
  have hsemi' : Good (F := F) ↥Rα := by
    intro h
    refine hsemi ?_
    have e : AdjoinRoot q ≃ₐ[↥R] ↥Rα := hminpoly ▸ adjoinRootEquivAdjoin (↥R) hint
    have := IsWSumSq.algHom_map (e.symm.restrictScalars F).toAlgHom h
    rwa [map_neg, map_one] at this
  set E : IntermediateField F Ω := Rα.restrictScalars F with hE
  have hRE : R ≤ E := fun y hy => by
    rw [hE, mem_restrictScalars]
    simpa using IntermediateField.algebraMap_mem Rα (⟨y, hy⟩ : ↥R)
  have hER : E = R := hRmax E hRE hsemi'
  have hαE : α ∈ E := by
    rw [hE, mem_restrictScalars]; exact IntermediateField.mem_adjoin_simple_self (↥R) α
  rw [hER] at hαE
  have hle : (minpoly (↥R) α).natDegree ≤ 1 := by
    have hdvd : minpoly (↥R) α ∣ (X - C (⟨α, hαE⟩ : ↥R)) :=
      minpoly.dvd (↥R) α (by rw [map_sub, aeval_X, aeval_C, sub_eq_zero]; rfl)
    have := natDegree_le_of_dvd hdvd (X_sub_C_ne_zero _)
    rwa [natDegree_X_sub_C] at this
  rw [hminpoly] at hle
  omega

/-- **Weighted √-adjunction.** Over a field `K` with an ordering `O` containing the images of `F`'s
nonnegative elements, adjoining `√x` for `x ∈ O` keeps the field good: `-1` is not a weighted sum
of squares of `K(√x)`. (Real-part argument: `re` of a weighted sum of squares lies in `O`, but
`re(-1) = -1 ∉ O`.) -/
theorem good_adjoinRoot_sqrt {K : Type*} [Field K] [Algebra F K] (O : RingPreordering K)
    [O.IsOrdering] (hFO : ∀ p : F, 0 ≤ p → algebraMap F K p ∈ O) {x : K} (hx : x ∈ O)
    (hirr : Irreducible (X ^ 2 - C x)) : Good (F := F) (AdjoinRoot (X ^ 2 - C x)) := by
  haveI : Fact (Irreducible (X ^ 2 - C x)) := ⟨hirr⟩
  set K' := AdjoinRoot (X ^ 2 - C x) with hK'
  have hne : (X ^ 2 - C x) ≠ 0 := hirr.ne_zero
  set pb := AdjoinRoot.powerBasis hne with hpb
  have hdim : pb.dim = 2 := by rw [hpb, AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C]
  set b : Module.Basis (Fin 2) K K' := pb.basis.reindex (finCongr hdim) with hb
  have hgen : pb.gen = AdjoinRoot.root (X ^ 2 - C x) := by simp [hpb, AdjoinRoot.powerBasis_gen]
  have hval0 : (((finCongr hdim).symm 0 : Fin pb.dim) : ℕ) = 0 := by simp
  have hval1 : (((finCongr hdim).symm 1 : Fin pb.dim) : ℕ) = 1 := by simp
  have hb0 : b 0 = 1 := by
    rw [hb, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, hval0, pow_zero]
  have hb1 : b 1 = AdjoinRoot.root (X ^ 2 - C x) := by
    rw [hb, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, hval1, pow_one, hgen]
  set re : K' →ₗ[K] K := b.coord 0 with hre
  have hre1 : re 1 = 1 := by rw [hre, ← hb0, Module.Basis.coord_apply, b.repr_self_apply]; simp
  have hre_root : re (AdjoinRoot.root (X ^ 2 - C x)) = 0 := by
    rw [hre, ← hb1, Module.Basis.coord_apply, b.repr_self_apply]; simp
  have hre_smul1 (c : K) : re (algebraMap K K' c) = c := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hre1, smul_eq_mul, mul_one]
  have hroot2 : (AdjoinRoot.root (X ^ 2 - C x)) ^ 2 = algebraMap K K' x := by
    have h : aeval (AdjoinRoot.root (X ^ 2 - C x)) (X ^ 2 - C x) = 0 := by
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    rw [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at h
    exact h
  have hdecomp (z : K') : z = algebraMap K K' (re z) + algebraMap K K' (b.coord 1 z)
      * AdjoinRoot.root (X ^ 2 - C x) := by
    conv_lhs => rw [← b.sum_repr z, Fin.sum_univ_two, hb0, hb1]
    rw [hre, Module.Basis.coord_apply, Module.Basis.coord_apply, Algebra.smul_def, Algebra.smul_def,
      mul_one]
  have hre_sq (z : K') : re (z ^ 2) = (re z) ^ 2 + x * (b.coord 1 z) ^ 2 := by
    set c := re z with hc
    set d := b.coord 1 z with hd
    have hz2 : z ^ 2 = algebraMap K K' (c ^ 2 + x * d ^ 2)
        + algebraMap K K' (2 * c * d) * AdjoinRoot.root (X ^ 2 - C x) := by
      rw [hdecomp z, ← hc, ← hd]
      simp only [map_add, map_mul, map_pow, map_ofNat]
      linear_combination (algebraMap K K' d) ^ 2 * hroot2
    rw [hz2, map_add, hre_smul1,
      show algebraMap K K' (2 * c * d) * AdjoinRoot.root (X ^ 2 - C x)
        = (2 * c * d) • AdjoinRoot.root (X ^ 2 - C x) from (Algebra.smul_def _ _).symm,
      map_smul, hre_root, smul_zero, add_zero]
  have hOre : ∀ z : K', IsWSumSq (F := F) z → re z ∈ O := by
    intro z hz
    induction hz with
    | zero => rw [map_zero]; exact zero_mem O
    | add_wsq p hp w h ih =>
        rw [map_add]
        refine add_mem ?_ ih
        have hpK : algebraMap F K' p = algebraMap K K' (algebraMap F K p) :=
          IsScalarTower.algebraMap_apply F K K' p
        rw [hpK, ← Algebra.smul_def, map_smul, smul_eq_mul,
          show w * w = w ^ 2 from (sq w).symm, hre_sq w]
        exact mul_mem (hFO p hp)
          (add_mem (O.pow_two_mem _) (mul_mem hx (O.pow_two_mem _)))
  intro hsos
  have hmem : re (-1 : K') ∈ O := hOre _ hsos
  rw [show (-1 : K') = algebraMap K K' (-1) by simp, hre_smul1] at hmem
  exact O.neg_one_notMem (by simpa using hmem)

/-- Ordinary sums of squares are weighted sums of squares (weight `1`). -/
theorem IsWSumSq.of_isSumSq {K : Type*} [CommRing K] [Algebra F K] {a : K} (h : IsSumSq a) :
    IsWSumSq (F := F) a := by
  induction h with
  | zero => exact IsWSumSq.zero
  | sq_add y _ ih => simpa using IsWSumSq.add_wsq (1 : F) zero_le_one y ih

/-- Over a field, `X² - C y` is irreducible when `y` is not a square. -/
theorem irreducible_X_sq_sub_C_of_not_isSquare {K : Type*} [Field K] {y : K}
    (hns : ¬ IsSquare y) : Irreducible (X ^ 2 - C y) := by
  have hmon : (X ^ 2 - C y : K[X]).Monic := monic_X_pow_sub_C y two_ne_zero
  have hdeg : (X ^ 2 - C y : K[X]).natDegree = 2 := natDegree_X_pow_sub_C
  have hne1 : (X ^ 2 - C y : K[X]) ≠ 1 := fun h => by rw [h, natDegree_one] at hdeg; omega
  rw [hmon.irreducible_iff_lt_natDegree_lt hne1]
  intro q hq hmem hdvd
  rw [hdeg] at hmem
  simp only [Finset.mem_Ioc] at hmem
  have hq1 : q.natDegree = 1 := by omega
  have hc1 : q.coeff 1 = 1 := by rw [← hq1]; exact hq.coeff_natDegree
  have hqeq : q = X + C (q.coeff 0) := by
    have h := eq_X_add_C_of_natDegree_le_one (le_of_eq hq1)
    rwa [hc1, map_one, one_mul] at h
  have hroot : (X ^ 2 - C y).IsRoot (-(q.coeff 0)) := by
    obtain ⟨c, hc⟩ := hdvd
    rw [IsRoot, hc, eval_mul, show q.eval (-(q.coeff 0)) = 0 from by rw [hqeq]; simp, zero_mul]
  rw [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hroot
  exact hns ⟨-(q.coeff 0), by rw [← hroot]; ring⟩

/-- **E4b: real closure of an ordered field exists.** -/
theorem exists_realClosure' : Nonempty (RealClosure F) := by
  obtain ⟨R, hRgood, hRmax⟩ := exists_maximal_good (F := F) (Ω := AlgebraicClosure F)
  haveI hsemiR : IsSemireal ↥R := by
    rw [isSemireal_iff_not_isSumSq_neg_one]
    exact fun h => hRgood (IsWSumSq.of_isSumSq h)
  obtain ⟨O, hO, hTO⟩ := RingPreordering.exists_isOrdering_ge (wsosPreordering hRgood)
  haveI := hO
  have hFO : ∀ p : F, 0 ≤ p → algebraMap F ↥R p ∈ O := fun p hp =>
    hTO ((mem_wsosPreordering hRgood).mpr (IsWSumSq.weight hp))
  have ha : ∀ y : ↥R, y ∈ O → IsSquare y := by
    intro y hy
    by_contra hns
    have hirr := irreducible_X_sq_sub_C_of_not_isSquare hns
    have hmon : (X ^ 2 - C y : (↥R)[X]).Monic := monic_X_pow_sub_C y two_ne_zero
    exact good_hmax_of_maximal hRmax _ hmon hirr (le_of_eq natDegree_X_pow_sub_C.symm)
      (good_adjoinRoot_sqrt O hFO hy hirr)
  have abs_hmax : ∀ q : (↥R)[X], q.Monic → Irreducible q → 2 ≤ q.natDegree →
      ¬ IsSemireal (AdjoinRoot q) := by
    intro q hqm hqirr hq2 hsemiq
    have hwsq : ∀ p : F, 0 ≤ p → IsSquare (algebraMap F (AdjoinRoot q) p) := by
      intro p hp
      obtain ⟨s, hs⟩ := ha (algebraMap F ↥R p) (hFO p hp)
      exact ⟨algebraMap (↥R) (AdjoinRoot q) s, by
        rw [← map_mul, ← hs, ← IsScalarTower.algebraMap_apply]⟩
    have hng : IsWSumSq (F := F) (-1 : AdjoinRoot q) :=
      not_not.mp (good_hmax_of_maximal hRmax q hqm hqirr hq2)
    exact (isSemireal_iff_not_isSumSq_neg_one.mp hsemiq)
      (IsWSumSq.isSumSq_of_weights_isSquare hwsq hng)
  haveI hRC : IsRealClosed ↥R := isRealClosed_of_maximal abs_hmax
  letI lo : LinearOrder ↥R := RingPreordering.toLinearOrder O
  haveI so : IsStrictOrderedRing ↥R := RingPreordering.toIsStrictOrderedRing O
  have hmono : Monotone (algebraMap F ↥R) := by
    intro a b hab
    rw [← sub_nonneg, RingPreordering.toLinearOrder_nonneg_iff, ← map_sub]
    exact hFO (b - a) (by linarith)
  exact ⟨{ carrier := ↥R, emb := algebraMap F ↥R, monotone_emb := hmono }⟩

end RealClosureExistence

/-- **Existence of a real closure of an ordered field.** Every ordered field has a real closure
(a real closed field with an order-preserving embedding). Construction, broken into steps:
* **E1.** Fix an algebraic closure `F̄ := AlgebraicClosure F`.
* **E2.** By Zorn, pick an intermediate field `R`, `F ≤ R ≤ F̄`, maximal among those that are
  *formally real* (`IsSemireal`) — chains of formally real subfields have a formally real union.
* **E3.** Such a maximal `R` is **real closed** (`IsRealClosed R`): formally real; each element
  or its negation is a square (else a proper formally real quadratic extension `R(√x) ≤ F̄`); and
  every odd-degree polynomial has a root (else a proper formally real odd-degree extension).
* **E4.** The order of `R` (from `IsSemireal` + the square structure of E3) extends that of `F`,
  giving the monotone embedding.
Consumed by `isSumSq_minpoly_signedCoeff` (D-transfer). -/
theorem exists_realClosure (F : Type u) [Field F] [LinearOrder F] [IsStrictOrderedRing F] :
    Nonempty (RealClosure F) := exists_realClosure'

end Hilbert17Blueprint
