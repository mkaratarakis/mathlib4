/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.Monogenic.CommonIndexDivisor.Split

/-!
# The index of a number field at an unramified prime

Whether `q` divides the index `i(K)` is a property of the finite ring `𝓞 K / q 𝓞 K`: it does exactly
when every `x` in this ring has `1, x, …, x ^ (n - 1)` of zero determinant over `ℤ / q`.  If `p` is
unramified in `K`, then `𝓞 K / p ^ k 𝓞 K` is a product of rings `(ℤ / p ^ k)[X] / (G)`, one for each
prime above `p`, where `G` lifts a monic irreducible polynomial over `𝔽_p` of degree the residue
degree.  Hence at an unramified prime `p`, `ν_p(i(K))` depends only on the residue degrees of the
primes above `p` (Ore).

## Main results

* `NumberField.dvd_fieldIndex_iff_allCoordDetZero`: `q ∣ i(K)` is decided by a finite check on the
  ring `𝓞 K / q 𝓞 K`.
* `NumberField.dvd_fieldIndex_iff_of_ringEquiv`: if `𝓞 K / q 𝓞 K ≅ 𝓞 L / q 𝓞 L` and
  `[K : ℚ] = [L : ℚ]`, then `q ∣ i(K) ↔ q ∣ i(L)`.
* `NumberField.nonempty_quotient_pow_ringEquiv_adjoinRoot`: at an unramified prime `P` of residue
  degree `f`, `𝓞 K / P ^ k ≅ (ℤ / p ^ k)[X] / (G)` with `G` of degree `f`.
* `NumberField.factorization_fieldIndex_eq_of_unramified`: Ore's theorem.

## References

* Ø. Ore, *Newtonsche Polygone in der Theorie der algebraischen Körper*, Math. Ann. **99** (1928),
  84–117.
-/

@[expose] public section

noncomputable section

open Polynomial NumberField Ideal

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

section Unramified

/-- The determinant of `1, x, …, x ^ (n - 1)` in the additive coordinates `c : R ≃+ (ℤ / q) ^ n`. -/
def coordDet {R : Type*} [Ring R] {n q : ℕ} (c : R ≃+ (Fin n → ZMod q)) (x : R) : ZMod q :=
  (Matrix.of fun i j : Fin n ↦ c (x ^ (j : ℕ)) i).det

/-- Whether `coordDet c x` vanishes does not depend on the coordinates `c`. -/
theorem coordDet_eq_zero_iff {R : Type*} [Ring R] {n q : ℕ} (c c' : R ≃+ (Fin n → ZMod q))
    (x : R) : coordDet c' x = 0 ↔ coordDet c x = 0 := by
  let T : (Fin n → ZMod q) →ₗ[ZMod q] (Fin n → ZMod q) :=
    (c.symm.trans c').toAddMonoidHom.toZModLinearMap q
  let T' : (Fin n → ZMod q) →ₗ[ZMod q] (Fin n → ZMod q) :=
    (c'.symm.trans c).toAddMonoidHom.toZModLinearMap q
  have hTT' : LinearMap.toMatrix' T * LinearMap.toMatrix' T' = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    ext v i
    simp [T, T']
  have hunit : IsUnit (LinearMap.toMatrix' T).det :=
    IsUnit.of_mul_eq_one (LinearMap.toMatrix' T').det
      (by rw [← Matrix.det_mul, hTT', Matrix.det_one])
  have hmat : (Matrix.of fun i j : Fin n ↦ c' (x ^ (j : ℕ)) i) =
      LinearMap.toMatrix' T * Matrix.of fun i j : Fin n ↦ c (x ^ (j : ℕ)) i := by
    ext i j
    have := congr_fun (LinearMap.toMatrix'_mulVec T (c (x ^ (j : ℕ)))) i
    simp only [T, AddMonoidHom.coe_toZModLinearMap, AddEquiv.coe_toAddMonoidHom,
      AddEquiv.trans_apply, AddEquiv.symm_apply_apply] at this
    rw [Matrix.of_apply, ← this]
    simp [T, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [coordDet, coordDet, hmat, Matrix.det_mul, hunit.mul_right_eq_zero]

/-- Every `x ∈ R` has `coordDet c x = 0`, in every additive coordinates `c : R ≃+ (ℤ / q) ^ n`. -/
def AllCoordDetZero (R : Type*) [Ring R] (n q : ℕ) : Prop :=
  ∀ (c : R ≃+ (Fin n → ZMod q)) (x : R), coordDet c x = 0

theorem AllCoordDetZero.of_ringEquiv {R R' : Type*} [Ring R] [Ring R'] (φ : R ≃+* R') {n q : ℕ}
    (h : AllCoordDetZero R n q) : AllCoordDetZero R' n q := by
  intro c y
  have := h (φ.toAddEquiv.trans c) (φ.symm y)
  simpa [coordDet, map_pow] using this

/-- `AllCoordDetZero` is invariant under ring isomorphisms. -/
theorem allCoordDetZero_congr {R R' : Type*} [Ring R] [Ring R'] (φ : R ≃+* R') {n q : ℕ} :
    AllCoordDetZero R n q ↔ AllCoordDetZero R' n q :=
  ⟨.of_ringEquiv φ, .of_ringEquiv φ.symm⟩

/-- Coordinates in a basis of `𝓞 K`, reduced modulo `q`. -/
def reduceCoords {n : ℕ} (b : Module.Basis (Fin n) ℤ (𝓞 K)) (q : ℕ) :
    𝓞 K →ₗ[ℤ] (Fin n → ZMod q) :=
  LinearMap.pi fun i ↦ (Int.castAddHom (ZMod q)).toIntLinearMap ∘ₗ b.coord i

omit [NumberField K] in
theorem reduceCoords_apply {n : ℕ} (b : Module.Basis (Fin n) ℤ (𝓞 K)) (q : ℕ) (x : 𝓞 K)
    (i : Fin n) : reduceCoords b q x i = ((b.repr x i : ℤ) : ZMod q) := by
  simp [reduceCoords]

omit [NumberField K] in
theorem reduceCoords_surjective {n : ℕ} (b : Module.Basis (Fin n) ℤ (𝓞 K)) (q : ℕ) [NeZero q] :
    Function.Surjective (reduceCoords b q) := by
  intro v
  refine ⟨b.equivFun.symm fun i ↦ ((v i).val : ℤ), funext fun i ↦ ?_⟩
  rw [reduceCoords_apply, ← b.equivFun_apply, LinearEquiv.apply_symm_apply]
  simp

omit [NumberField K] in
theorem ker_reduceCoords {n : ℕ} (b : Module.Basis (Fin n) ℤ (𝓞 K)) (q : ℕ) :
    LinearMap.ker (reduceCoords b q) = (Ideal.span {(q : 𝓞 K)}).restrictScalars ℤ := by
  ext x
  simp only [LinearMap.mem_ker, Submodule.restrictScalars_mem, Ideal.mem_span_singleton']
  constructor
  · intro h
    have hdvd : ∀ i, (q : ℤ) ∣ b.repr x i := fun i ↦
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp (by rw [← reduceCoords_apply, h]; rfl)
    choose t ht using hdvd
    refine ⟨∑ i, t i • b i, ?_⟩
    conv_rhs => rw [← b.sum_repr x]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [ht i, zsmul_eq_mul, zsmul_eq_mul]
    push_cast
    ring
  · rintro ⟨y, rfl⟩
    funext i
    rw [reduceCoords_apply,
      show y * (q : 𝓞 K) = (q : ℤ) • y by rw [zsmul_eq_mul, Int.cast_natCast, mul_comm],
      map_zsmul, Finsupp.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
      zero_mul]
    rfl

/-- `𝓞 K / q 𝓞 K ≃ (ℤ / q) ^ n`, through the coordinates in a basis of `𝓞 K`. -/
def quotCoords {n : ℕ} (b : Module.Basis (Fin n) ℤ (𝓞 K)) (q : ℕ) [NeZero q] :
    (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) ≃+ (Fin n → ZMod q) :=
  ((Submodule.Quotient.restrictScalarsEquiv ℤ (Ideal.span {(q : 𝓞 K)})).symm.trans
    ((Submodule.quotEquivOfEq _ _ (ker_reduceCoords b q).symm).trans
      (LinearMap.quotKerEquivOfSurjective _ (reduceCoords_surjective b q)))).toAddEquiv

omit [NumberField K] in
theorem quotCoords_mk {n : ℕ} (b : Module.Basis (Fin n) ℤ (𝓞 K)) (q : ℕ) [NeZero q] (x : 𝓞 K) :
    quotCoords b q (Ideal.Quotient.mk _ x) = reduceCoords b q x := by
  rw [← Ideal.Quotient.mk_eq_mk]
  rfl

omit [NumberField K] in
theorem coordDet_quotCoords_mk {n : ℕ} (b : Module.Basis (Fin n) ℤ (𝓞 K)) (q : ℕ) [NeZero q]
    (θ : 𝓞 K) : coordDet (quotCoords b q) (Ideal.Quotient.mk _ θ) =
      ((b.det fun j : Fin n ↦ θ ^ (j : ℕ) : ℤ) : ZMod q) := by
  rw [Module.Basis.det_apply, ← eq_intCast (Int.castRingHom (ZMod q)), RingHom.map_det, coordDet]
  congr 1

/-- **Divisibility of the index is a property of `𝓞 K / q 𝓞 K`.**  For `q ≠ 0`, `q ∣ i(K)` if and
only if in the ring `𝓞 K / q 𝓞 K` every `x` has `1, x, …, x ^ (n - 1)` of zero determinant over
`ℤ / q`, `n = [K : ℚ]`.  This is a finite check on a finite ring. -/
theorem dvd_fieldIndex_iff_allCoordDetZero (q : ℕ) [NeZero q] :
    q ∣ fieldIndex K ↔
      AllCoordDetZero (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) (Module.finrank ℚ K) q := by
  obtain ⟨b⟩ := nonempty_basis_fin (K := K)
  have key : ∀ θ : 𝓞 K, coordDet (quotCoords b q) (Ideal.Quotient.mk _ θ) = 0 ↔
      (q : ℤ) ∣ b.det fun j : Fin (Module.finrank ℚ K) ↦ θ ^ (j : ℕ) := fun θ ↦ by
    rw [coordDet_quotCoords_mk, ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · intro h c x
    obtain ⟨θ, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [coordDet_eq_zero_iff (quotCoords b q) c, key]
    by_cases hθ : Algebra.adjoin ℚ {(θ : K)} = ⊤
    · have := (dvd_fieldIndex_iff K q).mp h θ hθ
      rw [index_eq_natAbs_det hθ b] at this
      exact Int.natCast_dvd.mpr this
    · rw [show (b.det fun j : Fin (Module.finrank ℚ K) ↦ θ ^ (j : ℕ)) = 0 from
        by_contra fun h0 ↦ hθ (adjoin_eq_top_of_det_ne_zero b h0)]
      exact dvd_zero _
  · intro h
    refine (dvd_fieldIndex_iff K q).mpr fun θ hθ ↦ ?_
    rw [index_eq_natAbs_det hθ b]
    exact Int.natCast_dvd.mp ((key θ).mp (h _ _))

/-- If `𝓞 K / q 𝓞 K ≅ 𝓞 L / q 𝓞 L` as rings and `[K : ℚ] = [L : ℚ]`, then `q ∣ i(K) ↔ q ∣ i(L)`. -/
theorem dvd_fieldIndex_iff_of_ringEquiv {L : Type*} [Field L] [NumberField L] (q : ℕ) [NeZero q]
    (hn : Module.finrank ℚ K = Module.finrank ℚ L)
    (φ : (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) ≃+* (𝓞 L ⧸ Ideal.span {(q : 𝓞 L)})) :
    q ∣ fieldIndex K ↔ q ∣ fieldIndex L := by
  rw [dvd_fieldIndex_iff_allCoordDetZero, dvd_fieldIndex_iff_allCoordDetZero, ← hn]
  exact allCoordDetZero_congr φ

/-- In a Dedekind domain, if `x ∈ P \ P ^ 2` and `x y ∈ P ^ (k + 1)` then `y ∈ P ^ k`. -/
theorem mem_pow_of_mul_mem_pow_succ {R : Type*} [CommRing R] [IsDedekindDomain R] {P : Ideal R}
    [hPm : P.IsMaximal] (hP : P ≠ ⊥) {x y : R} (hx : x ∈ P) (hx2 : x ∉ P ^ 2) {k : ℕ}
    (h : x * y ∈ P ^ (k + 1)) : y ∈ P ^ k := by
  obtain ⟨J, hJ⟩ : P ∣ Ideal.span {x} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hx)
  have hJP : ¬ J ≤ P := by
    intro hJ'
    apply hx2
    rw [← Ideal.span_singleton_le_iff_mem, hJ, pow_two]
    exact Ideal.mul_mono_right hJ'
  have h1 : P ^ (k + 1) ∣ Ideal.span {x} * Ideal.span {y} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_le_iff_mem]
    exact h
  rw [hJ, pow_succ', mul_assoc] at h1
  have h2 : P ^ k ∣ J * Ideal.span {y} := (mul_dvd_mul_iff_left (by simpa using hP)).mp h1
  have hcop : IsCoprime (P ^ k) J := by
    refine IsCoprime.pow_left (Ideal.isCoprime_iff_sup_eq.mpr ?_)
    exact hPm.out.2 _ (lt_of_le_of_ne le_sup_left fun h ↦ hJP (le_sup_right.trans h.symm.le))
  exact (Ideal.span_singleton_le_iff_mem _).mp (Ideal.dvd_iff_le.mp (hcop.dvd_of_dvd_mul_left h2))

/-- The ring `(ℤ / q)[X] / (g)` has `q ^ deg g` elements for monic `g`. -/
theorem natCard_adjoinRoot_zmod {q : ℕ} {g : (ZMod q)[X]} (hg : g.Monic) :
    Nat.card (AdjoinRoot g) = q ^ g.natDegree := by
  rw [Nat.card_congr (AdjoinRoot.powerBasis' hg).basis.equivFun.toEquiv, Nat.card_fun,
    Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin, AdjoinRoot.powerBasis'_dim]

variable {p : ℕ} [hp : Fact p.Prime]

/-- `𝓞 K / P ^ k` has `p ^ (f k)` elements, `f` the residue degree of `P`. -/
theorem natCard_quotient_pow_of_mem_primesOver {P : Ideal (𝓞 K)}
    (hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K)) (k : ℕ) :
    Nat.card (𝓞 K ⧸ P ^ k) = (p ^ P.inertiaDeg ℤ) ^ k := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, map_pow, Ideal.absNorm_apply,
    Submodule.cardQuot_apply, natCard_quotient_of_mem_primesOver hP]

/-- At an unramified prime `P` above `p`, `𝓞 K / P ^ k` has characteristic `p ^ k`. -/
theorem charP_quotient_pow (he : ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K), P.ramificationIdx ℤ = 1)
    {P : Ideal (𝓞 K)} (hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K)) (k : ℕ) :
    CharP (𝓞 K ⧸ P ^ k) (p ^ k) :=
  ⟨fun c ↦ by
    rw [← map_natCast (Ideal.Quotient.mk (P ^ k)), Ideal.Quotient.eq_zero_iff_mem]
    refine ⟨dvd_of_natCast_mem_pow he hP, fun ⟨t, ht⟩ ↦ ?_⟩
    rw [ht, Nat.cast_mul, Nat.cast_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (natCast_mem_of_mem_primesOver hP) k)⟩

/-- **Hensel's lemma modulo `P ^ k`.**  A lift `G` of a monic irreducible `σ ∈ 𝔽_p[X]` of degree the
residue degree of `P` has a root modulo every power of `P`. -/
theorem exists_aeval_mem_pow_of_map_eq {P : Ideal (𝓞 K)}
    (hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K)) {σ : (ZMod p)[X]} (hσ : Irreducible σ)
    (hσm : σ.Monic) (hdeg : σ.natDegree = P.inertiaDeg ℤ) {G : ℤ[X]}
    (hGσ : G.map (Int.castRingHom (ZMod p)) = σ) (k : ℕ) : ∃ a : 𝓞 K, aeval a G ∈ P ^ k := by
  haveI : P.IsMaximal := Ideal.primesOver.isMaximal ⟨P, hP⟩
  obtain ⟨a₀, h0, hd0⟩ := exists_aeval_mem_derivative_notMem hP hσ hσm hdeg hGσ
  suffices h : ∀ j : ℕ, ∃ a : 𝓞 K, a - a₀ ∈ P ∧ aeval a G ∈ P ^ (j + 1) by
    obtain ⟨a, -, ha⟩ := h k
    exact ⟨a, Ideal.pow_le_pow_right (Nat.le_succ k) ha⟩
  intro j
  induction j with
  | zero => exact ⟨a₀, by simp, by simpa using h0⟩
  | succ j ih =>
    obtain ⟨a, ha, hG⟩ := ih
    have hd : aeval a (derivative G) ∉ P := by
      intro hda
      apply hd0
      obtain ⟨d, hd⟩ := sub_dvd_eval_sub a a₀ ((derivative G).map (algebraMap ℤ (𝓞 K)))
      rw [eval_map, eval_map, ← aeval_def, ← aeval_def] at hd
      have : aeval a₀ (derivative G) = aeval a (derivative G) - (a - a₀) * d := by
        rw [← hd]
        ring
      rw [this]
      exact sub_mem hda (Ideal.mul_mem_right _ _ ha)
    -- an inverse of `G'(a)` modulo `P`
    obtain ⟨u, hu⟩ : ∃ u : 𝓞 K, aeval a (derivative G) * u - 1 ∈ P := by
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      have hne : Ideal.Quotient.mk P (aeval a (derivative G)) ≠ 0 := by
        rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
      obtain ⟨u, hu⟩ :=
        Ideal.Quotient.mk_surjective (Ideal.Quotient.mk P (aeval a (derivative G)))⁻¹
      refine ⟨u, ?_⟩
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hu, mul_inv_cancel₀ hne, map_one,
        sub_self]
    -- the Newton step `a ↦ a - G(a) u`
    set y := -(aeval a G * u)
    obtain ⟨t, ht⟩ := binomExpansion (G.map (algebraMap ℤ (𝓞 K))) a y
    simp only [eval_map, ← aeval_def, derivative_map] at ht
    have hy : y ∈ P ^ (j + 1) := neg_mem (Ideal.mul_mem_right _ _ hG)
    have hy2 : y ^ 2 ∈ P ^ ((j + 1) * 2) := by
      rw [pow_mul]
      exact Ideal.pow_mem_pow hy 2
    refine ⟨a + y, ?_, ?_⟩
    · rw [add_sub_right_comm]
      exact add_mem ha (Ideal.pow_le_self (Nat.succ_ne_zero j) hy)
    · have e1 : aeval a G + aeval a (derivative G) * y =
          -(aeval a G * (aeval a (derivative G) * u - 1)) := by
        simp only [y]
        ring
      rw [ht, e1]
      refine add_mem (neg_mem ?_) (Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right (by omega) hy2))
      rw [pow_succ]
      exact Ideal.mul_mem_mul hG hu

/-- At an unramified prime `P`, if `σ` is the minimal polynomial of `θ` modulo `P`, an integer
polynomial of degree `< deg σ` that vanishes at `θ` modulo `P ^ k` has all coefficients divisible
by `p ^ k`. -/
theorem pow_dvd_coeff_of_aeval_mem_pow
    (he : ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K), P.ramificationIdx ℤ = 1) {P : Ideal (𝓞 K)}
    (hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K)) {θ : 𝓞 K} {G : ℤ[X]} {σ : (ZMod p)[X]}
    (hσ : Irreducible σ) (hσm : σ.Monic) (hGσ : G.map (Int.castRingHom (ZMod p)) = σ)
    (hG : aeval θ G ∈ P) :
    ∀ (k : ℕ) (T : ℤ[X]), T.degree < σ.degree → aeval θ T ∈ P ^ k →
      ∀ i, (p : ℤ) ^ k ∣ T.coeff i := by
  haveI : P.IsMaximal := Ideal.primesOver.isMaximal ⟨P, hP⟩
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver (span_natCast_ne_bot_of_prime hp.out) hP
  intro k
  induction k with
  | zero => intro _ _ _ _; simp
  | succ k ih =>
    intro T hT hTk i
    have hTP : aeval θ T ∈ P := Ideal.pow_le_self (Nat.succ_ne_zero k) hTk
    have hdvd := (aeval_mem_iff_dvd (natCast_mem_of_mem_primesOver hP) hσ hσm hGσ hG T).mp hTP
    have h0 : T.map (Int.castRingHom (ZMod p)) = 0 :=
      eq_zero_of_dvd_of_degree_lt hdvd (degree_map_le.trans_lt hT)
    obtain ⟨T₁, rfl⟩ : C (p : ℤ) ∣ T := (C_dvd_iff_dvd_coeff _ _).mpr fun j ↦ by
      have := congr_arg (coeff · j) h0
      simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using this
    have hT₁ : T₁.degree < σ.degree := by
      rwa [degree_C_mul (by exact_mod_cast hp.out.ne_zero)] at hT
    have hmem : aeval θ T₁ ∈ P ^ k := by
      rw [map_mul, aeval_C, map_natCast] at hTk
      exact mem_pow_of_mul_mem_pow_succ hP0 (natCast_mem_of_mem_primesOver hP)
        (natCast_notMem_sq_of_unramified he hP) hTk
    rw [coeff_C_mul, pow_succ']
    exact mul_dvd_mul_left _ (ih T₁ hT₁ hmem i)

/-- **The local rings at an unramified prime.**  If `P` is an unramified prime above `p` and `G` is
a monic lift of a monic irreducible `σ ∈ 𝔽_p[X]` of degree the residue degree of `P`, then for
`k ≠ 0`, `𝓞 K / P ^ k ≅ (ℤ / p ^ k)[X] / (G)`. -/
theorem nonempty_quotient_pow_ringEquiv_adjoinRoot
    (he : ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K), P.ramificationIdx ℤ = 1) {P : Ideal (𝓞 K)}
    (hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K)) {σ : (ZMod p)[X]} (hσ : Irreducible σ)
    (hσm : σ.Monic) (hdeg : σ.natDegree = P.inertiaDeg ℤ) {G : ℤ[X]} (hGm : G.Monic)
    (hGσ : G.map (Int.castRingHom (ZMod p)) = σ) {k : ℕ} (hk : k ≠ 0) :
    Nonempty ((𝓞 K ⧸ P ^ k) ≃+* AdjoinRoot (G.map (Int.castRingHom (ZMod (p ^ k))))) := by
  haveI := charP_quotient_pow he hP k
  haveI : Fact (1 < p ^ k) := ⟨Nat.one_lt_pow hk hp.out.one_lt⟩
  set Gq := G.map (Int.castRingHom (ZMod (p ^ k)))
  have hGqm : Gq.Monic := hGm.map _
  obtain ⟨θ, hθ⟩ := exists_aeval_mem_pow_of_map_eq hP hσ hσm hdeg hGσ (k + 1)
  have hθk : aeval θ G ∈ P ^ k := Ideal.pow_le_pow_right (Nat.le_succ k) hθ
  have hθ1 : aeval θ G ∈ P := Ideal.pow_le_self (Nat.succ_ne_zero k) hθ
  have heval : ∀ T : ℤ[X], eval₂ (ZMod.castHom (dvd_refl _) (𝓞 K ⧸ P ^ k))
      (Ideal.Quotient.mk _ θ) (T.map (Int.castRingHom (ZMod (p ^ k)))) =
        Ideal.Quotient.mk _ (aeval θ T) := by
    intro T
    rw [eval₂_map, aeval_def, hom_eval₂]
    congr 1
    exact Subsingleton.elim _ _
  let ψ := AdjoinRoot.lift (ZMod.castHom (dvd_refl _) (𝓞 K ⧸ P ^ k)) (Ideal.Quotient.mk _ θ)
    (by rw [heval, Ideal.Quotient.eq_zero_iff_mem]; exact hθk)
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨r, rfl⟩ := AdjoinRoot.mk_surjective z
    have hr : AdjoinRoot.mk Gq r = AdjoinRoot.mk Gq (r %ₘ Gq) :=
      AdjoinRoot.mk_eq_mk.mpr ⟨r /ₘ Gq, sub_eq_iff_eq_add'.mpr (modByMonic_add_div r Gq).symm⟩
    rw [hr] at hz ⊢
    have ht : (r %ₘ Gq).degree < G.degree := by
      rw [← hGm.degree_map (Int.castRingHom (ZMod (p ^ k)))]
      exact degree_modByMonic_lt r hGqm
    obtain ⟨T, hTt, hTdeg⟩ := exists_degree_eq_of_mem_lifts
      (mem_lifts_of_surjective (ZMod.ringHom_surjective (Int.castRingHom (ZMod (p ^ k))))
        (r %ₘ Gq))
    have hTP : aeval θ T ∈ P ^ k := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← heval, hTt]
      rwa [AdjoinRoot.lift_mk] at hz
    have hσdeg : σ.degree = G.degree := by rw [← hGσ, hGm.degree_map]
    have hcoeff := pow_dvd_coeff_of_aeval_mem_pow he hP hσ hσm hGσ hθ1 k T
      (by rw [hσdeg, hTdeg]; exact ht) hTP
    have hzero : r %ₘ Gq = 0 := by
      rw [← hTt]
      ext i
      rw [coeff_map, coeff_zero, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact_mod_cast hcoeff i
    rw [hzero, map_zero]
  have hdegG : G.natDegree = P.inertiaDeg ℤ := by rw [← hdeg, ← hGσ, hGm.natDegree_map]
  have hcard : Nat.card (AdjoinRoot Gq) = Nat.card (𝓞 K ⧸ P ^ k) := by
    rw [natCard_adjoinRoot_zmod hGqm, natCard_quotient_pow_of_mem_primesOver hP,
      hGm.natDegree_map, hdegG, ← pow_mul, ← pow_mul, mul_comm]
  haveI : Finite (𝓞 K ⧸ P ^ k) := Nat.finite_of_card_ne_zero (by
    rw [natCard_quotient_pow_of_mem_primesOver hP]
    exact pow_ne_zero _ (pow_ne_zero _ hp.out.ne_zero))
  exact ⟨(RingEquiv.ofBijective ψ (hinj.bijective_of_nat_card_le hcard.ge)).symm⟩

/-- **The Chinese remainder theorem at an unramified prime.**
`𝓞 K / p ^ k 𝓞 K ≅ ∏_{P ∣ p} 𝓞 K / P ^ k`. -/
theorem nonempty_quotient_span_pow_ringEquiv_pi
    (he : ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K), P.ramificationIdx ℤ = 1) (k : ℕ) :
    Nonempty ((𝓞 K ⧸ Ideal.span {((p ^ k : ℕ) : 𝓞 K)}) ≃+*
      ((P : primesOver (span {(p : ℤ)}) (𝓞 K)) → 𝓞 K ⧸ (P : Ideal (𝓞 K)) ^ k)) := by
  classical
  have hpb := span_natCast_ne_bot_of_prime hp.out
  refine ⟨IsDedekindDomain.quotientEquivPiOfProdEq _
    (fun P : primesOver (span {(p : ℤ)}) (𝓞 K) ↦ (P : Ideal (𝓞 K))) (fun _ ↦ k)
    (fun P ↦ Ideal.prime_of_isPrime (Ideal.ne_bot_of_mem_primesOver hpb P.2) P.2.1)
    (fun P Q hPQ h ↦ hPQ (Subtype.ext h)) ?_⟩
  rw [Nat.cast_pow, ← Ideal.span_singleton_pow, span_natCast_eq_prod_of_unramified he,
    ← Finset.prod_pow, Finset.prod_subtype _ (fun _ ↦ Set.mem_toFinset)]

omit hp in
/-- Primes above `p` of residue degree `c`, counted as a subtype. -/
theorem natCard_primesOver_inertiaDeg_eq {F : Type*} [Field F] (c : ℕ) :
    Nat.card {P : primesOver (span {(p : ℤ)}) (𝓞 F) // (P : Ideal (𝓞 F)).inertiaDeg ℤ = c} =
      {P ∈ primesOver (span {(p : ℤ)}) (𝓞 F) | P.inertiaDeg ℤ = c}.ncard := by
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
    (· ∈ primesOver (span {(p : ℤ)}) (𝓞 F)) (fun P ↦ P.inertiaDeg ℤ = c))

/-- If `p` has, for every `f`, as many primes of residue degree `f` in `K` as in `L`, there is a
bijection between the primes above `p` in `K` and in `L` preserving residue degrees. -/
theorem exists_equiv_primesOver_inertiaDeg {L : Type*} [Field L] [NumberField L]
    (h : ∀ f : ℕ, {P ∈ primesOver (span {(p : ℤ)}) (𝓞 K) | P.inertiaDeg ℤ = f}.ncard =
      {P ∈ primesOver (span {(p : ℤ)}) (𝓞 L) | P.inertiaDeg ℤ = f}.ncard) :
    ∃ τ : primesOver (span {(p : ℤ)}) (𝓞 K) ≃ primesOver (span {(p : ℤ)}) (𝓞 L),
      ∀ P, (τ P : Ideal (𝓞 L)).inertiaDeg ℤ = (P : Ideal (𝓞 K)).inertiaDeg ℤ := by
  classical
  have hfib : ∀ c : ℕ,
      Nonempty ({P : primesOver (span {(p : ℤ)}) (𝓞 K) // (P : Ideal (𝓞 K)).inertiaDeg ℤ = c} ≃
        {Q : primesOver (span {(p : ℤ)}) (𝓞 L) // (Q : Ideal (𝓞 L)).inertiaDeg ℤ = c}) := by
    intro c
    letI := Fintype.ofFinite
      {P : primesOver (span {(p : ℤ)}) (𝓞 K) // (P : Ideal (𝓞 K)).inertiaDeg ℤ = c}
    letI := Fintype.ofFinite
      {Q : primesOver (span {(p : ℤ)}) (𝓞 L) // (Q : Ideal (𝓞 L)).inertiaDeg ℤ = c}
    exact ⟨Fintype.equivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, natCard_primesOver_inertiaDeg_eq,
        natCard_primesOver_inertiaDeg_eq, h c])⟩
  let e := fun c ↦ (hfib c).some
  exact ⟨Equiv.ofFiberEquiv e, fun P ↦ Equiv.ofFiberEquiv_map e P⟩

/-- **Ore's theorem for unramified primes.**  If `p` is unramified in `K` and in `L`, and for every
`f` there are as many primes above `p` of residue degree `f` in `K` as in `L`, then for every `k`,
`p ^ k ∣ i(K) ↔ p ^ k ∣ i(L)`. -/
theorem pow_dvd_fieldIndex_iff_of_unramified {L : Type*} [Field L] [NumberField L]
    (hK : ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K), P.ramificationIdx ℤ = 1)
    (hL : ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 L), P.ramificationIdx ℤ = 1)
    (h : ∀ f : ℕ, {P ∈ primesOver (span {(p : ℤ)}) (𝓞 K) | P.inertiaDeg ℤ = f}.ncard =
      {P ∈ primesOver (span {(p : ℤ)}) (𝓞 L) | P.inertiaDeg ℤ = f}.ncard) (k : ℕ) :
    p ^ k ∣ fieldIndex K ↔ p ^ k ∣ fieldIndex L := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  obtain ⟨τ, hτ⟩ := exists_equiv_primesOver_inertiaDeg (K := K) (L := L) h
  -- the degrees agree
  have hn : Module.finrank ℚ K = Module.finrank ℚ L := by
    haveI := Int.ideal_span_isMaximal_of_prime p
    rw [← RingOfIntegers.rank K, ← RingOfIntegers.rank L,
      ← Ideal.sum_ramification_inertia_eq_finrank (span {(p : ℤ)}) (𝓞 K),
      ← Ideal.sum_ramification_inertia_eq_finrank (span {(p : ℤ)}) (𝓞 L),
      ← Equiv.sum_comp τ (fun Q ↦ (Q : Ideal (𝓞 L)).ramificationIdx ℤ *
        (Q : Ideal (𝓞 L)).inertiaDeg ℤ)]
    refine Finset.sum_congr rfl fun P _ ↦ ?_
    rw [hK P P.2, hL _ (τ P).2, hτ]
  -- a monic irreducible polynomial of each residue degree, with a monic integral lift
  have hσ : ∀ P : primesOver (span {(p : ℤ)}) (𝓞 K), ∃ G : ℤ[X], G.Monic ∧
      Irreducible (G.map (Int.castRingHom (ZMod p))) ∧
      (G.map (Int.castRingHom (ZMod p))).natDegree = (P : Ideal (𝓞 K)).inertiaDeg ℤ := by
    intro P
    haveI : (P : Ideal (𝓞 K)).IsPrime := P.2.1
    have hf0 : (P : Ideal (𝓞 K)).inertiaDeg ℤ ≠ 0 :=
      (Ideal.inertiaDeg_pos (R := ℤ) (P : Ideal (𝓞 K))).ne'
    obtain ⟨σ, hσm, hσi, hσd⟩ := Set.nonempty_of_ncard_ne_zero (s := {g : (ZMod p)[X] |
        g.Monic ∧ Irreducible g ∧ g.natDegree = (P : Ideal (𝓞 K)).inertiaDeg ℤ}) (fun h0 ↦ by
      have := Polynomial.prime_le_mul_ncard_monic_irreducible p hf0
      rw [h0, mul_zero] at this
      exact hp.out.ne_zero (Nat.le_zero.mp this))
    obtain ⟨G, hGσ, -, hGm⟩ := lifts_and_natDegree_eq_and_monic
      (mem_lifts_of_surjective (ZMod.ringHom_surjective (Int.castRingHom (ZMod p))) σ) hσm
    exact ⟨G, hGm, hGσ ▸ hσi, hGσ ▸ hσd⟩
  choose G hGm hGi hGd using hσ
  -- the local rings correspond
  have hcomp : ∀ P : primesOver (span {(p : ℤ)}) (𝓞 K),
      Nonempty ((𝓞 K ⧸ (P : Ideal (𝓞 K)) ^ k) ≃+* (𝓞 L ⧸ (τ P : Ideal (𝓞 L)) ^ k)) := by
    intro P
    obtain ⟨φK⟩ := nonempty_quotient_pow_ringEquiv_adjoinRoot hK P.2 (hGi P) ((hGm P).map _)
      (hGd P) (hGm P) rfl hk
    obtain ⟨φL⟩ := nonempty_quotient_pow_ringEquiv_adjoinRoot hL (τ P).2 (hGi P)
      ((hGm P).map _) (by rw [hGd P, hτ]) (hGm P) rfl hk
    exact ⟨φK.trans φL.symm⟩
  let φ := fun P ↦ (hcomp P).some
  obtain ⟨cK⟩ := nonempty_quotient_span_pow_ringEquiv_pi (K := K) hK k
  obtain ⟨cL⟩ := nonempty_quotient_span_pow_ringEquiv_pi (K := L) hL k
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  exact dvd_fieldIndex_iff_of_ringEquiv (p ^ k) hn (cK.trans ((RingEquiv.piCongrRight φ).trans
    ((RingEquiv.piCongrLeft (fun Q : primesOver (span {(p : ℤ)}) (𝓞 L) ↦
      𝓞 L ⧸ (Q : Ideal (𝓞 L)) ^ k) τ).trans cL.symm)))

/-- **Ore's theorem for unramified primes.**  If `p` is unramified in `K` and in `L`, and for every
`f` there are as many primes above `p` of residue degree `f` in `K` as in `L`, then
`ν_p(i(K)) = ν_p(i(L))`: at an unramified prime, the index of a number field is determined by the
residue degrees of the primes above `p`. -/
theorem factorization_fieldIndex_eq_of_unramified {L : Type*} [Field L] [NumberField L]
    (hK : ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K), P.ramificationIdx ℤ = 1)
    (hL : ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 L), P.ramificationIdx ℤ = 1)
    (h : ∀ f : ℕ, {P ∈ primesOver (span {(p : ℤ)}) (𝓞 K) | P.inertiaDeg ℤ = f}.ncard =
      {P ∈ primesOver (span {(p : ℤ)}) (𝓞 L) | P.inertiaDeg ℤ = f}.ncard) :
    (fieldIndex K).factorization p = (fieldIndex L).factorization p := by
  have hK0 := fieldIndex_ne_zero (K := K)
  have hL0 := fieldIndex_ne_zero (K := L)
  have hiff := fun k ↦ pow_dvd_fieldIndex_iff_of_unramified hK hL h k
  apply le_antisymm
  · rw [← hp.out.pow_dvd_iff_le_factorization hL0, ← hiff]
    exact Nat.ordProj_dvd _ _
  · rw [← hp.out.pow_dvd_iff_le_factorization hK0, hiff]
    exact Nat.ordProj_dvd _ _

end Unramified

end NumberField
