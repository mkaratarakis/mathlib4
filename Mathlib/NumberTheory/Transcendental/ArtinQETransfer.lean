/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.ArtinQESemantic
import Mathlib.NumberTheory.Transcendental.ArtinRealClosureExists

/-!
# The quantifier-free-type transfer for real closed fields

The field-theoretic heart of quantifier elimination for `Theory.RCF`: if parameter tuples in two
real closed ordered fields realize the same quantifier-free formulas, then one-existential
formulas transfer (`realize_ex_transfer`).

The construction: the values of ring terms at the parameters form a subring `termSubring`; the
same-quantifier-free-type hypothesis makes "evaluate the same term at the other tuple" a
well-defined, injective, order-preserving ring homomorphism out of it (equalities `t = t'` and
inequalities `t ≤ t'` of terms are quantifier-free formulas). Lifting to the fraction field `KA`
and taking relative algebraic closures inside `K` and `L` produces two real closures of `KA`
(`isRealClosed_algebraicClosure`), identified by the uniqueness of real closures
(`realClosureAlgEquiv`); since the identification is a `KA`-algebra map, it matches the parameter
tuples. Two applications of the one-existential Tarski transfer `realize_ex_map_iff` then carry
`θ.ex` from `K` down to the real closure and up to `L`.
-/

open FirstOrder Language Polynomial

namespace Artin.ModelTheory

variable {K L : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
  [Field L] [LinearOrder L] [IsStrictOrderedRing L] [IsRealClosed L]
  {α : Type} (va : α → K) (vb : α → L)

/-! ### Term equalities and inequalities as quantifier-free formulas -/

/-- The formula `t = t'` between ring terms, in the ordered-ring language. -/
def teq (t t' : Language.ring.Term α) : orderedRing.Formula α :=
  ((LHom.sumInl : Language.ring →ᴸ orderedRing).onTerm t).equal
    ((LHom.sumInl : Language.ring →ᴸ orderedRing).onTerm t')

/-- The formula `t ≤ t'` between ring terms, in the ordered-ring language. -/
def tle (t t' : Language.ring.Term α) : orderedRing.Formula α :=
  ((((LHom.sumInl : Language.ring →ᴸ orderedRing).onTerm t).relabel Sum.inl).le
    ((((LHom.sumInl : Language.ring →ᴸ orderedRing).onTerm t').relabel Sum.inl)) :
      orderedRing.BoundedFormula α 0)

theorem isQF_teq (t t' : Language.ring.Term α) : (teq t t').IsQF :=
  (BoundedFormula.IsAtomic.equal _ _).isQF

theorem isQF_tle (t t' : Language.ring.Term α) : (tle t t').IsQF :=
  (BoundedFormula.IsAtomic.rel _ _).isQF

omit [IsRealClosed K] in
theorem realize_teq {t t' : Language.ring.Term α} :
    (teq t t').Realize va ↔ t.realize va = t'.realize va := by
  rw [teq, Formula.realize_equal, LHom.realize_onTerm, LHom.realize_onTerm]

omit [IsRealClosed K] in
theorem realize_tle {t t' : Language.ring.Term α} :
    (tle t t').Realize va ↔ t.realize va ≤ t'.realize va := by
  rw [tle, Formula.Realize, Term.realize_le, Term.realize_relabel, Term.realize_relabel,
    LHom.realize_onTerm, LHom.realize_onTerm]
  simp only [Sum.elim_comp_inl]

/-! ### The subring of term values -/

/-- The subring of values of ring terms at the parameter tuple. -/
def termSubring : Subring K where
  carrier := {x | ∃ t : Language.ring.Term α, t.realize va = x}
  zero_mem' := ⟨0, by simp [FirstOrder.Ring.realize_zero]⟩
  one_mem' := ⟨1, by simp [FirstOrder.Ring.realize_one]⟩
  add_mem' := fun ⟨t, ht⟩ ⟨t', ht'⟩ => ⟨t + t', by simp [FirstOrder.Ring.realize_add, ht, ht']⟩
  mul_mem' := fun ⟨t, ht⟩ ⟨t', ht'⟩ => ⟨t * t', by simp [FirstOrder.Ring.realize_mul, ht, ht']⟩
  neg_mem' := fun ⟨t, ht⟩ => ⟨-t, by simp [FirstOrder.Ring.realize_neg, ht]⟩

omit [IsRealClosed K] in
theorem var_mem_termSubring (a : α) : va a ∈ termSubring va :=
  ⟨Term.var a, rfl⟩

section Transfer

variable (htype : ∀ δ : orderedRing.Formula α, δ.IsQF → (δ.Realize va ↔ δ.Realize vb))

omit [IsRealClosed K] [IsRealClosed L] in
include htype in
theorem realize_eq_transfer {t t' : Language.ring.Term α}
    (h : t.realize va = t'.realize va) : t.realize vb = t'.realize vb := by
  have := (htype _ (isQF_teq t t')).mp ((realize_teq va).mpr h)
  exact (realize_teq vb).mp this

omit [IsRealClosed K] [IsRealClosed L] in
include htype in
theorem realize_le_transfer {t t' : Language.ring.Term α}
    (h : t.realize va ≤ t'.realize va) : t.realize vb ≤ t'.realize vb := by
  have := (htype _ (isQF_tle t t')).mp ((realize_tle va).mpr h)
  exact (realize_tle vb).mp this

/-- Evaluate "the same term" at the other parameter tuple: the underlying function of the
transfer homomorphism. -/
noncomputable def transferFun (x : termSubring va) : L :=
  x.2.choose.realize vb

omit [IsRealClosed K] [IsRealClosed L] in
include htype in
theorem transferFun_eq {x : termSubring va} {t : Language.ring.Term α}
    (ht : t.realize va = (x : K)) : transferFun va vb x = t.realize vb :=
  realize_eq_transfer va vb htype (x.2.choose_spec.trans ht.symm)

/-- The transfer ring homomorphism out of the subring of term values. -/
noncomputable def transferHom : termSubring va →+* L where
  toFun := transferFun va vb
  map_zero' := by
    rw [transferFun_eq va vb htype (t := 0) (by simp [FirstOrder.Ring.realize_zero])]
    simp [FirstOrder.Ring.realize_zero]
  map_one' := by
    rw [transferFun_eq va vb htype (t := 1) (by simp [FirstOrder.Ring.realize_one])]
    simp [FirstOrder.Ring.realize_one]
  map_add' := fun x y => by
    obtain ⟨tx, htx⟩ := x.2
    obtain ⟨ty, hty⟩ := y.2
    rw [transferFun_eq va vb htype (x := x + y) (t := tx + ty)
        (by simp [FirstOrder.Ring.realize_add, htx, hty]),
      transferFun_eq va vb htype htx, transferFun_eq va vb htype hty]
    simp [FirstOrder.Ring.realize_add]
  map_mul' := fun x y => by
    obtain ⟨tx, htx⟩ := x.2
    obtain ⟨ty, hty⟩ := y.2
    rw [transferFun_eq va vb htype (x := x * y) (t := tx * ty)
        (by simp [FirstOrder.Ring.realize_mul, htx, hty]),
      transferFun_eq va vb htype htx, transferFun_eq va vb htype hty]
    simp [FirstOrder.Ring.realize_mul]

omit [IsRealClosed K] [IsRealClosed L] in
theorem transferHom_injective : Function.Injective (transferHom va vb htype) := by
  intro x y hxy
  obtain ⟨tx, htx⟩ := x.2
  obtain ⟨ty, hty⟩ := y.2
  rw [show transferHom va vb htype x = tx.realize vb from transferFun_eq va vb htype htx,
    show transferHom va vb htype y = ty.realize vb from transferFun_eq va vb htype hty] at hxy
  have : tx.realize va = ty.realize va := by
    have := (htype _ (isQF_teq tx ty)).mpr ((realize_teq vb).mpr hxy)
    exact (realize_teq va).mp this
  exact Subtype.ext (htx ▸ hty ▸ this)

omit [IsRealClosed K] [IsRealClosed L] in
theorem transferHom_nonneg {x : termSubring va} (hx : 0 ≤ (x : K)) :
    0 ≤ transferHom va vb htype x := by
  obtain ⟨tx, htx⟩ := x.2
  rw [show transferHom va vb htype x = tx.realize vb from transferFun_eq va vb htype htx]
  have h0 : (0 : Language.ring.Term α).realize va ≤ tx.realize va := by
    simpa [FirstOrder.Ring.realize_zero, htx] using hx
  simpa [FirstOrder.Ring.realize_zero] using realize_le_transfer va vb htype h0

omit [IsRealClosed K] [IsRealClosed L] in
theorem transferHom_var (a : α) :
    transferHom va vb htype ⟨va a, var_mem_termSubring va a⟩ = vb a :=
  transferFun_eq va vb htype (t := Term.var a) rfl

/-! ### The transfer of one-existential formulas -/

include htype in
/-- **The quantifier-free-type transfer for real closed fields**: if the parameter tuples `va`
and `vb` realize the same quantifier-free formulas, then one-existential formulas transfer. -/
theorem realize_ex_transfer {θ : orderedRing.BoundedFormula α 1} (hθ : θ.IsQF)
    (hva : θ.ex.Realize va Fin.elim0) : θ.ex.Realize vb Fin.elim0 := by
  classical
  -- the fraction field of the subring of term values
  set A : Subring K := termSubring va with hA
  letI : Algebra A (FractionRing A) := inferInstance
  set KA : Type := FractionRing A with hKA
  -- embeddings into `K` and `L`
  set ιK : KA →+* K := IsFractionRing.lift (g := A.subtype) Subtype.val_injective with hιK
  set e : A →+* L := transferHom va vb htype with he
  set ιL : KA →+* L := IsFractionRing.lift (g := e) (transferHom_injective va vb htype)
    with hιL
  -- order `KA` through `ιK`
  letI : LinearOrder KA := LinearOrder.lift' ιK ιK.injective
  have hιKmono : StrictMono ιK := fun x y h => h
  haveI : IsOrderedAddMonoid KA :=
    { add_le_add_left := fun x y h c => by
        show ιK (x + c) ≤ ιK (y + c)
        rw [map_add, map_add]
        have h' : ιK x ≤ ιK y := h
        exact add_le_add h' le_rfl }
  haveI : ZeroLEOneClass KA := ⟨by
    show ιK 0 ≤ ιK 1
    rw [map_zero, map_one]
    exact zero_le_one⟩
  haveI : IsStrictOrderedRing KA := by
    refine .of_mul_pos fun x y hx hy => ?_
    have : (0 : K) < ιK x * ιK y :=
      mul_pos (by simpa [map_zero] using hιKmono hx) (by simpa [map_zero] using hιKmono hy)
    show ιK 0 < ιK (x * y)
    rw [map_zero, map_mul]
    exact this
  -- `ιL` is monotone
  have hιLmono : Monotone ιL := by
    have key : ∀ z : KA, 0 ≤ z → 0 ≤ ιL z := by
      intro z hz
      obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors A) z
      have hs0 : ((s : A) : K) ≠ 0 := fun h =>
        nonZeroDivisors.coe_ne_zero s (Subtype.ext h)
      have hz' : (0 : K) ≤ ((a : K)) / ((s : A) : K) := by
        have := hιKmono.monotone hz
        rwa [map_zero, hιK, IsFractionRing.lift_mk'] at this
      have hmulK : (0 : K) ≤ (a : K) * ((s : A) : K) := by
        have hrw : (a : K) * ((s : A) : K) = ((a : K) / ((s : A) : K)) * ((s : A) : K) ^ 2 := by
          field_simp
        rw [hrw]
        positivity
      have hmulL : (0 : L) ≤ e (a * (s : A)) := by
        refine transferHom_nonneg va vb htype ?_
        simpa using hmulK
      have hes0 : e (s : A) ≠ 0 := fun h =>
        nonZeroDivisors.coe_ne_zero s (transferHom_injective va vb htype
          (h.trans (map_zero e).symm))
      have : (0 : L) ≤ e a / e (s : A) := by
        rw [map_mul] at hmulL
        rcases (mul_nonneg_iff.mp hmulL) with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact div_nonneg h1 h2
        · rw [div_eq_mul_inv]
          exact mul_nonneg_iff.mpr (Or.inr ⟨h1, inv_nonpos.mpr h2⟩)
      rwa [hιL, IsFractionRing.lift_mk']
    intro x y hxy
    have := key (y - x) (by simpa using hxy)
    rw [map_sub] at this
    linarith
  -- the two relative real closures
  letI : Algebra KA K := ιK.toAlgebra
  letI : Algebra KA L := ιL.toAlgebra
  set RA := algebraicClosure KA K with hRA
  set RB := algebraicClosure KA L with hRB
  letI : IsStrictOrderedRing ↥RA := RA.toSubfield.toIsStrictOrderedRing
  letI : IsStrictOrderedRing ↥RB := RB.toSubfield.toIsStrictOrderedRing
  haveI : IsRealClosed ↥RA := Hilbert17Blueprint.isRealClosed_algebraicClosure
  haveI : IsRealClosed ↥RB := Hilbert17Blueprint.isRealClosed_algebraicClosure
  haveI : Algebra.IsAlgebraic KA ↥RA := ⟨fun x =>
    ((isIntegral_algebraMap_iff (algebraMap ↥RA K).injective).mp
      (mem_algebraicClosure_iff'.mp x.2)).isAlgebraic⟩
  haveI : Algebra.IsAlgebraic KA ↥RB := ⟨fun x =>
    ((isIntegral_algebraMap_iff (algebraMap ↥RB L).injective).mp
      (mem_algebraicClosure_iff'.mp x.2)).isAlgebraic⟩
  -- the identification of the two real closures
  have hcompat : ∀ u v : KA, algebraMap KA ↥RA u ≤ algebraMap KA ↥RA v →
      algebraMap KA ↥RB u ≤ algebraMap KA ↥RB v := by
    intro u v huv
    have h1 : ιK u ≤ ιK v := huv
    have h2 : u ≤ v := (hιKmono.le_iff_le).mp h1
    exact (hιLmono h2 : ιL u ≤ ιL v)
  set g : ↥RA ≃ₐ[KA] ↥RB := Hilbert17Blueprint.realClosureAlgEquiv hcompat with hg
  -- the parameters, viewed inside `RA`
  set xa : α → KA := fun a => algebraMap A KA ⟨va a, var_mem_termSubring va a⟩ with hxa
  set ra : α → ↥RA := fun a => algebraMap KA ↥RA (xa a) with hra
  have hcoeK : ∀ a, ((ra a : K)) = va a := by
    intro a
    show ιK (xa a) = va a
    rw [hxa, hιK, IsFractionRing.lift_algebraMap]
    rfl
  have hcoeL : ∀ a, ((g (ra a) : L)) = vb a := by
    intro a
    rw [hra]
    show ((g (algebraMap KA ↥RA (xa a)) : ↥RB) : L) = vb a
    rw [AlgEquiv.commutes]
    show ιL (xa a) = vb a
    rw [hxa, hιL, IsFractionRing.lift_algebraMap]
    exact transferHom_var va vb htype a
  -- descend from `K` to `RA`, cross to `RB ⊆ L`
  have step1 : θ.ex.Realize ra Fin.elim0 := by
    have := (realize_ex_map_iff (K := ↥RA) (L := K)
      ((algebraMap ↥RA K : ↥RA →+* K)) ra hθ).mp ?_
    · exact this
    · have hfun : (fun a => (algebraMap ↥RA K) (ra a)) = va := funext fun a => hcoeK a
      rw [hfun]
      exact hva
  have step2 : θ.ex.Realize (fun a => ((algebraMap ↥RB L)) (g (ra a))) Fin.elim0 :=
    (realize_ex_map_iff (K := ↥RA) (L := L)
      ((algebraMap ↥RB L : ↥RB →+* L).comp (g : ↥RA →+* ↥RB)) ra hθ).mpr step1
  have hfun : (fun a => (algebraMap ↥RB L) (g (ra a))) = vb := funext fun a => hcoeL a
  rwa [hfun] at step2

end Transfer

end Artin.ModelTheory
