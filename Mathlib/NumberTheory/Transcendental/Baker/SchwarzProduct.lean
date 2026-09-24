/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.NumberTheory.Transcendental.Baker.CoordinateDivision
public import Mathlib.NumberTheory.Transcendental.Baker.Polydisc
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Schwarz's lemma for Cartesian products

A function analytic on the polydisc of polyradius `R` in `ℂⁿ` and vanishing to order `m` in
each coordinate at every point of a product `E₁ × ⋯ × Eₙ` of finite sets in the disc of
radius `r` is small on the polydisc of polyradius `r`.  This is Proposition 4.7 of Waldschmidt,
*Diophantine Approximation on Linear Algebraic Groups*.

## The proof

This is the argument of Waldschmidt's Lemma 4.8, organised as operations on functions rather
than on an ideal.  Newton division in one coordinate (`MultiIndex.exists_newton`), applied to
each coordinate in turn (`MultiIndex.exists_newton_finset`), writes `f` as a polynomial main
term with constant coefficients plus, for each coordinate `i`, the product
`∏_{ζ ∈ E i} (z i - ζ) ^ m` times an analytic function whose size is controlled.  The
vanishing of `f` forces the main term to be zero (`MultiIndex.eq_zero_of_tensor`,
`MultiIndex.newton_eq_zero_of_taylor`), and each remaining product is small on the polydisc
of polyradius `r`.

## Main statements

* `MultiIndex.norm_le_of_taylorCoeff_eq_zero`: Proposition 4.7, with explicit constants.
* `MultiIndex.norm_le_of_taylorCoeff_eq_zero_of_five_mul_le`: the same for `R ≥ 5r`, in the
  form `‖f‖ ≤ n (5 · 3ⁿ r / R) ^ (mS) M`.
-/

@[expose] public section

open Metric Function Filter Topology
open scoped NNReal ENNReal

/-!
### Newton division in one coordinate

Dividing successively by `z i - L 0, z i - L 1, …, z i - L (p - 1)` writes an analytic function
on a polydisc in Newton form
`g = ∑_{k < p} (∏_{l < k} (z i - L l)) • a k + (∏_{l < p} (z i - L l)) • q`, with `a k` not
depending on `z i`.  Each division costs a factor `2 / (R - r)` in the sup norm on the
polydisc of polyradius `R`, by the maximum modulus principle.
-/

namespace MultiIndex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

/-- `g` does not depend on the `j`-th coordinate. -/
def IndepOf (g : (ι → ℂ) → V) (j : ι) : Prop := ∀ (z : ι → ℂ) (w : ℂ), g (update z j w) = g z

omit [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] in
lemma indepOf_const (v : V) (j : ι) : IndepOf (fun _ : ι → ℂ => v) j := fun _ _ => rfl

omit [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] in
lemma indepOf_comp_update (g : (ι → ℂ) → V) (i : ι) (ζ : ℂ) :
    IndepOf (fun z => g (update z i ζ)) i := fun z w => by simp [update_idem]

omit [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] in
lemma IndepOf.comp_update {g : (ι → ℂ) → V} {i j : ι} (hji : j ≠ i) (hg : IndepOf g j) (ζ : ℂ) :
    IndepOf (fun z => g (update z i ζ)) j := fun z w => by
  simp only
  rw [update_comm hji, hg]

omit [Fintype ι] [CompleteSpace V] in
lemma IndepOf.dslope_slice {g : (ι → ℂ) → V} {i j : ι} (hji : j ≠ i) (hg : IndepOf g j)
    (ζ : ℂ) : IndepOf (fun z => dslope (slice g i z) ζ (z i)) j := fun z w => by
  have hsl : slice g i (update z j w) = slice g i z := by
    funext v
    simp only [slice]
    rw [update_comm hji, hg]
  simp only
  rw [hsl, update_of_ne hji.symm]

omit [DecidableEq ι] [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] in
lemma norm_update_le [DecidableEq ι] {y : ι → ℂ} {R : ℝ} (hy : ‖y‖ ≤ R) (i : ι) {v : ℂ}
    (hv : ‖v‖ ≤ R) : ‖update y i v‖ ≤ R := by
  have hR : 0 ≤ R := (norm_nonneg y).trans hy
  refine (pi_norm_le_iff_of_nonneg hR).2 fun j => ?_
  rcases eq_or_ne j i with rfl | hj
  · simpa using hv
  · rw [update_of_ne hj]; exact (norm_le_pi_norm y j).trans hy

/-- **One division by a linear factor, with its estimate.**  On the polydisc of polyradius
`R`, the divided difference of `g` in the `i`-th coordinate at a point `ζ` of the disc of
radius `r < R` is analytic and bounded by `2 / (R - r)` times a bound for `g`. -/
theorem dslope_slice_bound {g : (ι → ℂ) → V} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (i : ι)
    {ζ : ℂ} (hζ : ‖ζ‖ ≤ r) (hg : ∀ y : ι → ℂ, ‖y‖ ≤ R → AnalyticAt ℂ g y) :
    (∀ y : ι → ℂ, ‖y‖ ≤ R → AnalyticAt ℂ (fun z => dslope (slice g i z) ζ (z i)) y) ∧
      ∀ M : ℝ, (∀ y : ι → ℂ, ‖y‖ ≤ R → ‖g y‖ ≤ M) →
        ∀ y : ι → ℂ, ‖y‖ ≤ R → ‖dslope (slice g i y) ζ (y i)‖ ≤ 2 / (R - r) * M := by
  have hζR : ‖ζ‖ ≤ R := hζ.trans hrR.le
  have han : ∀ y : ι → ℂ, ‖y‖ ≤ R → AnalyticAt ℂ (fun z => dslope (slice g i z) ζ (z i)) y :=
    fun y hy => analyticAt_dslope_slice i ζ (hg y hy) (hg _ (norm_update_le hy i hζR))
  refine ⟨han, fun M hM y hy => ?_⟩
  have hbd := Complex.norm_le_of_eq_prod_smul (S := {ζ}) (m := 1) (M := 2 * M) hr hrR
    (by simpa using hζ) i han
    (f := fun z => g z - g (update z i ζ))
    (fun z _ => by simpa using (sub_smul_dslope_slice g i ζ z).symm)
    (fun z hz => (norm_sub_le _ _).trans (by
      linarith [hM z hz, hM _ (norm_update_le hz i hζR)])) y hy
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hbd

/-- **Newton division in one coordinate.**

For nodes `L 0, L 1, …` in the disc of radius `r < R` and an analytic `g` on the polydisc of
polyradius `R`, there are analytic `a k` not depending on `z i`, and an analytic `q`, with
`g = ∑_{k < p} (∏_{l < k} (z i - L l)) • a k + (∏_{l < p} (z i - L l)) • q`.  If `‖g‖ ≤ M` then
`‖a k‖ ≤ (2 / (R - r)) ^ k * M` and `‖q‖ ≤ (2 / (R - r)) ^ p * M`; and `a k`, `q` do not depend
on any coordinate `j ≠ i` that `g` does not depend on. -/
theorem exists_newton {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (i : ι) :
    ∀ (p : ℕ) (L : ℕ → ℂ), (∀ k, ‖L k‖ ≤ r) → ∀ {g : (ι → ℂ) → V},
      (∀ y : ι → ℂ, ‖y‖ ≤ R → AnalyticAt ℂ g y) →
      ∃ (a : ℕ → (ι → ℂ) → V) (q : (ι → ℂ) → V),
        (∀ k (y : ι → ℂ), ‖y‖ ≤ R → AnalyticAt ℂ (a k) y) ∧
        (∀ y : ι → ℂ, ‖y‖ ≤ R → AnalyticAt ℂ q y) ∧
        (∀ k, IndepOf (a k) i) ∧
        (∀ j, j ≠ i → IndepOf g j → (∀ k, IndepOf (a k) j) ∧ IndepOf q j) ∧
        (∀ z : ι → ℂ, g z = ∑ k ∈ Finset.range p, (∏ l ∈ Finset.range k, (z i - L l)) • a k z +
          (∏ l ∈ Finset.range p, (z i - L l)) • q z) ∧
        ∀ M : ℝ, (∀ y : ι → ℂ, ‖y‖ ≤ R → ‖g y‖ ≤ M) →
          (∀ k < p, ∀ y : ι → ℂ, ‖y‖ ≤ R → ‖a k y‖ ≤ (2 / (R - r)) ^ k * M) ∧
          ∀ y : ι → ℂ, ‖y‖ ≤ R → ‖q y‖ ≤ (2 / (R - r)) ^ p * M := by
  intro p
  induction p with
  | zero =>
    intro L _ g hg
    refine ⟨fun _ _ => 0, g, fun _ _ _ => analyticAt_const, hg, fun _ => indepOf_const 0 i,
      fun j _ hgj => ⟨fun _ => indepOf_const 0 j, hgj⟩, fun z => by simp, fun M hM => ?_⟩
    exact ⟨fun k hk => absurd hk (Nat.not_lt_zero k), fun y hy => by simpa using hM y hy⟩
  | succ p ih =>
    intro L hL g hg
    have hL0R : ‖L 0‖ ≤ R := (hL 0).trans hrR.le
    set a₀ : (ι → ℂ) → V := fun z => g (update z i (L 0)) with ha₀
    obtain ⟨hg₁an, hg₁bd⟩ := dslope_slice_bound hr hrR i (hL 0) hg
    obtain ⟨a', q', ha'an, hq'an, ha'i, ha'j, hid, hbd⟩ :=
      ih (fun k => L (k + 1)) (fun k => hL (k + 1)) hg₁an
    refine ⟨fun k => if k = 0 then a₀ else a' (k - 1), q', fun k y hy => ?_, hq'an,
      fun k => ?_, fun j hji hgj => ?_, fun z => ?_, fun M hM => ?_⟩
    · by_cases hk : k = 0
      · simp only [hk, ↓reduceIte]
        exact analyticAt_comp_update i (L 0) (hg _ (norm_update_le hy i hL0R))
      · simp only [hk, ↓reduceIte]
        exact ha'an _ y hy
    · by_cases hk : k = 0
      · simp only [hk, ↓reduceIte]
        exact indepOf_comp_update g i (L 0)
      · simp only [hk, ↓reduceIte]
        exact ha'i _
    · obtain ⟨h1, h2⟩ := ha'j j hji (hgj.dslope_slice hji (L 0))
      refine ⟨fun k => ?_, h2⟩
      by_cases hk : k = 0
      · simp only [hk, ↓reduceIte]
        exact hgj.comp_update hji (L 0)
      · simp only [hk, ↓reduceIte]
        exact h1 _
    · have hstep : g z = a₀ z + (z i - L 0) • dslope (slice g i z) (L 0) (z i) := by
        rw [ha₀, sub_smul_dslope_slice]
        abel
      rw [hstep, hid z, Finset.sum_range_succ', Finset.prod_range_succ']
      simp only [Finset.prod_range_zero, one_smul, ↓reduceIte,
        Nat.add_sub_cancel, Nat.succ_ne_zero]
      rw [smul_add, Finset.smul_sum]
      have hterm : ∀ k ∈ Finset.range p,
          (z i - L 0) • (∏ l ∈ Finset.range k, (z i - L (l + 1))) • a' k z
            = (∏ l ∈ Finset.range (k + 1), (z i - L l)) • a' k z := by
        intro k _
        rw [smul_smul, Finset.prod_range_succ', mul_comm]
      rw [Finset.sum_congr rfl hterm, smul_smul, mul_comm]
      abel
    · have hg₁M := hg₁bd M hM
      obtain ⟨hak, hq⟩ := hbd (2 / (R - r) * M) hg₁M
      refine ⟨fun k hk y hy => ?_, fun y hy => ?_⟩
      · by_cases hk0 : k = 0
        · simp only [hk0, ↓reduceIte, pow_zero, one_mul]
          exact hM _ (norm_update_le hy i hL0R)
        · simp only [hk0, ↓reduceIte]
          obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
          have := hak k' (by omega) y hy
          simp only [Nat.succ_sub_one]
          calc ‖a' k' y‖ ≤ (2 / (R - r)) ^ k' * (2 / (R - r) * M) := this
            _ = (2 / (R - r)) ^ (k' + 1) * M := by ring
      · calc ‖q' y‖ ≤ (2 / (R - r)) ^ p * (2 / (R - r) * M) := hq y hy
          _ = (2 / (R - r)) ^ (p + 1) * M := by ring

end MultiIndex

/-!
### Newton division in all coordinates

Applying `exists_newton` coordinate by coordinate writes `f` as a sum of a *main term*, a
combination of products of Newton basis polynomials in the separate coordinates, and one
*error term* `(∏_{l < p} (z i - L i l)) • Q i` for each coordinate.  Once every coordinate has
been processed the coefficients of the main term are constants.
-/

namespace MultiIndex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

/-- The Newton basis polynomial `∏_{l < k} (z j - L j l)` in the `j`-th coordinate. -/
def nodeProd (L : ι → ℕ → ℂ) (j : ι) (k : ℕ) (z : ι → ℂ) : ℂ :=
  ∏ l ∈ Finset.range k, (z j - L j l)

omit [DecidableEq ι] in
lemma analyticAt_nodeProd (L : ι → ℕ → ℂ) (j : ι) (k : ℕ) (y : ι → ℂ) :
    AnalyticAt ℂ (nodeProd L j k) y :=
  Finset.analyticAt_fun_prod _ fun _ _ =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) j).analyticAt y).sub
      analyticAt_const

omit [DecidableEq ι] in
lemma norm_nodeProd_le {L : ι → ℕ → ℂ} {r R : ℝ} (hL : ∀ j k, ‖L j k‖ ≤ r) (j : ι) (k : ℕ)
    {z : ι → ℂ} (hz : ‖z‖ ≤ R) : ‖nodeProd L j k z‖ ≤ (R + r) ^ k := by
  rw [nodeProd, norm_prod]
  calc ∏ l ∈ Finset.range k, ‖z j - L j l‖ ≤ ∏ _l ∈ Finset.range k, (R + r) := by
        gcongr with l hl
        exact (norm_sub_le _ _).trans (add_le_add ((norm_le_pi_norm z j).trans hz) (hL j l))
    _ = (R + r) ^ k := by simp

omit [Fintype ι] [DecidableEq ι] in
lemma nodeProd_update_of_ne (L : ι → ℕ → ℂ) {i j : ι} [DecidableEq ι] (hji : j ≠ i) (k : ℕ)
    (z : ι → ℂ) (w : ℂ) : nodeProd L j k (update z i w) = nodeProd L j k z := by
  simp [nodeProd, update_of_ne hji]

/-- The multi-indices with entries `< p` on `J` and `0` off `J`. -/
def boxH (J : Finset ι) (p : ℕ) : Finset (ι → ℕ) :=
  Fintype.piFinset fun j => if j ∈ J then Finset.range p else {0}

lemma mem_boxH {J : Finset ι} {p : ℕ} {h : ι → ℕ} :
    h ∈ boxH J p ↔ ∀ j, (j ∈ J → h j < p) ∧ (j ∉ J → h j = 0) := by
  simp only [boxH, Fintype.mem_piFinset]
  refine forall_congr' fun j => ?_
  by_cases hj : j ∈ J <;> simp [hj]

lemma boxH_empty (p : ℕ) : boxH (∅ : Finset ι) p = {0} := by
  have : boxH (∅ : Finset ι) p = Fintype.piFinset fun j : ι => ({(0 : ι → ℕ) j} : Finset ℕ) := by
    simp [boxH]
  rw [this, Fintype.piFinset_singleton]

lemma boxH_univ (p : ℕ) : boxH (Finset.univ : Finset ι) p =
    Fintype.piFinset fun _ : ι => Finset.range p := by
  simp [boxH]

/-- Summing over `boxH (insert i₀ J)` is summing over `boxH J` and then over the new
coordinate. -/
lemma sum_boxH_insert {W : Type*} [AddCommMonoid W] {J : Finset ι} {i₀ : ι} (hi₀ : i₀ ∉ J)
    (p : ℕ) (g : (ι → ℕ) → W) :
    ∑ h ∈ boxH (insert i₀ J) p, g h =
      ∑ h ∈ boxH J p, ∑ k ∈ Finset.range p, g (update h i₀ k) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun h => (update h i₀ 0, h i₀)) (fun hk => update hk.1 i₀ hk.2)
    ?_ ?_ ?_ ?_ ?_
  · intro h hh
    rw [mem_boxH] at hh
    simp only [Finset.mem_product, Finset.mem_range, mem_boxH]
    refine ⟨fun j => ⟨fun hj => ?_, fun hj => ?_⟩, (hh i₀).1 (Finset.mem_insert_self _ _)⟩
    · rw [update_of_ne (by rintro rfl; exact hi₀ hj)]
      exact (hh j).1 (Finset.mem_insert_of_mem hj)
    · rcases eq_or_ne j i₀ with rfl | hj'
      · simp
      · rw [update_of_ne hj']
        exact (hh j).2 (by simp [hj, hj'])
  · rintro ⟨h, k⟩ hhk
    simp only [Finset.mem_product, Finset.mem_range, mem_boxH] at hhk
    rw [mem_boxH]
    intro j
    rcases eq_or_ne j i₀ with rfl | hj'
    · simp [hhk.2]
    · rw [update_of_ne hj']
      simp only [Finset.mem_insert, hj', false_or]
      exact hhk.1 j
  · intro h _
    simp
  · rintro ⟨h, k⟩ hhk
    simp only [Finset.mem_product, mem_boxH] at hhk
    have h0 : h i₀ = 0 := (hhk.1 i₀).2 hi₀
    simp only [update_idem, update_self, Prod.mk.injEq, and_true]
    rw [← h0, update_eq_self]
  · intro h _
    simp

/-- The sum over `boxH J p` of `∏_{j ∈ J} ρ ^ h j` is `(∑_{k < p} ρ ^ k) ^ card J`. -/
lemma sum_boxH_prod_pow (ρ : ℝ) (p : ℕ) (J : Finset ι) :
    ∑ h ∈ boxH J p, ∏ j ∈ J, ρ ^ h j = (∑ k ∈ Finset.range p, ρ ^ k) ^ J.card := by
  induction J using Finset.induction_on with
  | empty => simp [boxH_empty]
  | insert i₀ J hi₀ ih =>
    rw [sum_boxH_insert hi₀, Finset.card_insert_of_notMem hi₀, pow_succ, ← ih, Finset.sum_mul]
    refine Finset.sum_congr rfl fun h hh => ?_
    have h0 : h i₀ = 0 := ((mem_boxH.1 hh) i₀).2 hi₀
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.prod_insert hi₀, update_self, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [update_of_ne (by rintro rfl; exact hi₀ hj)]

omit [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] in
/-- A function depending on no coordinate is constant. -/
lemma eq_apply_zero_of_forall_indepOf [Finite ι] {g : (ι → ℂ) → V} (hg : ∀ j, IndepOf g j)
    (z : ι → ℂ) : g z = g 0 := by
  have := Fintype.ofFinite ι
  have key : ∀ s : Finset ι, g z = g fun j => if j ∈ s then 0 else z j := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [ih]
      have hupd : (fun j => if j ∈ insert a s then (0 : ℂ) else z j)
          = update (fun j => if j ∈ s then (0 : ℂ) else z j) a 0 := by
        funext j
        rcases eq_or_ne j a with rfl | hja
        · simp
        · simp [hja]
      rw [hupd, hg a]
  simpa [Pi.zero_def] using key Finset.univ

/-- **Newton division in all coordinates of `J`.**  See the section docstring.  The constant
`K = 1 + ∑_{k < p} (2 (R + r) / (R - r)) ^ k` bounds the growth of the error terms. -/
theorem exists_newton_finset {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (p : ℕ) (L : ι → ℕ → ℂ)
    (hL : ∀ j k, ‖L j k‖ ≤ r) {f : (ι → ℂ) → V}
    (hf : ∀ y : ι → ℂ, ‖y‖ ≤ R → AnalyticAt ℂ f y) {M : ℝ}
    (hM : ∀ y : ι → ℂ, ‖y‖ ≤ R → ‖f y‖ ≤ M) (J : Finset ι) :
    ∃ (A : (ι → ℕ) → (ι → ℂ) → V) (Q : ι → (ι → ℂ) → V),
      (∀ h (y : ι → ℂ), ‖y‖ ≤ R → AnalyticAt ℂ (A h) y) ∧
      (∀ i (y : ι → ℂ), ‖y‖ ≤ R → AnalyticAt ℂ (Q i) y) ∧
      (∀ h, ∀ j ∈ J, IndepOf (A h) j) ∧
      (∀ h ∈ boxH J p, ∀ y : ι → ℂ, ‖y‖ ≤ R →
        ‖A h y‖ ≤ (∏ j ∈ J, (2 / (R - r)) ^ h j) * M) ∧
      (∀ i ∈ J, ∀ y : ι → ℂ, ‖y‖ ≤ R →
        ‖Q i y‖ ≤ (1 + ∑ k ∈ Finset.range p, (2 / (R - r) * (R + r)) ^ k) ^ J.card *
          (2 / (R - r)) ^ p * M) ∧
      ∀ z : ι → ℂ, f z = ∑ h ∈ boxH J p, (∏ j ∈ J, nodeProd L j (h j) z) • A h z +
        ∑ i ∈ J, nodeProd L i p z • Q i z := by
  have hR : 0 < R := hr.trans_lt hrR
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simpa using hR.le))
  have hc : 0 ≤ 2 / (R - r) := div_nonneg (by norm_num) (by linarith)
  set K := 1 + ∑ k ∈ Finset.range p, (2 / (R - r) * (R + r)) ^ k with hK
  have hK1 : 1 ≤ K := by
    have : 0 ≤ ∑ k ∈ Finset.range p, (2 / (R - r) * (R + r)) ^ k :=
      Finset.sum_nonneg fun k _ => pow_nonneg (mul_nonneg hc (by linarith)) k
    linarith
  induction J using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => f, fun _ => 0, fun _ => hf, fun _ _ _ => analyticAt_const,
      fun _ j hj => absurd hj (Finset.notMem_empty j), fun h _ y hy => by simpa using hM y hy,
      fun i hi => absurd hi (Finset.notMem_empty i), fun z => by simp [boxH_empty]⟩
  | insert i₀ J hi₀ ih =>
    obtain ⟨A, Q, hA, hQ, hAind, hAbd, hQbd, hid⟩ := ih
    have hN := fun h => exists_newton (V := V) hr hrR i₀ p (L i₀) (hL i₀) (hA h)
    choose a q ha hq hai haj hdec hbd using hN
    set A' : (ι → ℕ) → (ι → ℂ) → V := fun h' => a (update h' i₀ 0) (h' i₀) with hA'
    set Q₀ : (ι → ℂ) → V :=
      fun z => ∑ h ∈ boxH J p, (∏ j ∈ J, nodeProd L j (h j) z) • q h z with hQ₀
    set Q' : ι → (ι → ℂ) → V := fun i => if i = i₀ then Q₀ else Q i with hQ'
    refine ⟨A', Q', fun h' y hy => ha _ _ y hy, fun i y hy => ?_, fun h' j hj => ?_,
      fun h' hh' y hy => ?_, fun i hi y hy => ?_, fun z => ?_⟩
    · -- analyticity of the new error term
      by_cases hi : i = i₀
      · simp only [hQ', hi, ↓reduceIte, hQ₀]
        exact Finset.analyticAt_fun_sum _ fun h _ =>
          (Finset.analyticAt_fun_prod _ fun j _ => analyticAt_nodeProd L j _ y).smul
            (hq h y hy)
      · simp only [hQ', hi, ↓reduceIte]
        exact hQ i y hy
    · -- the new coefficients depend on no coordinate of `insert i₀ J`
      rcases Finset.mem_insert.1 hj with rfl | hjJ
      · exact hai _ _
      · exact (haj _ j (by rintro rfl; exact hi₀ hjJ) (hAind _ j hjJ)).1 _
    · -- bound on the new coefficients
      rw [mem_boxH] at hh'
      set h := update h' i₀ 0 with hh
      have hhmem : h ∈ boxH J p := by
        rw [mem_boxH]
        intro j
        refine ⟨fun hj => ?_, fun hj => ?_⟩
        · rw [hh, update_of_ne (by rintro rfl; exact hi₀ hj)]
          exact (hh' j).1 (Finset.mem_insert_of_mem hj)
        · rcases eq_or_ne j i₀ with rfl | hj'
          · simp [hh]
          · rw [hh, update_of_ne hj']
            exact (hh' j).2 (by simp [hj, hj'])
      have hk : h' i₀ < p := (hh' i₀).1 (Finset.mem_insert_self _ _)
      have := ((hbd h _ (hAbd h hhmem)).1 (h' i₀) hk y hy)
      refine this.trans (le_of_eq ?_)
      rw [Finset.prod_insert hi₀, mul_assoc]
      congr 2
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [hh, update_of_ne (by rintro rfl; exact hi₀ hj)]
    · -- bound on the error terms
      rw [Finset.card_insert_of_notMem hi₀]
      by_cases hii : i = i₀
      · simp only [hQ', hii, ↓reduceIte, hQ₀]
        have hterm : ∀ h ∈ boxH J p, ‖(∏ j ∈ J, nodeProd L j (h j) y) • q h y‖ ≤
            (2 / (R - r)) ^ p * M * ∏ j ∈ J, (2 / (R - r) * (R + r)) ^ h j := by
          intro h hh
          rw [norm_smul, norm_prod]
          have hqh := (hbd h _ (hAbd h hh)).2 y hy
          calc (∏ j ∈ J, ‖nodeProd L j (h j) y‖) * ‖q h y‖
              ≤ (∏ j ∈ J, (R + r) ^ h j) *
                  ((2 / (R - r)) ^ p * ((∏ j ∈ J, (2 / (R - r)) ^ h j) * M)) := by
                gcongr with j hj
                exact norm_nodeProd_le hL j (h j) hy
            _ = (2 / (R - r)) ^ p * M * ∏ j ∈ J, (2 / (R - r) * (R + r)) ^ h j := by
                rw [show ∏ j ∈ J, (2 / (R - r) * (R + r)) ^ h j
                    = (∏ j ∈ J, (2 / (R - r)) ^ h j) * ∏ j ∈ J, (R + r) ^ h j by
                  rw [← Finset.prod_mul_distrib]; simp_rw [mul_pow]]
                ring
        calc ‖∑ h ∈ boxH J p, (∏ j ∈ J, nodeProd L j (h j) y) • q h y‖
            ≤ ∑ h ∈ boxH J p, (2 / (R - r)) ^ p * M * ∏ j ∈ J, (2 / (R - r) * (R + r)) ^ h j :=
              (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
          _ = (2 / (R - r)) ^ p * M * (K - 1) ^ J.card := by
              rw [← Finset.mul_sum, sum_boxH_prod_pow, hK, add_sub_cancel_left]
          _ ≤ K ^ (J.card + 1) * (2 / (R - r)) ^ p * M := by
              have hKK : (K - 1) ^ J.card ≤ K ^ (J.card + 1) :=
                (pow_le_pow_left₀ (by linarith) (by linarith) _).trans
                  (pow_le_pow_right₀ hK1 (Nat.le_succ _))
              have : 0 ≤ (2 / (R - r)) ^ p * M := mul_nonneg (pow_nonneg hc p) hM0
              nlinarith
      · simp only [hQ', hii, ↓reduceIte]
        have hiJ : i ∈ J := by simpa [hii] using hi
        refine (hQbd i hiJ y hy).trans ?_
        have : 0 ≤ (2 / (R - r)) ^ p * M := mul_nonneg (pow_nonneg hc p) hM0
        have hKK : K ^ J.card ≤ K ^ (J.card + 1) := pow_le_pow_right₀ hK1 (Nat.le_succ _)
        nlinarith
    · -- the identity
      rw [hid z, sum_boxH_insert hi₀, Finset.sum_insert hi₀]
      have hmain : ∀ h ∈ boxH J p, (∏ j ∈ J, nodeProd L j (h j) z) • A h z =
          ∑ k ∈ Finset.range p,
            (∏ j ∈ insert i₀ J, nodeProd L j (update h i₀ k j) z) • A' (update h i₀ k) z +
          nodeProd L i₀ p z • (∏ j ∈ J, nodeProd L j (h j) z) • q h z := by
        intro h hh
        have h0 : h i₀ = 0 := ((mem_boxH.1 hh) i₀).2 hi₀
        rw [hdec h z, smul_add, Finset.smul_sum]
        congr 1
        · refine Finset.sum_congr rfl fun k _ => ?_
          have hA'k : A' (update h i₀ k) = a h k := by
            simp only [hA', update_idem, update_self]
            rw [← h0, update_eq_self]
          rw [hA'k, Finset.prod_insert hi₀, update_self, smul_smul,
            show ∏ x ∈ J, nodeProd L x (update h i₀ k x) z = ∏ j ∈ J, nodeProd L j (h j) z from
              Finset.prod_congr rfl fun j hj => by
                rw [update_of_ne (by rintro rfl; exact hi₀ hj)], mul_comm]
          rfl
        · rw [smul_comm]
          rfl
      rw [Finset.sum_congr rfl hmain, Finset.sum_add_distrib, ← Finset.smul_sum]
      have hQJ : ∑ i ∈ J, nodeProd L i p z • Q' i z = ∑ i ∈ J, nodeProd L i p z • Q i z :=
        Finset.sum_congr rfl fun i hi => by
          simp only [hQ', show i ≠ i₀ by rintro rfl; exact hi₀ hi, ↓reduceIte]
      rw [hQJ]
      simp only [hQ', ↓reduceIte, hQ₀]
      abel

end MultiIndex

/-!
### Uniqueness of the main term

After all coordinates are processed, the main term is a polynomial with constant
coefficients in the tensor Newton basis.  If `f` vanishes to order `m` in each coordinate on
`E₁ × ⋯ × Eₙ` and the nodes in the `j`-th coordinate are the points of `E j`, each repeated
`m` times, these coefficients vanish.  In one variable this is root counting: a polynomial of
degree `< m * card E` with a root of multiplicity `≥ m` at each point of `E` is zero.  The
several-variable statement is the injectivity of a tensor product of injective maps.
-/

namespace MultiIndex

open Polynomial

/-- The Newton basis polynomial `∏_{l < k} (X - L l)`. -/
noncomputable def nodePoly (L : ℕ → ℂ) (k : ℕ) : ℂ[X] := ∏ l ∈ Finset.range k, (X - C (L l))

lemma nodePoly_monic (L : ℕ → ℂ) (k : ℕ) : (nodePoly L k).Monic :=
  monic_prod_of_monic _ _ fun l _ => monic_X_sub_C (L l)

lemma natDegree_nodePoly (L : ℕ → ℂ) (k : ℕ) : (nodePoly L k).natDegree = k := by
  rw [nodePoly, natDegree_prod_of_monic _ _ fun l _ => monic_X_sub_C (L l)]
  simp

lemma eval_nodePoly (L : ℕ → ℂ) (k : ℕ) (w : ℂ) :
    (nodePoly L k).eval w = ∏ l ∈ Finset.range k, (w - L l) := by
  simp [nodePoly, eval_prod]

/-- The Newton basis is triangular: a vanishing combination has zero coefficients. -/
lemma eq_zero_of_sum_C_mul_nodePoly (L : ℕ → ℂ) : ∀ (p : ℕ) (a : ℕ → ℂ),
    ∑ k ∈ Finset.range p, C (a k) * nodePoly L k = 0 → ∀ k < p, a k = 0 := by
  intro p
  induction p with
  | zero => intro a _ k hk; omega
  | succ p ih =>
    intro a h k hk
    have h1 : (nodePoly L p).coeff p = 1 := by
      have := (nodePoly_monic L p).coeff_natDegree
      rwa [natDegree_nodePoly] at this
    have hlow : ∀ k ∈ Finset.range p, a k * (nodePoly L k).coeff p = 0 := fun k hk => by
      rw [coeff_eq_zero_of_natDegree_lt (by rw [natDegree_nodePoly]; exact Finset.mem_range.1 hk),
        mul_zero]
    have htop : a p = 0 := by
      have hc := congrArg (fun P => P.coeff p) h
      simp only [Finset.sum_range_succ, coeff_add, coeff_C_mul, finsetSum_coeff,
        coeff_zero] at hc
      rwa [Finset.sum_eq_zero hlow, zero_add, h1, mul_one] at hc
    have hrest : ∑ k ∈ Finset.range p, C (a k) * nodePoly L k = 0 := by
      rwa [Finset.sum_range_succ, htop, C_0, zero_mul, add_zero] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact ih a hrest k hk
    · exact htop

/-- **Newton coefficients from Taylor data.**  Let the nodes `L 0, …, L (p - 1)` be the points
of `E`, each repeated `m` times.  If a combination `∑_{k < p} d k • ∏_{l < k} (X - L l)` has all
Taylor coefficients of order `< m` zero at every point of `E`, then every `d k` is zero. -/
theorem newton_eq_zero_of_taylor {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    {L : ℕ → ℂ} {E : Finset ℂ} {m p : ℕ} (hLE : nodePoly L p = ∏ ζ ∈ E, (X - C ζ) ^ m)
    (d : ℕ → W)
    (hd : ∀ ζ ∈ E, ∀ t < m,
      ∑ k ∈ Finset.range p, (taylor ζ (nodePoly L k)).coeff t • d k = 0) :
    ∀ k < p, d k = 0 := by
  intro k hk
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ) fun φ => ?_
  set a : ℕ → ℂ := fun k => φ (d k) with ha
  set Q : ℂ[X] := ∑ k ∈ Finset.range p, C (a k) * nodePoly L k with hQ
  have htay : ∀ ζ ∈ E, ∀ t < m, (taylor ζ Q).coeff t = 0 := by
    intro ζ hζ t ht
    have hφ := congrArg φ (hd ζ hζ t ht)
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hφ
    rw [hQ]
    simp_rw [← smul_eq_C_mul]
    rw [map_sum, finsetSum_coeff]
    simp_rw [LinearMap.map_smul, coeff_smul, smul_eq_mul]
    rw [← hφ]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hdvd : ∀ ζ ∈ E, (X - C ζ) ^ m ∣ Q := by
    intro ζ hζ
    by_cases hQ0 : Q = 0
    · rw [hQ0]; exact dvd_zero _
    · rw [← le_rootMultiplicity_iff hQ0, rootMultiplicity_eq_natTrailingDegree, ← taylor_apply]
      exact le_natTrailingDegree (by rwa [Ne, taylor_eq_zero]) (htay ζ hζ)
  have hcop : (E : Set ℂ).Pairwise (IsCoprime on fun ζ => (X - C ζ) ^ m) := by
    intro a _ b _ hab
    exact ((pairwise_coprime_X_sub_C (s := id) injective_id) hab).pow
  have hprod : nodePoly L p ∣ Q := by
    rw [hLE]
    exact Finset.prod_dvd_of_coprime hcop hdvd
  have hdeg : Q.natDegree < (nodePoly L p).natDegree := by
    rw [natDegree_nodePoly]
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := p - 1) fun k hk => ?_)
      (by omega)
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_nodePoly]
    have := Finset.mem_range.1 hk
    omega
  exact eq_zero_of_sum_C_mul_nodePoly L p a (eq_zero_of_dvd_of_natDegree_lt hprod hdeg) k hk

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma update_zero_mem_boxH {J : Finset ι} {i₀ : ι} (hi₀ : i₀ ∉ J) {p : ℕ} {h : ι → ℕ}
    (hh : h ∈ boxH (insert i₀ J) p) : update h i₀ 0 ∈ boxH J p := by
  rw [mem_boxH] at hh ⊢
  intro j
  refine ⟨fun hj => ?_, fun hj => ?_⟩
  · rw [update_of_ne (by rintro rfl; exact hi₀ hj)]
    exact (hh j).1 (Finset.mem_insert_of_mem hj)
  · rcases eq_or_ne j i₀ with rfl | hj'
    · simp
    · rw [update_of_ne hj']
      exact (hh j).2 (by simp [hj, hj'])

/-- **A tensor product of injective maps is injective.**  If, in each coordinate, a vector
`d : ℕ → W` supported below `p` is determined by the values `∑_k Mx j k γ • d k`, then a family
indexed by `boxH J p` is determined by the tensor products of these values. -/
theorem eq_zero_of_tensor {W : Type*} [AddCommGroup W] [Module ℂ W] {p : ℕ}
    {Cond : ι → Type*} [∀ j, Nonempty (Cond j)] (Mx : ∀ j, ℕ → Cond j → ℂ)
    (hinj : ∀ j (d : ℕ → W),
      (∀ γ : Cond j, ∑ k ∈ Finset.range p, Mx j k γ • d k = 0) → ∀ k < p, d k = 0)
    (J : Finset ι) : ∀ C : (ι → ℕ) → W,
      (∀ γ : ∀ j, Cond j, ∑ h ∈ boxH J p, (∏ j ∈ J, Mx j (h j) (γ j)) • C h = 0) →
      ∀ h ∈ boxH J p, C h = 0 := by
  induction J using Finset.induction_on with
  | empty =>
    intro C hC h hh
    rw [boxH_empty, Finset.mem_singleton] at hh
    subst hh
    simpa [boxH_empty] using hC fun _ => Classical.arbitrary _
  | insert i₀ J hi₀ ih =>
    intro C hC h' hh'
    have hk : ∀ k < p, ∀ γ : ∀ j, Cond j,
        ∑ h ∈ boxH J p, (∏ j ∈ J, Mx j (h j) (γ j)) • C (update h i₀ k) = 0 := by
      intro k hkp γ
      refine hinj i₀ (fun k =>
        ∑ h ∈ boxH J p, (∏ j ∈ J, Mx j (h j) (γ j)) • C (update h i₀ k)) (fun γ₀ => ?_) k hkp
      calc ∑ k ∈ Finset.range p, Mx i₀ k γ₀ •
            ∑ h ∈ boxH J p, (∏ j ∈ J, Mx j (h j) (γ j)) • C (update h i₀ k)
          = ∑ h ∈ boxH J p, ∑ k ∈ Finset.range p,
              (∏ j ∈ insert i₀ J, Mx j (update h i₀ k j) (update γ i₀ γ₀ j)) •
                C (update h i₀ k) := by
            simp_rw [Finset.smul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun k _ => ?_
            rw [smul_smul, Finset.prod_insert hi₀, update_self, update_self]
            congr 2
            refine Finset.prod_congr rfl fun j hj => ?_
            have hj' : j ≠ i₀ := by rintro rfl; exact hi₀ hj
            rw [update_of_ne hj', update_of_ne hj']
        _ = 0 := (sum_boxH_insert hi₀ p fun h =>
              (∏ j ∈ insert i₀ J, Mx j (h j) (update γ i₀ γ₀ j)) • C h).symm.trans (hC _)
    have hmem := update_zero_mem_boxH hi₀ hh'
    have hlt : h' i₀ < p := ((mem_boxH.1 hh') i₀).1 (Finset.mem_insert_self _ _)
    have := ih (fun h => C (update h i₀ (h' i₀))) (hk _ hlt) _ hmem
    simpa [update_idem] using this

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

/-- **The Taylor coefficients of the main term.**  At `ξ`, the coefficient of `(z - ξ) ^ κ` of
`∑_h (∏_j nodeProd L j (h j) z) • C₀ h` is the tensor combination of the one-variable Taylor
coefficients of the Newton basis polynomials. -/
theorem taylorCoeff_mainTerm (L : ι → ℕ → ℂ) (p : ℕ) (C₀ : (ι → ℕ) → V) (ξ : ι → ℂ)
    (κ : ι → ℕ) :
    taylorCoeff (fun z => ∑ h ∈ boxH Finset.univ p, (∏ j, nodeProd L j (h j) z) • C₀ h) ξ κ =
      ∑ h ∈ boxH Finset.univ p,
        (∏ j, (taylor (ξ j) (nodePoly (L j) (h j))).coeff (κ j)) • C₀ h := by
  set c : (ι → ℕ) → V := fun κ => ∑ h ∈ boxH Finset.univ p,
    (∏ j, (taylor (ξ j) (nodePoly (L j) (h j))).coeff (κ j)) • C₀ h with hc
  set box : Finset (ι → ℕ) := Fintype.piFinset fun _ : ι => Finset.range (p + 1) with hbox
  have hc0 : ∀ κ ∉ box, c κ = 0 := by
    intro κ hκ
    obtain ⟨j, hj⟩ : ∃ j, p + 1 ≤ κ j := by
      by_contra hcon
      push Not at hcon
      exact hκ (by simpa [hbox, Fintype.mem_piFinset] using hcon)
    refine Finset.sum_eq_zero fun h hh => ?_
    have hhj : h j < p := ((mem_boxH.1 hh) j).1 (Finset.mem_univ j)
    rw [Finset.prod_eq_zero (Finset.mem_univ j), zero_smul]
    exact coeff_eq_zero_of_natDegree_lt (by rw [natDegree_taylor, natDegree_nodePoly]; omega)
  have hsum : Summable fun α : ι → ℕ => ‖c α‖ * ((1 : ℝ≥0) : ℝ) ^ (∑ i, α i) :=
    summable_of_ne_finset_zero (s := box) fun α hα => by simp [hc0 α hα]
  refine taylorCoeff_eq_of_hasSum (ρ := 1) one_pos hsum (fun y _ => ?_) κ
  have hfin : ∀ α ∉ box, (∏ i, y i ^ α i) • c α = 0 := fun α hα => by rw [hc0 α hα, smul_zero]
  have hN : ∀ h ∈ boxH Finset.univ p, ∀ j, nodeProd L j (h j) (ξ + y) =
      ∑ t ∈ Finset.range (p + 1), (taylor (ξ j) (nodePoly (L j) (h j))).coeff t * y j ^ t := by
    intro h hh j
    have hlt : (taylor (ξ j) (nodePoly (L j) (h j))).natDegree < p + 1 := by
      rw [natDegree_taylor, natDegree_nodePoly]
      have := ((mem_boxH.1 hh) j).1 (Finset.mem_univ j)
      omega
    rw [← eval_eq_sum_range' hlt, taylor_eval, nodeProd, eval_nodePoly]
    simp [add_comm]
  have heq : (∑ h ∈ boxH Finset.univ p, (∏ j, nodeProd L j (h j) (ξ + y)) • C₀ h) =
      ∑ α ∈ box, (∏ i, y i ^ α i) • c α := by
    calc ∑ h ∈ boxH Finset.univ p, (∏ j, nodeProd L j (h j) (ξ + y)) • C₀ h
        = ∑ h ∈ boxH Finset.univ p, (∑ α ∈ box,
            ∏ j, ((taylor (ξ j) (nodePoly (L j) (h j))).coeff (α j) * y j ^ α j)) • C₀ h := by
          refine Finset.sum_congr rfl fun h hh => ?_
          rw [Finset.prod_congr rfl fun j _ => hN h hh j, Finset.prod_univ_sum]
      _ = ∑ α ∈ box, (∏ i, y i ^ α i) • c α := by
          simp_rw [Finset.sum_smul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [hc, Finset.smul_sum]
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [Finset.prod_mul_distrib, smul_smul, mul_comm]
  rw [heq]
  exact hasSum_sum_of_ne_finset_zero hfin

/-- A factor `(z i - ξ i) ^ m` kills the Taylor coefficients at `ξ` of order `< m` in the
`i`-th coordinate. -/
theorem taylorCoeff_pow_smul_eq_zero {G : (ι → ℂ) → V} {ξ : ι → ℂ} (hG : AnalyticAt ℂ G ξ)
    (i : ι) (m : ℕ) {κ : ι → ℕ} (hκ : κ i < m) :
    taylorCoeff (fun z => (z i - ξ i) ^ m • G z) ξ κ = 0 := by
  obtain ⟨ρ, hρ, hsum, hhs⟩ := exists_hasSum_of_analyticAt hG
  set d := taylorCoeff G ξ with hd
  set c : (ι → ℕ) → V := fun α => if m ≤ α i then d (α - Pi.single i m) else 0 with hc
  have hc_shift : ∀ β : ι → ℕ, c (β + Pi.single i m) = d β := by
    intro β
    simp only [hc, Pi.add_apply, Pi.single_eq_same, le_add_iff_nonneg_left, zero_le,
      ↓reduceIte]
    congr 1
    funext j
    simp
  have hc_van : ∀ α : ι → ℕ, α i < m → c α = 0 := fun α hα => by
    simp [hc, not_le.2 hα]
  have hsum_c : Summable fun α : ι → ℕ => ‖c α‖ * (ρ : ℝ) ^ (∑ i, α i) := by
    have hinj : Function.Injective fun β : ι → ℕ => β + Pi.single i m := add_left_injective _
    have hzero : ∀ α ∉ Set.range fun β : ι → ℕ => β + Pi.single i m,
        ‖c α‖ * (ρ : ℝ) ^ (∑ i, α i) = 0 := by
      intro α hα
      have hlt : ¬ m ≤ α i := fun hle => hα ⟨α - Pi.single i m, by
        funext j
        rcases eq_or_ne j i with rfl | hj
        · simp [Nat.sub_add_cancel hle]
        · simp [Pi.single_eq_of_ne hj]⟩
      simp [hc, hlt]
    rw [← hinj.summable_iff hzero]
    refine (hsum.mul_left ((ρ : ℝ) ^ m)).congr fun β => ?_
    simp only [Function.comp_apply, hc_shift, Pi.add_apply, Finset.sum_add_distrib,
      Finset.sum_pi_single', Finset.mem_univ, ↓reduceIte, pow_add]
    ring
  have hhs_c : ∀ y : ι → ℂ, ‖y‖ < ρ → HasSum (fun α : ι → ℕ => (∏ j, y j ^ α j) • c α)
      ((fun z => (z i - ξ i) ^ m • G z) (ξ + y)) := by
    intro y hy
    have h1 : HasSum (fun β : ι → ℕ => (∏ j, y j ^ β j) • c (β + Pi.single i m))
        (G (ξ + y)) := by simpa [hc_shift] using hhs y hy
    simpa using hasSum_smul_shift_pow i m hc_van h1
  rw [taylorCoeff_eq_of_hasSum hρ hsum_c hhs_c κ]
  exact hc_van κ hκ

end MultiIndex

/-!
### Schwarz's lemma for Cartesian products
-/

namespace MultiIndex

open Polynomial

/-- Nodes listing the points of `E`, each `m` times, in the disc of radius `r`. -/
theorem exists_nodes (E : Finset ℂ) (m : ℕ) {r : ℝ} (hr : 0 ≤ r) (hE : ∀ ζ ∈ E, ‖ζ‖ ≤ r) :
    ∃ L : ℕ → ℂ, (∀ k, ‖L k‖ ≤ r) ∧ nodePoly L (m * E.card) = ∏ ζ ∈ E, (X - C ζ) ^ m := by
  classical
  induction E using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, fun _ => by simpa using hr, by simp [nodePoly]⟩
  | insert a E ha ih =>
    obtain ⟨L', hL'r, hL'E⟩ := ih fun ζ hζ => hE ζ (Finset.mem_insert_of_mem hζ)
    refine ⟨fun k => if k < m then a else L' (k - m), fun k => ?_, ?_⟩
    · by_cases hk : k < m
      · simp only [hk, ↓reduceIte]
        exact hE a (Finset.mem_insert_self a E)
      · simp only [hk, ↓reduceIte]
        exact hL'r _
    · rw [Finset.card_insert_of_notMem ha, Finset.prod_insert ha, ← hL'E, mul_add, mul_one,
        add_comm, nodePoly, Finset.prod_range_add]
      congr 1
      · rw [Finset.prod_congr rfl fun x hx =>
          show X - C (if x < m then a else L' (x - m)) = X - C a by
            simp [Finset.mem_range.1 hx], Finset.prod_const, Finset.card_range]
      · refine Finset.prod_congr rfl fun k _ => ?_
        simp

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

/-- **Schwarz's lemma for Cartesian products** (Proposition 4.7 of [waldschmidt2000]).

Let `f` be analytic on the closed polydisc of polyradius `R` in `ℂⁿ`, with `‖f‖ ≤ M` there, and
let `E₁, …, Eₙ` be sets of `S` points in the disc of radius `r < R`.  If every Taylor
coefficient of `f` of order `< m` in each coordinate vanishes at every point of
`E₁ × ⋯ × Eₙ`, then on the polydisc of polyradius `r`
`‖f‖ ≤ n (4r / (R - r)) ^ (mS) K ^ n M`, where `K = 1 + ∑_{k < mS} (2 (R + r) / (R - r)) ^ k`.
For `R ≥ 5r` this is at most `n (5 · 3ⁿ r / R) ^ (mS) M`: see
`norm_le_of_taylorCoeff_eq_zero_of_five_mul_le`. -/
theorem norm_le_of_taylorCoeff_eq_zero [Nonempty ι] {f : (ι → ℂ) → V} {E : ι → Finset ℂ}
    {S m : ℕ} (hE : ∀ i, (E i).card = S) {r R M : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hEr : ∀ i, ∀ ζ ∈ E i, ‖ζ‖ ≤ r)
    (hf : ∀ y : ι → ℂ, ‖y‖ ≤ R → AnalyticAt ℂ f y)
    (hM : ∀ y : ι → ℂ, ‖y‖ ≤ R → ‖f y‖ ≤ M)
    (hvan : ∀ ξ : ι → ℂ, (∀ i, ξ i ∈ E i) → ∀ κ : ι → ℕ, (∀ i, κ i < m) →
      taylorCoeff f ξ κ = 0)
    {z : ι → ℂ} (hz : ‖z‖ ≤ r) :
    ‖f z‖ ≤ Fintype.card ι * (2 * r * (2 / (R - r))) ^ (m * S) *
      (1 + ∑ k ∈ Finset.range (m * S), (2 / (R - r) * (R + r)) ^ k) ^ Fintype.card ι * M := by
  set p := m * S with hp
  have hR : 0 < R := hr.trans_lt hrR
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simpa using hR.le))
  have hc : 0 ≤ 2 / (R - r) := div_nonneg (by norm_num) (by linarith)
  choose L hLr hLE using fun i => exists_nodes (E i) m hr (hEr i)
  simp only [hE] at hLE
  obtain ⟨A, Q, hA, hQ, hAind, -, hQbd, hid⟩ :=
    exists_newton_finset hr hrR p L (fun j k => hLr j k) hf hM Finset.univ
  set C₀ : (ι → ℕ) → V := fun h => A h 0 with hC₀
  have hAC : ∀ h z, A h z = C₀ h := fun h z =>
    eq_apply_zero_of_forall_indepOf (fun j => hAind h j (Finset.mem_univ j)) z
  set T : (ι → ℂ) → V :=
    fun z => ∑ h ∈ boxH Finset.univ p, (∏ j, nodeProd L j (h j) z) • C₀ h with hT
  set Er : (ι → ℂ) → V := fun z => ∑ i, nodeProd L i p z • Q i z with hEr'
  have hfTE : ∀ z, f z = T z + Er z := fun z => by
    rw [hid z]
    simp [hT, hEr', hAC]
  -- the main term vanishes
  have hC0 : ∀ h ∈ boxH Finset.univ p, C₀ h = 0 := by
    rcases Nat.eq_zero_or_pos p with hp0 | hp0
    · intro h hh
      obtain ⟨j⟩ := ‹Nonempty ι›
      have := ((mem_boxH.1 hh) j).1 (Finset.mem_univ j)
      omega
    · have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => by simp [hp, h] at hp0
      have hS0 : 0 < S := Nat.pos_of_ne_zero fun h => by simp [hp, h] at hp0
      have hne : ∀ j, Nonempty {x : ℂ × ℕ // x.1 ∈ E j ∧ x.2 < m} := fun j => by
        obtain ⟨ζ, hζ⟩ := Finset.card_pos.1 (by rw [hE j]; exact hS0)
        exact ⟨⟨(ζ, 0), hζ, hm0⟩⟩
      refine eq_zero_of_tensor (Cond := fun j => {x : ℂ × ℕ // x.1 ∈ E j ∧ x.2 < m})
        (fun j k γ => (taylor γ.1.1 (nodePoly (L j) k)).coeff γ.1.2)
        (fun j d hd => newton_eq_zero_of_taylor (hLE j) d fun ζ hζ t ht => hd ⟨(ζ, t), hζ, ht⟩)
        Finset.univ C₀ (fun γ => ?_)
      set ξ : ι → ℂ := fun j => (γ j).1.1 with hξdef
      set κ : ι → ℕ := fun j => (γ j).1.2 with hκdef
      have hξ : ∀ i, ξ i ∈ E i := fun i => (γ i).2.1
      have hκ : ∀ i, κ i < m := fun i => (γ i).2.2
      have hξR : ‖ξ‖ ≤ R :=
        (pi_norm_le_iff_of_nonneg hR.le).2 fun i => (hEr i _ (hξ i)).trans hrR.le
      have hEran : ∀ i ∈ (Finset.univ : Finset ι),
          AnalyticAt ℂ (fun z => nodeProd L i p z • Q i z) ξ :=
        fun i _ => (analyticAt_nodeProd L i p ξ).smul (hQ i ξ hξR)
      have hEr0 : taylorCoeff Er ξ κ = 0 := by
        rw [hEr', taylorCoeff_finset_sum _ hEran]
        refine Finset.sum_eq_zero fun i _ => ?_
        have hfac : (fun z => nodeProd L i p z • Q i z) = fun z =>
            (z i - ξ i) ^ m • ((∏ ζ ∈ (E i).erase (ξ i), (z i - ζ) ^ m) • Q i z) := by
          funext z
          have hprod : nodeProd L i p z = ∏ ζ ∈ E i, (z i - ζ) ^ m := by
            rw [nodeProd, ← eval_nodePoly, hLE i]
            simp [eval_prod]
          rw [hprod, ← Finset.mul_prod_erase _ _ (hξ i), mul_smul]
        rw [hfac]
        have hcoord : AnalyticAt ℂ (fun z : ι → ℂ => z i) ξ :=
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i).analyticAt ξ
        exact taylorCoeff_pow_smul_eq_zero ((Finset.analyticAt_fun_prod _ fun ζ _ =>
          (hcoord.sub analyticAt_const).pow m).smul (hQ i ξ hξR)) i m (hκ i)
      have hTeq : T = f - Er := by
        funext z
        simp [hfTE z]
      have hT0 : taylorCoeff T ξ κ = 0 := by
        rw [hTeq, taylorCoeff_sub (hf ξ hξR) (Finset.analyticAt_fun_sum _ hEran),
          hvan ξ hξ κ hκ, hEr0, sub_zero]
      exact (taylorCoeff_mainTerm L p C₀ ξ κ).symm.trans hT0
  -- only the error terms remain
  have hTz : T z = 0 := Finset.sum_eq_zero fun h hh => by rw [hC0 h hh, smul_zero]
  rw [hfTE z, hTz, zero_add]
  have hzR : ‖z‖ ≤ R := hz.trans hrR.le
  set K := 1 + ∑ k ∈ Finset.range p, (2 / (R - r) * (R + r)) ^ k with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ ∑ k ∈ Finset.range p, (2 / (R - r) * (R + r)) ^ k :=
      Finset.sum_nonneg fun k _ => pow_nonneg (mul_nonneg hc (by linarith)) k
    linarith
  have hbd : ∀ i, ‖nodeProd L i p z • Q i z‖ ≤
      (r + r) ^ p * (K ^ Fintype.card ι * (2 / (R - r)) ^ p * M) := fun i => by
    rw [norm_smul]
    have hQi := hQbd i (Finset.mem_univ i) z hzR
    rw [Finset.card_univ] at hQi
    exact mul_le_mul (norm_nodeProd_le hLr i p hz) hQi (norm_nonneg _) (by positivity)
  calc ‖Er z‖ ≤ ∑ _i : ι, (r + r) ^ p * (K ^ Fintype.card ι * (2 / (R - r)) ^ p * M) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hbd i)
    _ = Fintype.card ι * (2 * r * (2 / (R - r))) ^ p * K ^ Fintype.card ι * M := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          show 2 * r * (2 / (R - r)) = (r + r) * (2 / (R - r)) by ring, mul_pow]
        ring

/-- **Schwarz's lemma for Cartesian products, for `R ≥ 5r`**: on the polydisc of polyradius
`r`, `‖f‖ ≤ n (5 · 3ⁿ r / R) ^ (mS) M`. -/
theorem norm_le_of_taylorCoeff_eq_zero_of_five_mul_le [Nonempty ι] {f : (ι → ℂ) → V}
    {E : ι → Finset ℂ} {S m : ℕ} (hE : ∀ i, (E i).card = S) {r R M : ℝ} (hr : 0 ≤ r)
    (hR : 0 < R) (h5 : 5 * r ≤ R) (hEr : ∀ i, ∀ ζ ∈ E i, ‖ζ‖ ≤ r)
    (hf : ∀ y : ι → ℂ, ‖y‖ ≤ R → AnalyticAt ℂ f y)
    (hM : ∀ y : ι → ℂ, ‖y‖ ≤ R → ‖f y‖ ≤ M)
    (hvan : ∀ ξ : ι → ℂ, (∀ i, ξ i ∈ E i) → ∀ κ : ι → ℕ, (∀ i, κ i < m) →
      taylorCoeff f ξ κ = 0)
    {z : ι → ℂ} (hz : ‖z‖ ≤ r) :
    ‖f z‖ ≤ Fintype.card ι * (5 * 3 ^ Fintype.card ι * r / R) ^ (m * S) * M := by
  have hrR : r < R := by linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simpa using hR.le))
  have hRr : 0 < R - r := by linarith
  have hmain := norm_le_of_taylorCoeff_eq_zero hE hr hrR hEr hf hM hvan hz
  refine hmain.trans ?_
  set p := m * S
  set n := Fintype.card ι
  have hc0 : 0 ≤ 2 / (R - r) := by positivity
  have h1 : 2 * r * (2 / (R - r)) ≤ 5 * r / R := by
    rw [show 2 * r * (2 / (R - r)) = 4 * r / (R - r) by ring, div_le_div_iff₀ hRr hR]
    nlinarith
  have hρ : 2 / (R - r) * (R + r) ≤ 3 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hRr]
    linarith
  have hρ0 : 0 ≤ 2 / (R - r) * (R + r) := mul_nonneg hc0 (by linarith)
  have hK : 1 + ∑ k ∈ Finset.range p, (2 / (R - r) * (R + r)) ^ k ≤ 3 ^ p := by
    have hsum : ∑ k ∈ Finset.range p, (2 / (R - r) * (R + r)) ^ k ≤
        ∑ k ∈ Finset.range p, (3 : ℝ) ^ k :=
      Finset.sum_le_sum fun k _ => pow_le_pow_left₀ hρ0 hρ k
    have hgeom : ∑ k ∈ Finset.range p, (3 : ℝ) ^ k = (3 ^ p - 1) / 2 := by
      rw [geom_sum_eq (by norm_num)]
      norm_num
    have h3 : (1 : ℝ) ≤ 3 ^ p := one_le_pow₀ (by norm_num)
    linarith
  have hK0 : 0 ≤ 1 + ∑ k ∈ Finset.range p, (2 / (R - r) * (R + r)) ^ k := by
    have : 0 ≤ ∑ k ∈ Finset.range p, (2 / (R - r) * (R + r)) ^ k :=
      Finset.sum_nonneg fun k _ => pow_nonneg hρ0 k
    linarith
  calc (n : ℝ) * (2 * r * (2 / (R - r))) ^ p *
        (1 + ∑ k ∈ Finset.range p, (2 / (R - r) * (R + r)) ^ k) ^ n * M
      ≤ n * (5 * r / R) ^ p * (3 ^ p) ^ n * M := by
        gcongr
    _ = n * (5 * 3 ^ n * r / R) ^ p * M := by
        rw [show 5 * 3 ^ n * r / R = 3 ^ n * (5 * r / R) by ring, mul_pow, ← pow_mul, ← pow_mul,
          mul_comm n p]
        ring

end MultiIndex
