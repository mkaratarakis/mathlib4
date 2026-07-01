/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.Hilbert17FTA

/-!
# The intermediate value property for polynomials over a real closed field

Over a real closed field `R`, a polynomial that is `≥ 0` at `x` and `≤ 0` at `y ≥ x` has a root in
`[x, y]` (`Hilbert17Blueprint.intermediate_value_property`). This is the algebraic substitute for
the
analytic IVT (there is no completeness on an abstract real closed field) and is the foundation of
the
Sturm–Tarski theory used for quantifier elimination.

The proof rests on the classification of monic irreducibles over a real closed field
(`irred_poly_classify`): every monic irreducible is linear or a positive-definite quadratic
`(X - a)² + b²`, obtained here from the fundamental theorem of algebra for `R` (`R[i]` is
algebraically closed, `Hilbert17Blueprint.isAlgClosed_adjoinRoot`) via the conjugation involution on
`R[i]`.
-/

namespace Hilbert17Blueprint

open Polynomial

variable {R : Type*} [Field R] [IsRealClosed R]

local notation "K" => AdjoinRoot (X ^ 2 + 1 : R[X])

/-- A positive-definite quadratic `(X - a)² + b²` (with `b ≠ 0`) has no root in a real closed field:
a root would make `-1` a square, contradicting semireality. -/
theorem eval_quadratic_ne_zero {a b : R} (hb : b ≠ 0) (r : R) :
    ((X - C a) ^ 2 + C b ^ 2).eval r ≠ 0 := by
  simp only [eval_add, eval_pow, eval_sub, eval_X, eval_C]
  intro h
  have hbb : b * b⁻¹ = 1 := mul_inv_cancel₀ hb
  have hrel : (r - a) * (r - a) = -(b * b) := by linear_combination h
  have hx : ((r - a) * b⁻¹) * ((r - a) * b⁻¹) = -1 := by
    have hsplit : ((r - a) * b⁻¹) * ((r - a) * b⁻¹)
        = ((r - a) * (r - a)) * (b⁻¹ * b⁻¹) := by ring
    rw [hsplit, hrel,
      show -(b * b) * (b⁻¹ * b⁻¹) = -((b * b⁻¹) * (b * b⁻¹)) from by ring, hbb]
    ring
  exact IsSemireal.one_add_ne_zero (IsSumSq.mul_self _) (by rw [hx]; ring)

/-- A positive-definite quadratic `(X - a)² + b²` (with `b ≠ 0`) is monic of degree `2`. -/
theorem monic_quadratic (a b : R) : ((X - C a) ^ 2 + C b ^ 2).Monic := by
  monicity!

/-- A positive-definite quadratic `(X - a)² + b²` (with `b ≠ 0`) has degree `2`. -/
theorem natDegree_quadratic (a b : R) : ((X - C a) ^ 2 + C b ^ 2).natDegree = 2 := by
  compute_degree!

/-- A positive-definite quadratic `(X - a)² + b²` (with `b ≠ 0`) is irreducible over a real closed
field: it is monic of degree `2` with no root. -/
theorem irreducible_quadratic {a b : R} (hb : b ≠ 0) :
    Irreducible ((X - C a) ^ 2 + C b ^ 2) := by
  rw [(monic_quadratic a b).irreducible_iff_roots_eq_zero_of_degree_le_three
    (natDegree_quadratic a b).ge ((natDegree_quadratic a b).le.trans (by norm_num))]
  rw [Multiset.eq_zero_iff_forall_notMem]
  intro r hr
  exact eval_quadratic_ne_zero hb r ((mem_roots'.1 hr).2)

section Ordered

variable [LinearOrder R] [IsStrictOrderedRing R]

/-- **Classification of monic irreducibles over a real closed field.** A monic polynomial is
irreducible iff it is linear or a positive-definite quadratic `(X - a)² + b²` with `b ≠ 0`. -/
theorem irred_poly_classify {f : R[X]} (hf : f.Monic) :
    Irreducible f ↔
      f.natDegree = 1 ∨ (∃ a b : R, b ≠ 0 ∧ f = (X - C a) ^ 2 + C b ^ 2) := by
  haveI : Fact (Irreducible (X ^ 2 + 1 : R[X])) := ⟨irreducible_X_sq_add_one⟩
  haveI : IsAlgClosed K := isAlgClosed_adjoinRoot
  haveI : Module.Finite R K :=
    (show (X ^ 2 + 1 : R[X]).Monic by monicity!).finite_adjoinRoot
  have hφinj : Function.Injective (algebraMap R K) := FaithfulSMul.algebraMap_injective R K
  constructor
  · intro hirr
    -- `f` has a root `z` in `R[i]`.
    have hmapdeg : (f.map (algebraMap R K)).degree ≠ 0 := by
      rw [degree_map_eq_of_injective hφinj]
      exact (degree_pos_of_irreducible hirr).ne'
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (f.map (algebraMap R K)) hmapdeg
    have hzaeval : aeval z f = 0 := by
      have h := hz; rw [IsRoot, eval_map, ← aeval_def] at h; exact h
    by_cases hzr : z ∈ Set.range (algebraMap R K)
    · -- Real root: `f` is linear.
      obtain ⟨b, rfl⟩ := hzr
      left
      have hb0 : f.eval b = 0 := by
        have h := hz
        rw [IsRoot, eval_map, Polynomial.eval₂_at_apply] at h
        exact hφinj (h.trans (map_zero _).symm)
      obtain ⟨c, hc⟩ := dvd_iff_isRoot.2 hb0
      rcases hirr.isUnit_or_isUnit hc with hu | hu
      · simp [Polynomial.isUnit_iff_degree_eq_zero, degree_X_sub_C] at hu
      · rw [hc, natDegree_mul (X_sub_C_ne_zero b) hu.ne_zero, natDegree_X_sub_C,
          Polynomial.natDegree_eq_zero_of_isUnit hu]
    · -- Non-real root: `z, conj z` give a positive-definite quadratic factor equal to `f`.
      right
      obtain ⟨p, q, hzeq⟩ := exists_repr z
      have hp : p ≠ 0 := by
        rintro rfl
        exact hzr ⟨q, by rw [hzeq, map_zero, zero_mul, zero_add]⟩
      refine ⟨q, p, hp, ?_⟩
      have hwaeval : aeval z ((X - C q) ^ 2 + C p ^ 2) = 0 := by
        have hzq : z - algebraMap R K q
            = algebraMap R K p * AdjoinRoot.root (X ^ 2 + 1 : R[X]) := by rw [hzeq]; ring
        simp only [map_add, map_pow, map_sub, aeval_X, aeval_C]
        rw [hzq, mul_pow, root_sq]; ring
      rw [minpoly.eq_of_irreducible_of_monic hirr hzaeval hf,
        minpoly.eq_of_irreducible_of_monic (irreducible_quadratic hp) hwaeval (monic_quadratic q p)]
  · rintro (lin | ⟨a, b, hb, rfl⟩)
    · exact Polynomial.irreducible_of_degree_eq_one
        (by rw [Polynomial.degree_eq_natDegree hf.ne_zero, lin]; rfl)
    · exact irreducible_quadratic hb

/-- **Intermediate value property for polynomials over a real closed field.** If `f ≥ 0` at `x` and
`f ≤ 0` at some `y ≥ x`, then `f` has a root in `[x, y]`. Proved by strong induction on the degree,
peeling off monic irreducible factors: quadratic factors `(X - a)² + b²` are everywhere positive (so
cannot cause the sign change), while a linear factor supplies the root. -/
theorem intermediate_value_property {f : R[X]} {x y : R}
    (hle : x ≤ y) (hx : 0 ≤ f.eval x) (hy : f.eval y ≤ 0) :
    ∃ z ∈ Set.Icc x y, f.eval z = 0 := by
  induction hdeg : f.natDegree using Nat.strong_induction_on generalizing f with
  | _ n ih =>
    subst hdeg
    by_cases hz : f.natDegree = 0
    · rw [f.eq_C_of_natDegree_eq_zero hz] at hx hy ⊢
      exact ⟨x, ⟨le_refl x, hle⟩, le_antisymm (by simpa using hy) (by simpa using hx)⟩
    have hpos := Nat.pos_of_ne_zero hz
    by_cases hdiv : ∃ g : R[X], 0 < g.natDegree ∧ g ∣ f ∧ 0 < g.eval y ∧ 0 < g.eval x
    · obtain ⟨g, hg_deg, ⟨k, rfl⟩, hg_y, hg_x⟩ := hdiv
      have hgne : g ≠ 0 := fun h => by simp [h] at hg_deg
      have hkne : k ≠ 0 := by rintro rfl; rw [mul_zero] at hpos; simp at hpos
      rw [Polynomial.natDegree_mul hgne hkne] at ih
      rw [eval_mul] at hx hy
      obtain ⟨z, hz_m, hz_e⟩ := ih k.natDegree (by omega) (by nlinarith) (by nlinarith) rfl
      exact ⟨z, hz_m,
        Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (Dvd.intro_left g rfl) hz_e⟩
    · push_neg at hdiv
      obtain ⟨g, hg_m, hg_i, hg_d⟩ :=
        Polynomial.exists_monic_irreducible_factor f (f.not_isUnit_of_natDegree_pos hpos)
      rcases (irred_poly_classify hg_m).mp hg_i with lin | ⟨a, b, hb, g_eq⟩
      · -- Linear factor `g = X + C (g.coeff 0)`, with root `r₀ = -g.coeff 0`.
        have hg_eq : g = X + C (g.coeff 0) := hg_m.eq_X_add_C lin
        have hgpos : 0 < g.natDegree := by rw [lin]; norm_num
        set r₀ : R := -g.coeff 0 with hr₀
        have hroot : g.eval r₀ = 0 := by rw [hg_eq]; simp [hr₀]
        have hfr : f.eval r₀ = 0 := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hg_d hroot
        have hgx : g.eval x = x - r₀ := by rw [hg_eq]; simp [hr₀]
        have hgy : g.eval y = y - r₀ := by rw [hg_eq]; simp [hr₀]
        by_cases le_y : r₀ < y
        · have hx' : g.eval x ≤ 0 := hdiv g hgpos hg_d (by rw [hgy]; linarith)
          rw [hgx] at hx'
          exact ⟨r₀, ⟨by linarith, by linarith⟩, hfr⟩
        · by_cases y_le : y < r₀
          · have hng : 0 < (-g).natDegree := by rw [natDegree_neg]; exact hgpos
            have hx' : (-g).eval x ≤ 0 :=
              hdiv (-g) hng (neg_dvd.mpr hg_d) (by simp only [eval_neg, hgy]; linarith)
            simp only [eval_neg, hgx] at hx'
            linarith
          · exact ⟨r₀, ⟨by linarith, by linarith⟩, hfr⟩
      · -- Quadratic factor, everywhere positive: contradicts the sign change.
        have pos : ∀ z, 0 < g.eval z := fun z => by
          rw [g_eq]; simp only [eval_add, eval_pow, eval_sub, eval_X, eval_C]; positivity
        have := hdiv g hg_i.natDegree_pos hg_d (pos y)
        linarith [pos x]

end Ordered

end Hilbert17Blueprint
