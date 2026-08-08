/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.Monogenic.Exponent

/-!
# Monogenicity criteria at a double root modulo `p`

The *accompanying paper* referred to in the docstrings below is

> M. Karatarakis, *A Local Approach to Monogenity with an Application to Lenny Jones'
> Conjecture*,

which is the write-up of this development; each result it states is named in the docstring
of the declaration formalising it.

Let `K` be a number field, `θ : 𝓞 K` with minimal polynomial `f` over `ℤ`, and let `p` be a
rational prime.  Suppose `r : ℤ` is a double root of `f` modulo `p`, that is, `p ∣ f(r)` and
`p ∣ f'(r)`.  This file proves the two halves of Dedekind's index criterion in this situation:

* `RingOfIntegers.dvd_exponent_of_sq_dvd_eval` (necessity): if moreover `p ^ 2 ∣ f(r)`, then
  `p` divides the exponent of `θ`; in particular `ℤ[θ] ≠ 𝓞 K`
  (`RingOfIntegers.adjoin_ne_top_of_sq_dvd_eval`).  The obstruction is the explicit algebraic
  integer `(θ - r) * g(θ) / p`, where `f = f(r) + f'(r) (X - r) + (X - r)^2 g`.

* `RingOfIntegers.not_dvd_exponent_of_sq_not_dvd_eval` (sufficiency, for a "tame" double
  root): if `p ^ 2 ∤ f(r)`, `p ∤ f''(r)` and every maximal ideal above `p` containing the
  conductor of `θ` also contains `θ - r`, then `p` does not divide the exponent of `θ`, i.e.
  `ℤ[θ]` is maximal at `p`.

Together with `RingOfIntegers.not_dvd_exponent_of_minpoly_isEisensteinAt`, these results can
replace Dedekind's criterion in the computation of rings of integers whose minimal polynomial
has at most one repeated root modulo each ramified prime, of multiplicity two.  This is used
to prove the Kaur–Kumar theorem on monogenicity of `X ^ n + A (B X + 1) ^ m` in
`Mathlib/NumberTheory/NumberField/Monogenic/KaurKumar.lean`.

## References

* [S. Kaur, S. Kumar, *On a conjecture of Lenny Jones about certain monogenic polynomials*,
  Bull. Aust. Math. Soc. (2023)][kaurkumar2023]
-/

@[expose] public section

noncomputable section

open Polynomial NumberField Ideal

/-! ### Order-two Taylor decompositions of a polynomial -/

namespace Polynomial

variable {R : Type*} [CommRing R]

theorem leadingCoeff_divX {p : R[X]} (h : 1 ≤ p.natDegree) :
    p.divX.leadingCoeff = p.leadingCoeff := by
  rw [leadingCoeff, natDegree_divX_eq_natDegree_tsub_one, coeff_divX,
    Nat.sub_add_cancel h, leadingCoeff]

/-- Order-one Taylor decomposition of a polynomial at `r`:
`f = f(r) + (X - r) g` where `g(r) = f'(r)`. -/
theorem exists_eq_C_eval_add_X_sub_C_mul (f : R[X]) (r : R) :
    ∃ g : R[X], f = C (f.eval r) + (X - C r) * g ∧ g.eval r = (derivative f).eval r := by
  refine ⟨((taylor r f).divX).comp (X - C r), ?_, ?_⟩
  · have h0 : (taylor r f).comp (X - C r) = f := by
      rw [taylor_apply, comp_assoc]
      simp
    conv_lhs => rw [← h0, ← X_mul_divX_add (taylor r f)]
    rw [add_comp, mul_comp, X_comp, C_comp, taylor_coeff_zero]
    ring
  · rw [eval_comp]
    simp only [eval_sub, eval_X, eval_C, sub_self, ← coeff_zero_eq_eval_zero, coeff_divX,
      zero_add, taylor_coeff_one]

/-- Order-two Taylor decomposition of a polynomial at `r`:
`f = f(r) + f'(r) (X - r) + (X - r)^2 g` where `g(r)` is the second Hasse derivative of `f`
at `r`, and `g` has the same leading coefficient as `f` and degree `deg f - 2`. -/
theorem exists_eq_C_eval_add_X_sub_C_sq_mul (f : R[X]) (r : R) :
    ∃ g : R[X], f = C (f.eval r) + C ((derivative f).eval r) * (X - C r) + (X - C r) ^ 2 * g ∧
      g.eval r = (hasseDeriv 2 f).eval r ∧
      g.natDegree = f.natDegree - 2 ∧
      (2 ≤ f.natDegree → g.leadingCoeff = f.leadingCoeff) := by
  set q : R[X] := ((taylor r f).divX).divX with hq
  refine ⟨q.comp (X - C r), ?_, ?_, ?_, fun hdeg => ?_⟩
  · have h0 : (taylor r f).comp (X - C r) = f := by
      rw [taylor_apply, comp_assoc]
      simp
    have h1 : taylor r f =
        C (f.eval r) + C ((derivative f).eval r) * X + X ^ 2 * q := by
      conv_lhs => rw [← X_mul_divX_add (taylor r f), ← X_mul_divX_add ((taylor r f).divX)]
      rw [taylor_coeff_zero, coeff_divX, zero_add, taylor_coeff_one]
      ring
    conv_lhs => rw [← h0, h1]
    simp only [add_comp, mul_comp, C_comp, X_comp, pow_comp]
  · rw [eval_comp]
    simp only [eval_sub, eval_X, eval_C, sub_self, ← coeff_zero_eq_eval_zero]
    rw [hq, coeff_divX, coeff_divX]
    simpa using taylor_coeff (r := r) (f := f) 2
  · have hcomp : q.comp (X - C r) = taylor (-r) q := by
      rw [taylor_apply, map_neg, ← sub_eq_add_neg]
    rw [hcomp, natDegree_taylor, hq, natDegree_divX_eq_natDegree_tsub_one,
      natDegree_divX_eq_natDegree_tsub_one, natDegree_taylor]
    omega
  · have hcomp : q.comp (X - C r) = taylor (-r) q := by
      rw [taylor_apply, map_neg, ← sub_eq_add_neg]
    have h1 : 1 ≤ (taylor r f).natDegree := by rw [natDegree_taylor]; omega
    have h2 : 1 ≤ (taylor r f).divX.natDegree := by
      rw [natDegree_divX_eq_natDegree_tsub_one, natDegree_taylor]; omega
    rw [hcomp, leadingCoeff_taylor, hq, leadingCoeff_divX h2, leadingCoeff_divX h1,
      leadingCoeff_taylor]

/-- Twice the second Hasse derivative, evaluated at `r`, is the second derivative at `r`. -/
theorem two_mul_hasseDeriv_two_eval (f : R[X]) (r : R) :
    2 * (hasseDeriv 2 f).eval r = (derivative (derivative f)).eval r := by
  have h := congrFun (factorial_smul_hasseDeriv (R := R) 2) f
  have h2 : Nat.factorial 2 = 2 := rfl
  rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply] at h
  rw [← h]
  simp [h2, two_smul, two_mul]

end Polynomial

/-! ### The two halves of the criterion -/

namespace RingOfIntegers

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {p : ℕ} [hp : Fact p.Prime] {r : ℤ}

omit [NumberField K] in
/-- The fundamental relation in `𝓞 K` attached to the order-two Taylor decomposition
`f = f(r) + f'(r) (X - r) + (X - r) ^ 2 g` of the minimal polynomial `f` of `θ`:
`(θ - r) ^ 2 g(θ) = -(f(r) + f'(r) (θ - r))`. -/
private theorem sq_mul_aeval_eq_neg {g : ℤ[X]}
    (hfeq : minpoly ℤ θ = C ((minpoly ℤ θ).eval r) +
      C ((derivative (minpoly ℤ θ)).eval r) * (X - C r) + (X - C r) ^ 2 * g) :
    (θ - (r : 𝓞 K)) ^ 2 * aeval θ g =
      -((((minpoly ℤ θ).eval r : ℤ) : 𝓞 K) +
        (((derivative (minpoly ℤ θ)).eval r : ℤ) : 𝓞 K) * (θ - (r : 𝓞 K))) := by
  have h := congrArg (aeval θ) hfeq
  rw [minpoly.aeval] at h
  simp only [map_add, map_mul, map_pow, aeval_X, map_sub, eq_intCast, map_intCast] at h
  linear_combination -h

/-- The `𝔪`-adic multiplicity of a nonzero principal ideal is finite. -/
private theorem exists_emultiplicity_span_singleton_eq {𝔪 : Ideal (𝓞 K)} (h𝔪 : Prime 𝔪)
    {x : 𝓞 K} (hx : x ≠ 0) : ∃ k : ℕ, emultiplicity 𝔪 (Ideal.span {x}) = k :=
  have hfin : FiniteMultiplicity 𝔪 (Ideal.span {x}) :=
    FiniteMultiplicity.of_prime_left h𝔪 (by
      rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hx)
  ⟨multiplicity 𝔪 _, hfin.emultiplicity_eq_multiplicity⟩

/-- The obstruction element attached to a double root `r` of the minimal polynomial `f` of
`θ` modulo `p` with `p ^ 2 ∣ f(r)`: the algebraic integer `z = (θ - r) g(θ) / p`, where
`f = f(r) + f'(r)(X - r) + (X - r)^2 g`, satisfies `p * z ∈ ℤ[θ]` but `z ∉ ℤ[θ]`. -/
private theorem exists_mul_mem_adjoin_notMem_adjoin (hdeg : 2 ≤ (minpoly ℤ θ).natDegree)
    (h₀ : (p : ℤ) ^ 2 ∣ (minpoly ℤ θ).eval r)
    (h₁ : (p : ℤ) ∣ (derivative (minpoly ℤ θ)).eval r) :
    ∃ z : 𝓞 K, (p : 𝓞 K) * z ∈ Algebra.adjoin ℤ {θ} ∧ z ∉ Algebra.adjoin ℤ {θ} := by
  obtain ⟨g, hfeq, -, hgdeg, hglead⟩ :=
    (minpoly ℤ θ).exists_eq_C_eval_add_X_sub_C_sq_mul r
  obtain ⟨t, ht⟩ := h₀
  obtain ⟨k, hk⟩ := h₁
  set f : ℤ[X] := minpoly ℤ θ with hf
  set π : 𝓞 K := θ - (r : ℤ) with hπ
  set S : 𝓞 K := aeval θ g with hS
  -- the fundamental relation `π ^ 2 * S = -(f(r) + f'(r) * π)` in `𝓞 K`
  have hrel : π ^ 2 * S =
      -(((f.eval r : ℤ) : 𝓞 K) + (((derivative f).eval r : ℤ) : 𝓞 K) * π) :=
    sq_mul_aeval_eq_neg hfeq
  -- `y = π * S` satisfies the monic quadratic `y ^ 2 + f'(r) y + f(r) S = 0`
  set y : 𝓞 K := π * S with hydef
  have hy : y ^ 2 + ((p : 𝓞 K) * (k : 𝓞 K)) * y + ((p : 𝓞 K) ^ 2 * (t : 𝓞 K)) * S = 0 := by
    have e1 : (((derivative f).eval r : ℤ) : 𝓞 K) = (p : 𝓞 K) * (k : 𝓞 K) := by
      rw [hk]; push_cast; ring
    have e2 : ((f.eval r : ℤ) : 𝓞 K) = (p : 𝓞 K) ^ 2 * (t : 𝓞 K) := by
      rw [ht]; push_cast; ring
    rw [hydef, ← e1, ← e2]
    linear_combination S * hrel
  -- hence `z = y / p ∈ K` is integral over `𝓞 K`, so `y = p * z'` with `z' : 𝓞 K`
  have hpK : ((p : ℕ) : K) ≠ 0 := by
    exact_mod_cast hp.out.ne_zero
  set z : K := algebraMap (𝓞 K) K y / p with hz
  have hzy : (p : K) * z = algebraMap (𝓞 K) K y := by
    rw [hz]; field_simp
  have hzint : IsIntegral (𝓞 K) z := by
    refine ⟨X ^ 2 + (C ((k : ℤ) : 𝓞 K) * X + C (((t : ℤ) : 𝓞 K) * S)), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_add
        (lt_of_le_of_lt Polynomial.degree_linear_le (by norm_num))
    · simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]
      have hyK := congrArg (algebraMap (𝓞 K) K) hy
      simp only [map_add, map_mul, map_pow, map_zero, map_natCast, map_intCast] at hyK
      rw [← hzy] at hyK
      have hp2 : ((p : K)) ^ 2 ≠ 0 := pow_ne_zero _ hpK
      rw [map_mul, map_intCast, map_intCast]
      have hgoal : (p : K) ^ 2 *
          (z ^ 2 + ((k : K) * z + (t : K) * algebraMap (𝓞 K) K S)) = 0 := by
        linear_combination hyK
      have := (mul_eq_zero.mp hgoal).resolve_left hp2
      linear_combination this
  have hzint' : IsIntegral ℤ z := isIntegral_trans z hzint
  obtain ⟨z', hz'⟩ := IsIntegralClosure.isIntegral_iff (A := 𝓞 K) |>.mp hzint'
  have hpz' : (p : 𝓞 K) * z' = y := by
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    rw [map_mul, hz', map_natCast, hzy]
  refine ⟨z', ?_, ?_⟩
  · -- `p * z' = (θ - r) g(θ)` visibly lies in `ℤ[θ]`
    rw [hpz', hydef, hπ, hS]
    exact mul_mem (sub_mem (Algebra.self_mem_adjoin_singleton ℤ θ)
      (Subalgebra.intCast_mem _ r)) (Polynomial.aeval_mem_adjoin_singleton ℤ θ)
  -- if `z'` were in `ℤ[θ]`, then `π S = p c(θ)` with `deg c < deg f`
  intro hz'mem
  have hfmonic : f.Monic := hf ▸ minpoly.monic θ.isIntegral
  have haevf : aeval θ f = 0 := hf ▸ minpoly.aeval ℤ θ
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hz'mem
  obtain ⟨c, hc⟩ := hz'mem
  replace hc : aeval θ c = z' := hc
  set c' : ℤ[X] := c %ₘ f with hc'
  have haevalc' : aeval θ c' = z' := by
    rw [hc', Polynomial.modByMonic_eq_sub_mul_div c f, map_sub,
      map_mul, haevf, zero_mul, sub_zero, hc]
  have hdegc' : c'.degree < f.degree :=
    Polynomial.degree_modByMonic_lt c hfmonic
  -- the polynomial `W = (X - r) g` is monic of degree `n - 1` and `W(θ) = π S = p c'(θ)`
  set W : ℤ[X] := (X - C r) * g with hW
  have hgne : g ≠ 0 := fun h => by
    have := hglead hdeg
    rw [h, Polynomial.leadingCoeff_zero] at this
    exact one_ne_zero (this.trans (minpoly.monic θ.isIntegral).leadingCoeff).symm
  have hWdeg : W.natDegree = f.natDegree - 1 := by
    rw [hW, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero r) hgne,
      Polynomial.natDegree_X_sub_C, hgdeg]
    omega
  have hgmonic : g.Monic := by
    have h := hglead hdeg
    rw [Polynomial.Monic.def, h]
    exact (minpoly.monic θ.isIntegral).leadingCoeff
  have hWmonic : W.Monic := (Polynomial.monic_X_sub_C r).mul hgmonic
  have haevalW : aeval θ W = y := by
    rw [hW, map_mul, hydef, hS, hπ]
    congr 1
    simp only [map_sub, aeval_X, eq_intCast, map_intCast]
  -- `W - p c'` annihilates `θ` and has degree `< deg f`, so it vanishes
  have hann : aeval θ (W - C (p : ℤ) * c') = 0 := by
    rw [map_sub, haevalW, map_mul, aeval_C, haevalc', ← hpz', algebraMap_int_eq, eq_intCast,
      Int.cast_natCast]
    ring
  have hfne : f ≠ 0 := minpoly.ne_zero θ.isIntegral
  have hdegW : W.degree < f.degree := by
    rw [Polynomial.degree_eq_natDegree hWmonic.ne_zero, Polynomial.degree_eq_natDegree hfne,
      hWdeg]
    exact_mod_cast Nat.sub_lt (by omega) one_pos
  have hdeglt : (W - C (p : ℤ) * c').degree < f.degree := by
    apply lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
    rw [max_lt_iff]
    refine ⟨hdegW, lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_⟩
    rw [Polynomial.degree_C (by exact_mod_cast hp.out.ne_zero), zero_add]
    exact hdegc'
  have hWeq : W = C (p : ℤ) * c' := by
    by_contra hne
    have hsubne : W - C (p : ℤ) * c' ≠ 0 := sub_ne_zero_of_ne hne
    have hmapne : (W - C (p : ℤ) * c').map (algebraMap ℤ ℚ) ≠ 0 := by
      rwa [Ne, Polynomial.map_eq_zero_iff (algebraMap ℤ ℚ).injective_int]
    have haev : Polynomial.aeval ((θ : K)) ((W - C (p : ℤ) * c').map (algebraMap ℤ ℚ)) = 0 := by
      rw [aeval_map_algebraMap, aeval_algebraMap_apply, hann, map_zero]
    have hge := minpoly.degree_le_of_ne_zero ℚ ((θ : K)) hmapne haev
    rw [minpoly.isIntegrallyClosed_eq_field_fractions ℚ K θ.isIntegral,
      Polynomial.degree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int,
      Polynomial.degree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int] at hge
    exact absurd (hge.trans_lt hdeglt) (lt_irrefl _)
  -- comparing leading coefficients gives `p ∣ 1`, a contradiction
  have hlead : (1 : ℤ) = (p : ℤ) * c'.leadingCoeff := by
    have := congrArg Polynomial.leadingCoeff hWeq
    rwa [hWmonic.leadingCoeff, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C] at this
  have : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos (Dvd.intro _ hlead.symm)
  have h2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.out.two_le
  omega

/-- **Necessity half of Dedekind's criterion at a double root, exponent form.**
If `r` is a root of the minimal polynomial `f` of `θ` modulo `p` which is also a root of `f'`
modulo `p`, and if moreover `p ^ 2 ∣ f(r)`, then `p` divides the exponent of `θ` (the index
`[𝓞 K : ℤ[θ]]`, in the sense of `RingOfIntegers.exponent`): the algebraic integer
`z = (θ - r) g(θ) / p`, where `f = f(r) + f'(r)(X - r) + (X - r)^2 g`, satisfies
`p * z ∈ ℤ[θ]` but `z ∉ ℤ[θ]`, so `ℤ[θ]` is not maximal at `p`.

Accompanying paper: the necessity half of the double-root criterion, replacing
Dedekind's index criterion. -/
theorem dvd_exponent_of_sq_dvd_eval (hdeg : 2 ≤ (minpoly ℤ θ).natDegree)
    (h₀ : (p : ℤ) ^ 2 ∣ (minpoly ℤ θ).eval r)
    (h₁ : (p : ℤ) ∣ (derivative (minpoly ℤ θ)).eval r) :
    p ∣ exponent θ := by
  obtain ⟨z, hpz, hz⟩ := exists_mul_mem_adjoin_notMem_adjoin hdeg h₀ h₁
  by_contra hpe
  -- `p` is coprime to the exponent `e`, so `1 = u p + v e` for some integers `u`, `v`
  have hpZ : ¬(p : ℤ) ∣ ((exponent θ : ℕ) : ℤ) := fun h =>
    hpe (Int.natCast_dvd_natCast.mp h)
  obtain ⟨u, v, huv⟩ : IsCoprime ((p : ℤ)) ((exponent θ : ℤ)) :=
    (Nat.prime_iff_prime_int.mp hp.out).coprime_iff_not_dvd.mpr hpZ
  -- `e` lies in the conductor, hence `e * z ∈ ℤ[θ]`; but also `p * z ∈ ℤ[θ]`
  have hEmem : ((exponent θ : 𝓞 K)) ∈ conductor ℤ θ := Int.absNorm_under_mem (conductor ℤ θ)
  have hez : ((exponent θ : 𝓞 K)) * z ∈ Algebra.adjoin ℤ {θ} := mem_conductor_iff.mp hEmem z
  -- so `z = u (p z) + v (e z) ∈ ℤ[θ]`, a contradiction
  apply hz
  have hzeq : z = (u : 𝓞 K) * ((p : 𝓞 K) * z) + (v : 𝓞 K) * ((exponent θ : 𝓞 K) * z) := by
    have h := congrArg (fun t : ℤ => ((t : ℤ) : 𝓞 K)) huv
    push_cast at h
    linear_combination -z * h
  rw [hzeq]
  exact add_mem (mul_mem (Subalgebra.intCast_mem _ u) hpz)
    (mul_mem (Subalgebra.intCast_mem _ v) hez)

/-- **Necessity half of Dedekind's criterion at a double root.**
If `r` is a root of the minimal polynomial `f` of `θ` modulo `p` which is also a root of `f'`
modulo `p`, and if moreover `p ^ 2 ∣ f(r)`, then `ℤ[θ]` is not the full ring of integers.
This is the special case "`exponent θ = 1` is impossible" of
`RingOfIntegers.dvd_exponent_of_sq_dvd_eval`. -/
theorem adjoin_ne_top_of_sq_dvd_eval (hdeg : 2 ≤ (minpoly ℤ θ).natDegree)
    (h₀ : (p : ℤ) ^ 2 ∣ (minpoly ℤ θ).eval r)
    (h₁ : (p : ℤ) ∣ (derivative (minpoly ℤ θ)).eval r) :
    Algebra.adjoin ℤ {θ} ≠ ⊤ := by
  intro htop
  have h := dvd_exponent_of_sq_dvd_eval hdeg h₀ h₁
  rw [exponent_eq_one_iff.mpr htop, Nat.dvd_one] at h
  exact hp.out.ne_one h

omit [NumberField K] in
/-- If `𝔪` is a maximal ideal of `𝓞 K` containing the rational prime `p`, then an integer
lies in `𝔪` if and only if it is divisible by `p`. -/
theorem intCast_mem_iff_dvd {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪.IsMaximal)
    (hp𝔪 : (p : 𝓞 K) ∈ 𝔪) (t : ℤ) : (t : 𝓞 K) ∈ 𝔪 ↔ (p : ℤ) ∣ t := by
  constructor
  · intro ht
    have h1 : Ideal.span {(p : ℤ)} ≤ Ideal.comap (algebraMap ℤ (𝓞 K)) 𝔪 := by
      rw [Ideal.span_le]
      simpa using hp𝔪
    have h2 : Ideal.comap (algebraMap ℤ (𝓞 K)) 𝔪 ≠ ⊤ := by
      intro h
      exact h𝔪.ne_top (Ideal.eq_top_iff_one _ |>.mpr (by
        have := Ideal.eq_top_iff_one _ |>.mp h
        rw [Ideal.mem_comap, map_one] at this
        exact this))
    have h3 : Ideal.comap (algebraMap ℤ (𝓞 K)) 𝔪 = Ideal.span {(p : ℤ)} :=
      ((Int.ideal_span_isMaximal_of_prime p).eq_of_le h2 h1).symm
    have h4 : t ∈ Ideal.comap (algebraMap ℤ (𝓞 K)) 𝔪 := by
      rw [Ideal.mem_comap]
      simpa using ht
    rw [h3, Ideal.mem_span_singleton] at h4
    exact h4
  · rintro ⟨s, rfl⟩
    push_cast
    exact Ideal.mul_mem_right _ _ hp𝔪

/-- **Sufficiency half of Dedekind's criterion at a tame double root.**
Let `f` be the minimal polynomial of `θ` and let `p` be a rational prime.  Suppose that
`r : ℤ` satisfies `p ^ 2 ∤ f(r)` and `p ∤ f''(r)`, and that every maximal ideal of `𝓞 K`
containing `p` and the conductor of `θ` also contains `θ - r` (that is, `r` is the only
repeated root of `f` mod `p` that can obstruct `p`-maximality).  Then `p` does not divide
the exponent of `θ`, i.e. `ℤ[θ]` is `p`-maximal.

Accompanying paper: the sufficiency half of the double-root criterion at a tame double root. -/
theorem not_dvd_exponent_of_sq_not_dvd_eval (hθ : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (h₂ : ¬(p : ℤ) ^ 2 ∣ (minpoly ℤ θ).eval r)
    (h'' : ¬(p : ℤ) ∣ (derivative (derivative (minpoly ℤ θ))).eval r)
    (hroot : ∀ 𝔪 : Ideal (𝓞 K), 𝔪.IsMaximal → conductor ℤ θ ≤ 𝔪 → (p : 𝓞 K) ∈ 𝔪 →
      θ - (r : 𝓞 K) ∈ 𝔪) :
    ¬p ∣ exponent θ := by
  rw [not_dvd_exponent_iff_conductor_sup_span_eq_top]
  by_contra hsup
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hsup
  have hcond : conductor ℤ θ ≤ 𝔪 := le_trans le_sup_left hle
  have hpmem : (p : 𝓞 K) ∈ 𝔪 := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hπmem : θ - (r : 𝓞 K) ∈ 𝔪 := hroot 𝔪 h𝔪 hcond hpmem
  set f : ℤ[X] := minpoly ℤ θ with hfdef
  -- Taylor decompositions of `f` at `r` and of `f'` at `r`
  obtain ⟨g, hfeq, hg2, -, -⟩ := f.exists_eq_C_eval_add_X_sub_C_sq_mul r
  obtain ⟨g₁, hf'eq, hg₁⟩ := (derivative f).exists_eq_C_eval_add_X_sub_C_mul r
  set π : 𝓞 K := θ - (r : 𝓞 K) with hπ
  set S : 𝓞 K := aeval θ g with hS
  set T : 𝓞 K := aeval θ g₁ with hT
  -- the fundamental relations in `𝓞 K`
  have hrel : π ^ 2 * S =
      -(((f.eval r : ℤ) : 𝓞 K) + (((derivative f).eval r : ℤ) : 𝓞 K) * π) :=
    sq_mul_aeval_eq_neg hfeq
  have hrel' : aeval θ (derivative f) = (((derivative f).eval r : ℤ) : 𝓞 K) + π * T := by
    have h := congrArg (aeval θ) hf'eq
    simp only [map_add, map_mul, aeval_X, map_sub, eq_intCast, map_intCast] at h
    rw [hπ, hT]
    linear_combination h
  -- `f'(θ)` lies in `𝔪` since it lies in the conductor
  have hf'mem : aeval θ (derivative f) ∈ 𝔪 := hcond (aeval_derivative_minpoly_mem_conductor hθ)
  -- membership facts modulo `𝔪`
  have hc₁ : (p : ℤ) ∣ (derivative f).eval r := by
    rw [← intCast_mem_iff_dvd h𝔪 hpmem]
    have : (((derivative f).eval r : ℤ) : 𝓞 K) = aeval θ (derivative f) - π * T := by
      rw [hrel']; ring
    rw [this]
    exact Submodule.sub_mem _ hf'mem (Ideal.mul_mem_right _ _ hπmem)
  have hc₀ : (p : ℤ) ∣ f.eval r := by
    rw [← intCast_mem_iff_dvd h𝔪 hpmem]
    have : ((f.eval r : ℤ) : 𝓞 K) = -(π ^ 2 * S) - (((derivative f).eval r : ℤ) : 𝓞 K) * π := by
      rw [hrel]; ring
    rw [this]
    refine Submodule.sub_mem _ (Submodule.neg_mem _ ?_) (Ideal.mul_mem_left _ _ hπmem)
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hπmem _ two_pos)
  -- `p ∤ f''(r)` forces `S ∉ 𝔪` and `T ∉ 𝔪`
  have haux : ∀ q : ℤ[X], ¬((p : ℤ) ∣ q.eval r) → aeval θ q ∉ 𝔪 := by
    intro q hq hmem
    apply hq
    rw [← intCast_mem_iff_dvd h𝔪 hpmem]
    obtain ⟨w, hw⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (a := r) (p := q)
    have : ((q.eval r : ℤ) : 𝓞 K) = aeval θ q - π * aeval θ w := by
      have := congrArg (aeval θ) hw
      simp only [map_sub, eq_intCast, map_mul, aeval_X, map_intCast] at this
      rw [hπ]
      linear_combination -this
    rw [this]
    exact Submodule.sub_mem _ hmem (Ideal.mul_mem_right _ _ hπmem)
  have hSmem : S ∉ 𝔪 := by
    apply haux
    rw [hg2]
    intro hdvd
    exact h'' (by
      rw [← f.two_mul_hasseDeriv_two_eval r]
      exact Dvd.dvd.mul_left hdvd 2)
  have hTmem : T ∉ 𝔪 := by
    apply haux
    rw [hg₁]
    exact h''
  -- `π ≠ 0`: otherwise the minimal polynomial is linear and `f'' = 0`
  have hπne : π ≠ 0 := by
    intro h
    apply h''
    have hθr : θ = ((r : ℤ) : 𝓞 K) := by rwa [hπ, sub_eq_zero] at h
    have : f = X - C r := by
      rw [hfdef, hθr]
      exact minpoly.eq_X_sub_C_of_algebraMap_inj _
        (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))
    rw [this]
    simp
  -- exact `𝔪`-adic valuations
  have h𝔪bot : 𝔪 ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpmem
    exact hp.out.ne_zero (by exact_mod_cast hpmem)
  have h𝔪prime : Prime 𝔪 := Ideal.prime_of_isPrime h𝔪bot h𝔪.isPrime
  -- write `f(r) = p t` with `p ∤ t` and `f'(r) = p k`
  obtain ⟨t, ht⟩ := hc₀
  obtain ⟨k, hk⟩ := hc₁
  have hpt : ¬(p : ℤ) ∣ t := by
    rintro ⟨s, rfl⟩
    exact h₂ ⟨s, by rw [ht]; ring⟩
  set σ : 𝓞 K := (t : 𝓞 K) + (k : 𝓞 K) * π with hσ
  have hσmem : σ ∉ 𝔪 := by
    intro h
    have : (t : 𝓞 K) ∈ 𝔪 := by
      have : (t : 𝓞 K) = σ - (k : 𝓞 K) * π := by rw [hσ]; ring
      rw [this]
      exact Submodule.sub_mem _ h (Ideal.mul_mem_left _ _ hπmem)
    exact hpt ((intCast_mem_iff_dvd h𝔪 hpmem t).mp this)
  -- the span identity `(π)^2 (S) = (p) (σ)`
  have helt : π ^ 2 * S = -((p : 𝓞 K) * σ) := by
    rw [hrel, hσ, ht, hk]
    push_cast
    ring
  have hspan : Ideal.span {π} ^ 2 * Ideal.span {S} =
      Ideal.span {(p : 𝓞 K)} * Ideal.span {σ} := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton,
      Ideal.span_singleton_mul_span_singleton, helt, Ideal.span_singleton_neg]
  -- extract exact multiplicities
  have hpne : (p : 𝓞 K) ≠ 0 := by
    exact_mod_cast hp.out.ne_zero
  obtain ⟨w, hw⟩ := exists_emultiplicity_span_singleton_eq h𝔪prime hπne
  obtain ⟨e, he⟩ := exists_emultiplicity_span_singleton_eq h𝔪prime hpne
  -- `e = 2 w`
  have hmulS : emultiplicity 𝔪 (Ideal.span {S}) = 0 :=
    emultiplicity_eq_zero.mpr (fun h => hSmem (Ideal.dvd_span_singleton.mp h))
  have hmulσ : emultiplicity 𝔪 (Ideal.span {σ}) = 0 :=
    emultiplicity_eq_zero.mpr (fun h => hσmem (Ideal.dvd_span_singleton.mp h))
  have he2w : e = 2 * w := by
    have h1 := congrArg (emultiplicity 𝔪) hspan
    rw [emultiplicity_mul h𝔪prime, emultiplicity_mul h𝔪prime, emultiplicity_pow h𝔪prime,
      hw, he, hmulS, hmulσ, add_zero, add_zero] at h1
    exact_mod_cast h1.symm
  have hw1 : 1 ≤ w := by
    have : 𝔪 ^ 1 ∣ Ideal.span {π} := by
      rw [pow_one]
      exact Ideal.dvd_span_singleton.mpr hπmem
    have := pow_dvd_iff_le_emultiplicity.mp this
    rw [hw] at this
    exact_mod_cast this
  -- `f'(θ) ∉ 𝔪 ^ (w + 1)`
  have hπT : ¬ 𝔪 ^ (w + 1) ∣ Ideal.span {π * T} := by
    intro hdvd
    rw [← Ideal.span_singleton_mul_span_singleton] at hdvd
    have h1 : ¬𝔪 ∣ Ideal.span {T} := fun h => hTmem (Ideal.dvd_span_singleton.mp h)
    have h2 : 𝔪 ^ (w + 1) ∣ Ideal.span {π} :=
      h𝔪prime.pow_dvd_of_dvd_mul_right _ h1 hdvd
    have := pow_dvd_iff_le_emultiplicity.mp h2
    rw [hw] at this
    exact absurd (by exact_mod_cast this) (by omega)
  have hppow : (p : 𝓞 K) ∈ 𝔪 ^ (w + 1) := by
    have h1 : 𝔪 ^ e ∣ Ideal.span {(p : 𝓞 K)} :=
      pow_dvd_of_le_emultiplicity (le_of_eq he.symm)
    have h2 : (p : 𝓞 K) ∈ 𝔪 ^ e := Ideal.dvd_span_singleton.mp h1
    exact Ideal.pow_le_pow_right (by omega) h2
  have hf'not : aeval θ (derivative f) ∉ 𝔪 ^ (w + 1) := by
    intro hmem
    apply hπT
    rw [Ideal.dvd_span_singleton]
    have hπTeq : π * T = aeval θ (derivative f) - ((p : 𝓞 K) * (k : 𝓞 K)) := by
      rw [hrel', hk]
      push_cast
      ring
    rw [hπTeq]
    exact Submodule.sub_mem _ hmem (Ideal.mul_mem_right _ _ hppow)
  -- the conductor–different identity forces `f'(θ) ∈ 𝔪 ^ (w + 1)`, a contradiction
  have hcondmul := conductor_mul_differentIdeal ℤ ℚ K θ hθ
  have h𝔡 : 𝔪 ^ (e - 1) ∣ differentIdeal ℤ (𝓞 K) := by
    refine pow_sub_one_dvd_differentIdeal ℤ (p := Ideal.span {(p : ℤ)}) 𝔪 e ?_ ?_
    · rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hp.out.ne_zero
    · rw [Ideal.map_span]
      have : (algebraMap ℤ (𝓞 K)) '' {((p : ℕ) : ℤ)} = {((p : ℕ) : 𝓞 K)} := by
        simp
      rw [this]
      exact pow_dvd_of_le_emultiplicity (le_of_eq he.symm)
  have hcm : 𝔪 ∣ conductor ℤ θ := Ideal.dvd_iff_le.mpr hcond
  have hfinal : 𝔪 ^ e ∣ Ideal.span {aeval θ (derivative f)} := by
    have h1 : 𝔪 ^ (1 + (e - 1)) ∣ conductor ℤ θ * differentIdeal ℤ (𝓞 K) := by
      rw [pow_add, pow_one]
      exact mul_dvd_mul hcm h𝔡
    rw [hcondmul, show 1 + (e - 1) = e by omega] at h1
    exact h1
  have : aeval θ (derivative f) ∈ 𝔪 ^ (w + 1) :=
    Ideal.pow_le_pow_right (by omega) (Ideal.dvd_span_singleton.mp hfinal)
  exact hf'not this

end RingOfIntegers
