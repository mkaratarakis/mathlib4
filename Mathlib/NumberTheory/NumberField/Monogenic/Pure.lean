/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.Monogenic.DoubleRoot

/-!
# Monogenicity of pure fields `ℚ(c ^ (1/n))`

Let `f = X ^ n - c ∈ ℤ[X]` be irreducible and let `θ` be a root of `f` generating the
number field `K`.  This file proves the criterion of Jhorar and Khanduja [jhorarkhanduja2016]
(Corollary 1.3 of [jakharkaurkumar2023]) for `ℤ[θ]` to be the full ring of integers of `K`,
prime by prime:

* `RingOfIntegers.dvd_exponent_of_sq_factor`: the generalized obstruction lemma: if
  `f = h ^ 2 * g + p * (k * h) + p ^ 2 * t` with `h * g` monic of degree `< deg f`, then `p`
  divides the exponent of `θ`.  This extends the double-root criterion
  `RingOfIntegers.dvd_exponent_of_sq_dvd_eval` (the case `h = X - r`) to repeated *factors*,
  as needed for pure polynomials, whose repeated factors mod `p` have wild multiplicity `p ^ r`
  and are in general nonlinear.

* `NumberField.Pure.key_identity`: for `h = X ^ m - C c` and `n = p ^ r * m`,
  `X ^ n - C c = h ^ p ^ r + p * (h * T) + C (c ^ p ^ r - c)`; the arithmetic of the criterion
  is entirely carried by the constant `c ^ p ^ r - c`.

* `NumberField.Pure.dvd_exponent_iff_of_dvd` (`p ∣ c`): `p ∣ [𝓞 K : ℤ[θ]]` iff `p ^ 2 ∣ c`.
* `NumberField.Pure.not_dvd_exponent_of_not_dvd` (`p ∤ n * c`): `ℤ[θ]` is `p`-maximal.
* `NumberField.Pure.dvd_exponent_of_sq_dvd` (`p ∣ n`): if `p ^ 2 ∣ c ^ p ^ r - c` then
  `p ∣ [𝓞 K : ℤ[θ]]`.
* `NumberField.Pure.not_dvd_exponent_of_sq_not_dvd` (`n = p ^ r`): if
  `p ^ 2 ∤ c ^ p ^ r - c` then `ℤ[θ]` is `p`-maximal, by Eisenstein's criterion applied to the
  minimal polynomial `(X + c) ^ p ^ r - c` of `θ - c`.
* `NumberField.Pure.not_dvd_exponent_of_sq_not_dvd_of_not_dvd` (general degree
  `n = p ^ r * m`, `p ∤ m`, `p ∤ c`): the tower step.  The wild part of the extension is
  confined to the subfield `M = ℚ(θ ^ m)`, of degree `p ^ r`, where the previous result
  applies to `θ ^ m`; the conductor–different identity over the base `𝓞 M` shows that
  `m θ ^ (m - 1)` lies in the conductor of `𝓞 M[θ]`, and multiplying it by the comaximality
  certificate coming from `M` produces an element of `conductor ℤ θ` avoiding every maximal
  ideal above `p`.

These combine into the full criterion `NumberField.Pure.monogenic_iff`
(**the Jhorar–Khanduja criterion**, Corollary 1.3 of [jakharkaurkumar2023]):  `ℤ[θ] = 𝓞 K`
iff `c` is squarefree and `p ^ 2 ∤ c ^ p ^ r - c` whenever `p ^ r` is the exact power of a
prime `p` dividing `n` with `p ∤ c`; together with the per-prime index criteria
`NumberField.Pure.dvd_exponent_iff_prime_pow` (`n = p ^ r`, uniform in `p ∣ c`) and
`NumberField.Pure.dvd_exponent_iff_of_not_dvd` (general `n`).

## References

* [B. Jhorar, S. K. Khanduja, *When is `R[θ]` integrally closed?*,
  J. Algebra Appl. (2016)][jhorarkhanduja2016]
* [A. Jakhar, S. Kaur, S. Kumar, *On power basis of a class of number fields*,
  arXiv:2303.03138 (2023)][jakharkaurkumar2023]
-/

@[expose] public section

noncomputable section

open Polynomial NumberField Ideal

/-! ### The generalized obstruction lemma -/

namespace RingOfIntegers

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {p : ℕ} [hp : Fact p.Prime]

/-- The obstruction element attached to a decomposition
`f = h ^ 2 * g + p * (k * h) + p ^ 2 * t` of the minimal polynomial `f` of `θ`, where `h * g`
is monic of degree `< deg f`: the algebraic integer `z = h(θ) * g(θ) / p` satisfies
`p * z ∈ ℤ[θ]` but `z ∉ ℤ[θ]`. -/
private theorem exists_mul_mem_adjoin_notMem_adjoin_of_factor {h g k t : ℤ[X]}
    (hW : (h * g).Monic) (hdeg : (h * g).natDegree < (minpoly ℤ θ).natDegree)
    (hfeq : minpoly ℤ θ = h ^ 2 * g + C (p : ℤ) * (k * h) + C (p : ℤ) ^ 2 * t) :
    ∃ z : 𝓞 K, (p : 𝓞 K) * z ∈ Algebra.adjoin ℤ {θ} ∧ z ∉ Algebra.adjoin ℤ {θ} := by
  set f : ℤ[X] := minpoly ℤ θ with hf
  set π : 𝓞 K := aeval θ h with hπ
  set S : 𝓞 K := aeval θ g with hS
  set kθ : 𝓞 K := aeval θ k with hk
  set tθ : 𝓞 K := aeval θ t with ht
  -- the fundamental relation `π ^ 2 S + p kθ π + p ^ 2 tθ = 0` in `𝓞 K`
  have hrel : π ^ 2 * S + (p : 𝓞 K) * (kθ * π) + (p : 𝓞 K) ^ 2 * tθ = 0 := by
    have h1 : aeval θ f = 0 := hf ▸ minpoly.aeval ℤ θ
    rw [hfeq] at h1
    simp only [map_add, map_mul, map_pow, map_natCast] at h1
    rw [hπ, hS, hk, ht]
    linear_combination h1
  -- `y = π * S` satisfies the monic quadratic `y ^ 2 + p kθ y + p ^ 2 tθ S = 0`
  set y : 𝓞 K := π * S with hydef
  have hy : y ^ 2 + ((p : 𝓞 K) * kθ) * y + ((p : 𝓞 K) ^ 2 * tθ) * S = 0 := by
    rw [hydef]
    linear_combination S * hrel
  -- hence `z = y / p ∈ K` is integral over `𝓞 K`, so `y = p * z'` with `z' : 𝓞 K`
  have hpK : ((p : ℕ) : K) ≠ 0 := by
    exact_mod_cast hp.out.ne_zero
  set z : K := algebraMap (𝓞 K) K y / p with hz
  have hzy : (p : K) * z = algebraMap (𝓞 K) K y := by
    rw [hz]; field_simp
  have hzint : IsIntegral (𝓞 K) z := by
    refine ⟨X ^ 2 + (C kθ * X + C (tθ * S)), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_add
        (lt_of_le_of_lt Polynomial.degree_linear_le (by norm_num))
    · simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]
      have hyK := congrArg (algebraMap (𝓞 K) K) hy
      simp only [map_add, map_mul, map_pow, map_zero, map_natCast] at hyK
      rw [← hzy] at hyK
      have hp2 : ((p : K)) ^ 2 ≠ 0 := pow_ne_zero _ hpK
      have hgoal : (p : K) ^ 2 *
          (z ^ 2 + (algebraMap (𝓞 K) K kθ * z +
            algebraMap (𝓞 K) K tθ * algebraMap (𝓞 K) K S)) = 0 := by
        linear_combination hyK
      have := (mul_eq_zero.mp hgoal).resolve_left hp2
      rw [map_mul]
      linear_combination this
  have hzint' : IsIntegral ℤ z := isIntegral_trans z hzint
  obtain ⟨z', hz'⟩ := IsIntegralClosure.isIntegral_iff (A := 𝓞 K) |>.mp hzint'
  have hpz' : (p : 𝓞 K) * z' = y := by
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    rw [map_mul, hz', map_natCast, hzy]
  refine ⟨z', ?_, ?_⟩
  · -- `p * z' = h(θ) g(θ)` visibly lies in `ℤ[θ]`
    rw [hpz', hydef, hπ, hS]
    exact mul_mem (Polynomial.aeval_mem_adjoin_singleton ℤ θ)
      (Polynomial.aeval_mem_adjoin_singleton ℤ θ)
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
  -- the polynomial `W = h * g` is monic of degree `< deg f` and `W(θ) = π S = p c'(θ)`
  set W : ℤ[X] := h * g with hWdef
  have haevalW : aeval θ W = y := by
    rw [hWdef, map_mul, hydef, hπ, hS]
  -- `W - p c'` annihilates `θ` and has degree `< deg f`, so it vanishes
  have hann : aeval θ (W - C (p : ℤ) * c') = 0 := by
    rw [map_sub, haevalW, map_mul, aeval_C, haevalc', ← hpz', algebraMap_int_eq, eq_intCast,
      Int.cast_natCast]
    ring
  have hfne : f ≠ 0 := minpoly.ne_zero θ.isIntegral
  have hdegW : W.degree < f.degree := by
    rw [Polynomial.degree_eq_natDegree hW.ne_zero, Polynomial.degree_eq_natDegree hfne]
    exact_mod_cast hdeg
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
    rwa [hW.leadingCoeff, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C] at this
  have : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos (Dvd.intro _ hlead.symm)
  have h2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.out.two_le
  omega

/-- **The generalized obstruction lemma.**  Let `f` be the minimal polynomial of `θ : 𝓞 K` and
`p` a rational prime.  If `f = h ^ 2 * g + p * (k * h) + p ^ 2 * t` for polynomials
`h, g, k, t ∈ ℤ[X]` with `h * g` monic of degree `< deg f`, then `p` divides the exponent of
`θ` (the index `[𝓞 K : ℤ[θ]]` in the sense of `RingOfIntegers.exponent`): the algebraic
integer `h(θ) * g(θ) / p` witnesses the failure of `p`-maximality.

The double-root criterion `RingOfIntegers.dvd_exponent_of_sq_dvd_eval` is the special case
`h = X - r`, `g` the second Taylor remainder of `f` at `r`. -/
theorem dvd_exponent_of_sq_factor {h g k t : ℤ[X]}
    (hW : (h * g).Monic) (hdeg : (h * g).natDegree < (minpoly ℤ θ).natDegree)
    (hfeq : minpoly ℤ θ = h ^ 2 * g + C (p : ℤ) * (k * h) + C (p : ℤ) ^ 2 * t) :
    p ∣ exponent θ := by
  obtain ⟨z, hpz, hz⟩ := exists_mul_mem_adjoin_notMem_adjoin_of_factor hW hdeg hfeq
  by_contra hpe
  have hpZ : ¬(p : ℤ) ∣ ((exponent θ : ℕ) : ℤ) := fun h =>
    hpe (Int.natCast_dvd_natCast.mp h)
  obtain ⟨u, v, huv⟩ : IsCoprime ((p : ℤ)) ((exponent θ : ℤ)) :=
    (Nat.prime_iff_prime_int.mp hp.out).coprime_iff_not_dvd.mpr hpZ
  have hEmem : ((exponent θ : 𝓞 K)) ∈ conductor ℤ θ := Int.absNorm_under_mem (conductor ℤ θ)
  have hez : ((exponent θ : 𝓞 K)) * z ∈ Algebra.adjoin ℤ {θ} := mem_conductor_iff.mp hEmem z
  apply hz
  have hzeq : z = (u : 𝓞 K) * ((p : 𝓞 K) * z) + (v : 𝓞 K) * ((exponent θ : 𝓞 K) * z) := by
    have h := congrArg (fun t : ℤ => ((t : ℤ) : 𝓞 K)) huv
    push_cast at h
    linear_combination -z * h
  rw [hzeq]
  exact add_mem (mul_mem (Subalgebra.intCast_mem _ u) hpz)
    (mul_mem (Subalgebra.intCast_mem _ v) hez)

end RingOfIntegers

/-! ### The key identity for pure polynomials -/

namespace NumberField.Pure

/-- **The key identity.**  For `h = X ^ m - C c` and any `r`, there is `T : ℤ[X]` with
`X ^ (p ^ r * m) - C c = h ^ p ^ r + p * (h * T) + C (c ^ p ^ r - c)`.
Modulo `p` this is the Frobenius identity `X ^ n - c = (X ^ m - c) ^ p ^ r`; the criterion
for monogenicity is carried by the integer constant `c ^ p ^ r - c`. -/
theorem key_identity (p : ℕ) [hp : Fact p.Prime] (r : ℕ) {m : ℕ} (hm : m ≠ 0) (c : ℤ) :
    ∃ T : ℤ[X], (X ^ (p ^ r * m) - C c : ℤ[X]) =
      (X ^ m - C c) ^ p ^ r + C (p : ℤ) * ((X ^ m - C c) * T) + C (c ^ p ^ r - c) := by
  set h : ℤ[X] := X ^ m - C c with hh
  have hhm : h.Monic := monic_X_pow_sub_C _ hm
  -- `h` divides `E := X ^ (p ^ r * m) - C (c ^ p ^ r) - h ^ p ^ r`
  have hdvd : h ∣ X ^ (p ^ r * m) - C (c ^ p ^ r) - h ^ p ^ r := by
    refine dvd_sub ?_ (dvd_pow_self h (pow_ne_zero r hp.out.ne_zero))
    have h1 := sub_dvd_pow_sub_pow (X ^ m : ℤ[X]) (C c) (p ^ r)
    rwa [← pow_mul, mul_comm m, ← map_pow] at h1
  obtain ⟨V, hV⟩ := hdvd
  -- modulo `p`, `E` vanishes by Frobenius, hence `p` divides `V`
  have hmapE : (X ^ (p ^ r * m) - C (c ^ p ^ r) - h ^ p ^ r).map
      (Int.castRingHom (ZMod p)) = 0 := by
    have hfrob : ((X : (ZMod p)[X]) ^ m - C ((c : ZMod p))) ^ p ^ r =
        X ^ (p ^ r * m) - C ((c : ZMod p) ^ p ^ r) := by
      rw [sub_pow_char_pow, ← pow_mul, mul_comm m, ← map_pow]
    simp only [hh, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      Int.coe_castRingHom, map_pow]
    rw [hfrob, map_pow]
    ring
  have hpV : C (p : ℤ) ∣ V := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    have hVmap : V.map (Int.castRingHom (ZMod p)) = 0 := by
      have h2 : h.map (Int.castRingHom (ZMod p)) * V.map (Int.castRingHom (ZMod p)) = 0 := by
        rw [← Polynomial.map_mul, ← hV, hmapE]
      exact (mul_eq_zero.mp h2).resolve_left (hhm.map _).ne_zero
    have h3 := congrArg (fun q : (ZMod p)[X] => q.coeff i) hVmap
    simp only [Polynomial.coeff_map, Int.coe_castRingHom, Polynomial.coeff_zero] at h3
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h3
  obtain ⟨T, hT⟩ := hpV
  refine ⟨T, ?_⟩
  have hE : X ^ (p ^ r * m) - C (c ^ p ^ r) - h ^ p ^ r = C (p : ℤ) * (h * T) := by
    rw [hV, hT]; ring
  rw [Polynomial.C_sub]
  linear_combination hE

/-! ### Elementary integer and polynomial lemmas -/

variable {p : ℕ} [hp : Fact p.Prime] {c : ℤ} {r : ℕ}

/-- Fermat: `p ∣ c ^ p ^ r - c`. -/
private theorem dvd_pow_pow_sub (r : ℕ) (c : ℤ) : (p : ℤ) ∣ c ^ p ^ r - c := by
  have h : ((c ^ p ^ r - c : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [ZMod.pow_card_pow]
    ring
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h

/-- `X ^ n - C c` is Eisenstein at `q` when `q ∣ c` and `q ^ 2 ∤ c`. -/
private theorem isEisensteinAt_pure {q : ℤ} (hq : Prime q) {n : ℕ} (hn : n ≠ 0)
    (hqc : q ∣ c) (hqc2 : ¬q ^ 2 ∣ c) :
    (X ^ n - C c : ℤ[X]).IsEisensteinAt (Submodule.span ℤ {q}) :=
  (monic_X_pow_sub_C c hn).isEisensteinAt_of_mem_of_notMem
    (fun h => hq.not_unit (isUnit_of_dvd_one
      (Ideal.mem_span_singleton.mp ((Ideal.eq_top_iff_one _).mp h))))
    (fun {i} hi => by
      rw [natDegree_X_pow_sub_C] at hi
      rw [coeff_sub, coeff_X_pow, if_neg (by omega), coeff_C, Ideal.mem_span_singleton]
      split_ifs with h
      · simpa using hqc.neg_right
      · simp)
    (by
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, coeff_sub, coeff_X_pow,
        if_neg (by omega), coeff_C, if_pos rfl, zero_sub]
      intro h
      exact hqc2 (dvd_neg.mp h))

/-- The translated pure polynomial `(X + C c) ^ p ^ r - C c` is Eisenstein at `p` as soon as
`p ^ 2 ∤ c ^ p ^ r - c`: the middle binomial coefficients are divisible by `p`, and the
constant term is exactly `c ^ p ^ r - c`. -/
private theorem isEisensteinAt_translate
    (hpc2 : ¬(p : ℤ) ^ 2 ∣ c ^ p ^ r - c) :
    ((X + C c) ^ p ^ r - C c : ℤ[X]).IsEisensteinAt (Submodule.span ℤ {(p : ℤ)}) := by
  have hn0 : p ^ r ≠ 0 := pow_ne_zero r hp.out.ne_zero
  have hcompeq : ((X ^ p ^ r - C c : ℤ[X]).comp (X + C c)) = (X + C c) ^ p ^ r - C c := by
    simp [sub_comp, pow_comp, X_comp]
  have hmonic : ((X + C c) ^ p ^ r - C c : ℤ[X]).Monic := by
    rw [← hcompeq]
    exact (monic_X_pow_sub_C c hn0).comp_X_add_C c
  have hdeg : ((X + C c) ^ p ^ r - C c : ℤ[X]).natDegree = p ^ r := by
    rw [natDegree_sub_C, natDegree_pow, natDegree_X_add_C, mul_one]
  refine hmonic.isEisensteinAt_of_mem_of_notMem
    (fun h => (Nat.prime_iff_prime_int.mp hp.out).not_unit (isUnit_of_dvd_one
      (Ideal.mem_span_singleton.mp ((Ideal.eq_top_iff_one _).mp h))))
    (fun {i} hi => ?_) ?_
  · rw [hdeg] at hi
    rw [coeff_sub, coeff_X_add_C_pow, coeff_C, Ideal.mem_span_singleton]
    rcases eq_or_ne i 0 with rfl | h0
    · rw [if_pos rfl]
      simpa using dvd_pow_pow_sub r c
    · rw [if_neg h0]
      have hch : (p : ℤ) ∣ ((p ^ r).choose i : ℤ) :=
        Int.natCast_dvd_natCast.mpr (Nat.Prime.dvd_choose_pow hp.out h0 (by omega))
      simpa using hch.mul_left (c ^ (p ^ r - i))
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, coeff_sub, coeff_X_add_C_pow,
      coeff_C, if_pos rfl]
    simpa using hpc2

/-! ### Translation by `c` -/

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}

omit [NumberField K] in
private theorem adjoin_int_sub_intCast (x : 𝓞 K) (c : ℤ) :
    Algebra.adjoin ℤ {x - (c : 𝓞 K)} = Algebra.adjoin ℤ {x} := by
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    exact sub_mem (Algebra.self_mem_adjoin_singleton ℤ x) (Subalgebra.intCast_mem _ c)
  · rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    have h := add_mem (Algebra.self_mem_adjoin_singleton ℤ (x - (c : 𝓞 K)))
      (Subalgebra.intCast_mem (Algebra.adjoin ℤ {x - (c : 𝓞 K)}) c)
    simpa using h

private theorem adjoin_rat_sub_intCast (x : K) (c : ℤ) :
    Algebra.adjoin ℚ {x - (c : K)} = Algebra.adjoin ℚ {x} := by
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    exact sub_mem (Algebra.self_mem_adjoin_singleton ℚ x) (Subalgebra.intCast_mem _ c)
  · rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    have h := add_mem (Algebra.self_mem_adjoin_singleton ℚ (x - (c : K)))
      (Subalgebra.intCast_mem (Algebra.adjoin ℚ {x - (c : K)}) c)
    simpa using h

omit [NumberField K] in
/-- The exponent is invariant under translating the generator by an integer. -/
private theorem exponent_sub_intCast (θ : 𝓞 K) (c : ℤ) :
    RingOfIntegers.exponent (θ - (c : 𝓞 K)) = RingOfIntegers.exponent θ := by
  have hcond : conductor ℤ (θ - (c : 𝓞 K)) = conductor ℤ θ := by
    ext a
    simp only [mem_conductor_iff, adjoin_int_sub_intCast]
  unfold RingOfIntegers.exponent
  rw [hcond]

/-- The minimal polynomial of `θ - c`, computed from that of `θ` by translation. -/
private theorem minpoly_sub_intCast {n : ℕ} (hn : n ≠ 0)
    (hθ : minpoly ℤ θ = X ^ n - C c) :
    minpoly ℤ (θ - (c : 𝓞 K)) = (X + C c) ^ n - C c := by
  set G : ℤ[X] := minpoly ℤ (θ - (c : 𝓞 K)) with hG
  have hcompeq : ((X ^ n - C c : ℤ[X]).comp (X + C c)) = (X + C c) ^ n - C c := by
    simp [sub_comp, pow_comp, X_comp]
  have hFmonic : ((X + C c) ^ n - C c : ℤ[X]).Monic := by
    rw [← hcompeq]
    exact (monic_X_pow_sub_C c hn).comp_X_add_C c
  -- `F` kills `θ - c`
  have hFroot : aeval (θ - (c : 𝓞 K)) ((X + C c) ^ n - C c : ℤ[X]) = 0 := by
    have h := minpoly.aeval ℤ θ
    rw [hθ] at h
    simp only [map_sub, map_pow, map_add, aeval_X, eq_intCast, map_intCast] at h ⊢
    rw [sub_add_cancel]
    exact h
  have hdvd : G ∣ (X + C c) ^ n - C c :=
    minpoly.isIntegrallyClosed_dvd (θ - (c : 𝓞 K)).isIntegral hFroot
  -- conversely, `G.comp (X - C c)` kills `θ`, so `n ≤ deg G`
  have hGcomp : aeval θ (G.comp (X - C c)) = 0 := by
    rw [aeval_comp]
    have h1 : aeval θ (X - C c : ℤ[X]) = θ - (c : 𝓞 K) := by
      simp
    rw [h1, hG]
    exact minpoly.aeval ℤ _
  have hGmonic : G.Monic := minpoly.monic (θ - (c : 𝓞 K)).isIntegral
  have hdvd2 : minpoly ℤ θ ∣ G.comp (X - C c) :=
    minpoly.isIntegrallyClosed_dvd θ.isIntegral hGcomp
  have hle : n ≤ G.natDegree := by
    have h2 := Polynomial.natDegree_le_of_dvd hdvd2 (hGmonic.comp_X_sub_C c).ne_zero
    rw [hθ, natDegree_X_pow_sub_C, natDegree_comp, natDegree_X_sub_C, mul_one] at h2
    exact h2
  have hdegF : ((X + C c) ^ n - C c : ℤ[X]).natDegree = n := by
    rw [natDegree_sub_C, natDegree_pow, natDegree_X_add_C, mul_one]
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hGmonic hFmonic hdvd
    (le_trans hdegF.le hle)).symm

/-! ### The per-prime criterion -/

variable {n : ℕ}

/-- **At a prime dividing `c`**: `p` divides the index `[𝓞 K : ℤ[θ]]` if and only if
`p ^ 2 ∣ c`.  Sufficiency is Eisenstein's criterion; necessity is the double-root criterion
at `r = 0`. -/
theorem dvd_exponent_iff_of_dvd (hn : 2 ≤ n) (hpc : (p : ℤ) ∣ c)
    (hθ : minpoly ℤ θ = X ^ n - C c) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    p ∣ RingOfIntegers.exponent θ ↔ (p : ℤ) ^ 2 ∣ c := by
  constructor
  · intro hdvd
    by_contra hc2
    exact RingOfIntegers.not_dvd_exponent_of_minpoly_isEisensteinAt hgen
      (hθ ▸ isEisensteinAt_pure (Nat.prime_iff_prime_int.mp hp.out)
        (by omega : n ≠ 0) hpc hc2) hdvd
  · intro hc2
    refine RingOfIntegers.dvd_exponent_of_sq_dvd_eval (r := 0) ?_ ?_ ?_
    · rw [hθ, natDegree_X_pow_sub_C]
      exact hn
    · rw [hθ]
      simp only [eval_sub, eval_pow, eval_X, eval_C, zero_pow (show n ≠ 0 by omega), zero_sub]
      exact hc2.neg_right
    · rw [hθ]
      simp only [derivative_sub, derivative_C, sub_zero, derivative_X_pow, eval_mul, eval_C,
        eval_pow, eval_X]
      rw [zero_pow (show n - 1 ≠ 0 by omega), mul_zero]
      exact dvd_zero _

/-- **At a prime dividing neither `n` nor `c`**, `ℤ[θ]` is `p`-maximal: a maximal ideal
containing the conductor and `p` would contain `f'(θ) = n θ ^ (n - 1)`, hence `n` or
`c = θ ^ n`. -/
theorem not_dvd_exponent_of_not_dvd (hn : n ≠ 0) (hpn : ¬(p : ℤ) ∣ (n : ℤ))
    (hpc : ¬(p : ℤ) ∣ c) (hθ : minpoly ℤ θ = X ^ n - C c)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    ¬p ∣ RingOfIntegers.exponent θ := by
  rw [RingOfIntegers.not_dvd_exponent_iff_conductor_sup_span_eq_top]
  by_contra hsup
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hsup
  have hcond : conductor ℤ θ ≤ 𝔪 := le_trans le_sup_left hle
  have hp𝔪 : (p : 𝓞 K) ∈ 𝔪 := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hf' : aeval θ (derivative (minpoly ℤ θ)) ∈ 𝔪 :=
    hcond (RingOfIntegers.aeval_derivative_minpoly_mem_conductor hgen)
  have hder : aeval θ (derivative (minpoly ℤ θ)) = (n : 𝓞 K) * θ ^ (n - 1) := by
    rw [hθ]
    simp only [derivative_sub, derivative_C, sub_zero, derivative_X_pow, map_mul, map_pow,
      aeval_X, map_natCast]
  rw [hder] at hf'
  rcases h𝔪.isPrime.mem_or_mem hf' with h1 | h1
  · refine hpn ((RingOfIntegers.intCast_mem_iff_dvd h𝔪 hp𝔪 (n : ℤ)).mp ?_)
    rw [Int.cast_natCast]
    exact h1
  · have hθ𝔪 : θ ∈ 𝔪 := h𝔪.isPrime.mem_of_pow_mem _ h1
    have hc𝔪 : ((c : ℤ) : 𝓞 K) ∈ 𝔪 := by
      have hroot := minpoly.aeval ℤ θ
      rw [hθ] at hroot
      simp only [map_sub, map_pow, aeval_X, eq_intCast, map_intCast] at hroot
      have h3 : ((c : ℤ) : 𝓞 K) = θ ^ n := by linear_combination -hroot
      rw [h3]
      exact Ideal.pow_mem_of_mem _ hθ𝔪 _ (by omega)
    exact hpc ((RingOfIntegers.intCast_mem_iff_dvd h𝔪 hp𝔪 c).mp hc𝔪)

/-- **Necessity at a wild prime.**  If `p ^ r ∣ n` with `r ≥ 1` and
`p ^ 2 ∣ c ^ p ^ r - c`, then `p` divides the index: the key identity turns the hypothesis
into a decomposition `f = h ^ 2 g + p k h + p ^ 2 t` around the repeated factor
`h = X ^ m - c`, and the generalized obstruction lemma applies. -/
theorem dvd_exponent_of_sq_dvd {m : ℕ} (hr : 1 ≤ r) (hm : m ≠ 0)
    (hc2 : (p : ℤ) ^ 2 ∣ c ^ p ^ r - c)
    (hθ : minpoly ℤ θ = X ^ (p ^ r * m) - C c) :
    p ∣ RingOfIntegers.exponent θ := by
  obtain ⟨T, hT⟩ := key_identity p r hm c
  obtain ⟨t₀, ht₀⟩ := hc2
  have h2 : 2 ≤ p ^ r := by
    calc 2 ≤ p := hp.out.two_le
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ r := Nat.pow_le_pow_right hp.out.one_lt.le hr
  have hhm : (X ^ m - C c : ℤ[X]).Monic := monic_X_pow_sub_C c hm
  have hsplit : (X ^ m - C c : ℤ[X]) ^ p ^ r
      = (X ^ m - C c) ^ 2 * (X ^ m - C c) ^ (p ^ r - 2) := by
    rw [← pow_add]
    congr 1
    omega
  refine RingOfIntegers.dvd_exponent_of_sq_factor
    (h := X ^ m - C c) (g := (X ^ m - C c) ^ (p ^ r - 2)) (k := T) (t := C t₀) ?_ ?_ ?_
  · exact hhm.mul (hhm.pow _)
  · rw [hθ, natDegree_X_pow_sub_C, hhm.natDegree_mul (hhm.pow _), natDegree_pow,
      natDegree_X_pow_sub_C]
    obtain ⟨a, ha⟩ : ∃ a, p ^ r = a + 2 := ⟨p ^ r - 2, by omega⟩
    rw [ha]
    have hm1 : 0 < m := Nat.pos_of_ne_zero hm
    simp only [Nat.add_sub_cancel]
    nlinarith [hm1]
  · rw [hθ, hT, ht₀, hsplit, map_mul, map_pow]
    ring

/-- **Sufficiency at the wild prime, for prime-power degree** `n = p ^ r`: if
`p ^ 2 ∤ c ^ p ^ r - c`, then `ℤ[θ]` is `p`-maximal.  The whole wildness is absorbed by a
translation: the minimal polynomial `(X + c) ^ p ^ r - c` of `θ - c` is Eisenstein at `p`,
its constant term being exactly `c ^ p ^ r - c`. -/
theorem not_dvd_exponent_of_sq_not_dvd
    (hc2 : ¬(p : ℤ) ^ 2 ∣ c ^ p ^ r - c)
    (hθ : minpoly ℤ θ = X ^ p ^ r - C c) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    ¬p ∣ RingOfIntegers.exponent θ := by
  rw [← exponent_sub_intCast θ c]
  have hgen' : Algebra.adjoin ℚ {((θ - (c : 𝓞 K) : 𝓞 K) : K)} = ⊤ := by
    have hcoe : ((θ - (c : 𝓞 K) : 𝓞 K) : K) = (θ : K) - (c : K) := by
      norm_cast
    rw [hcoe, adjoin_rat_sub_intCast]
    exact hgen
  refine RingOfIntegers.not_dvd_exponent_of_minpoly_isEisensteinAt hgen' ?_
  rw [minpoly_sub_intCast (pow_ne_zero r hp.out.ne_zero) hθ]
  exact isEisensteinAt_translate hc2

/-- **The per-prime criterion at `p`, for prime-power degree** `n = p ^ r`:
`p` divides the index `[𝓞 K : ℤ[θ]]` if and only if `p ^ 2 ∣ c ^ p ^ r - c`.
(This is uniform in `p ∣ c` vs `p ∤ c`.) -/
theorem dvd_exponent_iff_prime_pow (hr : 1 ≤ r)
    (hθ : minpoly ℤ θ = X ^ p ^ r - C c) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    p ∣ RingOfIntegers.exponent θ ↔ (p : ℤ) ^ 2 ∣ c ^ p ^ r - c := by
  constructor
  · intro h
    by_contra hc2
    exact not_dvd_exponent_of_sq_not_dvd hc2 hθ hgen h
  · intro hc2
    exact dvd_exponent_of_sq_dvd hr one_ne_zero hc2 (by rwa [mul_one])

/-! ### General degree: descending along the subfield `ℚ(θ ^ m)`

For `n = p ^ r * m` with `p ∤ m`, the wild part of the extension is confined to the subfield
`M = ℚ(θ ^ m)`, of degree `p ^ r` over `ℚ`, where the prime-power sufficiency applies.  The
passage from `M` back to `K` is governed by the polynomial `X ^ m - θ ^ m`, whose derivative
`m θ ^ (m - 1)` is a unit above `p`: by the conductor–different identity over the base
`𝓞 M`, it lies in the conductor of `𝓞 M[θ]`, and multiplying it by the certificate
`c₀ ≡ 1 mod p` coming from `p`-maximality of `ℤ[θ ^ m]` in `𝓞 M` produces an element of
`conductor ℤ θ` that avoids every maximal ideal above `p`. -/

section Tower

open scoped IntermediateField

/-- Enlarging the base field preserves `Algebra.adjoin _ {x} = ⊤`. -/
private theorem adjoin_intermediateField_eq_top (M : IntermediateField ℚ K) {x : K}
    (h : Algebra.adjoin ℚ {x} = ⊤) : Algebra.adjoin M {x} = ⊤ := by
  have key : ∀ y ∈ Algebra.adjoin ℚ {x}, y ∈ Algebra.adjoin M {x} := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem z hz => exact Algebra.subset_adjoin hz
    | algebraMap q =>
        rw [IsScalarTower.algebraMap_apply ℚ M K q]
        exact Subalgebra.algebraMap_mem _ _
    | add _ _ _ _ h1 h2 => exact add_mem h1 h2
    | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2
  rw [eq_top_iff]
  intro y _
  exact key y (by rw [h]; trivial)

/-- **Sufficiency at the wild prime, general degree** (the tower step).  Let
`θ` have minimal polynomial `X ^ (p ^ r * m) - C c` with `r ≥ 1`, `p ∤ m` and `p ∤ c`, and
generate `K` over `ℚ`.  If `p ^ 2 ∤ c ^ p ^ r - c`, then `ℤ[θ]` is `p`-maximal. -/
theorem not_dvd_exponent_of_sq_not_dvd_of_not_dvd {m : ℕ} (hm : ¬p ∣ m)
    (hpc : ¬(p : ℤ) ∣ c) (hc2 : ¬(p : ℤ) ^ 2 ∣ c ^ p ^ r - c)
    (hθ : minpoly ℤ θ = X ^ (p ^ r * m) - C c)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    ¬p ∣ RingOfIntegers.exponent θ := by
  have hm0 : m ≠ 0 := fun h => hm (h.symm ▸ dvd_zero p)
  have hpr0 : p ^ r ≠ 0 := pow_ne_zero r hp.out.ne_zero
  -- the root relation `θ ^ (p ^ r * m) = c` and the element `μ = θ ^ m`
  have hroot : θ ^ (p ^ r * m) = ((c : ℤ) : 𝓞 K) := by
    have h := minpoly.aeval ℤ θ
    rw [hθ] at h
    simp only [map_sub, map_pow, aeval_X, eq_intCast, map_intCast] at h
    linear_combination h
  have hμc : (θ ^ m) ^ p ^ r = ((c : ℤ) : 𝓞 K) := by
    rw [← pow_mul, mul_comm m]
    exact hroot
  set μK : K := ((θ ^ m : 𝓞 K) : K) with hμK
  set M : IntermediateField ℚ K := ℚ⟮μK⟯ with hM
  have hintμ : IsIntegral ℚ μK := IsIntegral.of_finite ℚ μK
  have hintθ : IsIntegral ℚ ((θ : K)) := IsIntegral.of_finite ℚ _
  have hμKc : μK ^ p ^ r = ((c : ℤ) : K) := by
    have h := congrArg (algebraMap (𝓞 K) K) hμc
    rw [map_pow, map_intCast] at h
    exact h
  -- degrees: `[M : ℚ] = p ^ r` and `[K : M] = m`
  have hfinK : Module.finrank ℚ K = p ^ r * m := by
    have hpb : Module.finrank ℚ K = (minpoly ℚ ((θ : K))).natDegree :=
      (PowerBasis.ofAdjoinEqTop hintθ hgen).finrank
    rw [hpb, minpoly.isIntegrallyClosed_eq_field_fractions ℚ K θ.isIntegral, hθ]
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      natDegree_X_pow_sub_C]
  have hgenM : Algebra.adjoin M {(θ : K)} = ⊤ := adjoin_intermediateField_eq_top M hgen
  have hintθM : IsIntegral M ((θ : K)) := IsIntegral.of_finite M _
  have hfinMK : Module.finrank M K = (minpoly M ((θ : K))).natDegree :=
    (PowerBasis.ofAdjoinEqTop hintθM hgenM).finrank
  -- the generator of `M` as an element of `M`
  set μM : M := ⟨μK, IntermediateField.mem_adjoin_simple_self ℚ μK⟩ with hμM
  have hdvdθM : minpoly M ((θ : K)) ∣ X ^ m - C μM := by
    apply minpoly.dvd
    have hcoe : algebraMap M K μM = μK := rfl
    simp only [map_sub, map_pow, aeval_X, aeval_C, hcoe]
    rw [hμK]
    push_cast
    ring
  have hMK_le : Module.finrank M K ≤ m := by
    rw [hfinMK]
    calc (minpoly M ((θ : K))).natDegree ≤ (X ^ m - C μM : M[X]).natDegree :=
          Polynomial.natDegree_le_of_dvd hdvdθM (monic_X_pow_sub_C μM hm0).ne_zero
      _ = m := natDegree_X_pow_sub_C
  have hdvdμ : minpoly ℚ μK ∣ X ^ p ^ r - C ((c : ℤ) : ℚ) := by
    apply minpoly.dvd
    simp only [map_sub, map_pow, aeval_X, map_intCast]
    rw [hμKc, sub_self]
  have hQM_le : Module.finrank ℚ M ≤ p ^ r := by
    rw [IntermediateField.adjoin.finrank hintμ]
    calc (minpoly ℚ μK).natDegree ≤ (X ^ p ^ r - C ((c : ℤ) : ℚ)).natDegree :=
          Polynomial.natDegree_le_of_dvd hdvdμ (monic_X_pow_sub_C _ hpr0).ne_zero
      _ = p ^ r := natDegree_X_pow_sub_C
  have hprod : Module.finrank ℚ M * Module.finrank M K = p ^ r * m := by
    rw [Module.finrank_mul_finrank, hfinK]
  have hMK : Module.finrank M K = m := by
    by_contra hne
    have hlt : Module.finrank M K < m := lt_of_le_of_ne hMK_le hne
    have h1 : Module.finrank ℚ M * Module.finrank M K < p ^ r * m :=
      lt_of_le_of_lt (Nat.mul_le_mul_right _ hQM_le)
        ((Nat.mul_lt_mul_left (Nat.pos_of_ne_zero hpr0)).mpr hlt)
    omega
  have hQM : Module.finrank ℚ M = p ^ r := by
    rw [hMK] at hprod
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hm0) hprod
  -- minimal polynomials over `M` and over `ℚ`
  have hminθM : minpoly M ((θ : K)) = X ^ m - C μM := by
    refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hintθM)
      (monic_X_pow_sub_C μM hm0) hdvdθM ?_).symm
    rw [natDegree_X_pow_sub_C, ← hfinMK, hMK]
  have hminμ : minpoly ℚ μK = X ^ p ^ r - C ((c : ℤ) : ℚ) := by
    refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hintμ)
      (monic_X_pow_sub_C _ hpr0) hdvdμ ?_).symm
    rw [natDegree_X_pow_sub_C, ← IntermediateField.adjoin.finrank hintμ, hQM]
  -- the generator of `M` as an element of `𝓞 M`
  have hintμM : IsIntegral ℤ μM := by
    rw [← isIntegral_algHom_iff (M.val.restrictScalars ℤ) Subtype.val_injective]
    exact (θ ^ m : 𝓞 K).isIntegral_coe
  set μ' : 𝓞 M := ⟨μM, hintμM⟩ with hμ'
  have hminμ' : minpoly ℤ μ' = X ^ p ^ r - C c := by
    have h1 : minpoly ℚ ((μ' : M)) = (minpoly ℤ μ').map (algebraMap ℤ ℚ) :=
      minpoly.isIntegrallyClosed_eq_field_fractions ℚ M μ'.isIntegral
    have h2 : minpoly ℚ ((μ' : M)) = minpoly ℚ μK :=
      (minpoly.algHom_eq M.val Subtype.val_injective μM).symm
    rw [h2, hminμ] at h1
    apply Polynomial.map_injective (algebraMap ℤ ℚ) (algebraMap ℤ ℚ).injective_int
    rw [← h1, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      eq_intCast]
  -- `μ'` generates `M` over `ℚ`
  have hgenμ : Algebra.adjoin ℚ {((μ' : 𝓞 M) : M)} = ⊤ := by
    have hgen' := (IntermediateField.adjoin.powerBasis hintμ).adjoin_gen_eq_top
    rwa [show (IntermediateField.adjoin.powerBasis hintμ).gen = μM from rfl] at hgen'
  -- Step A: `ℤ[μ']` is `p`-maximal in `𝓞 M`
  have hstepA : ¬p ∣ RingOfIntegers.exponent μ' :=
    not_dvd_exponent_of_sq_not_dvd hc2 hminμ' hgenμ
  rw [RingOfIntegers.not_dvd_exponent_iff_conductor_sup_span_eq_top] at hstepA
  have h1M : (1 : 𝓞 M) ∈ conductor ℤ μ' ⊔ Ideal.span {(p : 𝓞 M)} := by
    rw [hstepA]; trivial
  obtain ⟨c₀, hc₀, v, hv, hcv⟩ := Submodule.mem_sup.mp h1M
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp hv
  -- Euler: `m θ ^ (m - 1)` lies in the conductor of `𝓞 M[θ]`
  have hδcond : aeval θ (derivative (minpoly (𝓞 M) θ)) ∈ conductor (𝓞 M) θ := by
    have h : Ideal.span {aeval θ (derivative (minpoly (𝓞 M) θ))} ≤ conductor (𝓞 M) θ := by
      rw [← conductor_mul_differentIdeal (𝓞 M) M K θ hgenM]
      exact Ideal.mul_le_right
    exact h (Ideal.mem_span_singleton_self _)
  have hminθ𝓞M : minpoly (𝓞 M) θ = X ^ m - C μ' := by
    have h1 : minpoly M ((θ : K)) = (minpoly (𝓞 M) θ).map (algebraMap (𝓞 M) M) :=
      minpoly.isIntegrallyClosed_eq_field_fractions M K (IsIntegral.tower_top θ.isIntegral)
    rw [hminθM] at h1
    apply Polynomial.map_injective (algebraMap (𝓞 M) M) (IsFractionRing.injective (𝓞 M) M)
    rw [← h1, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    rfl
  have hδeq : aeval θ (derivative (minpoly (𝓞 M) θ)) = (m : 𝓞 K) * θ ^ (m - 1) := by
    rw [hminθ𝓞M]
    simp only [derivative_sub, derivative_C, sub_zero, derivative_X_pow, map_mul, map_pow,
      aeval_X, map_natCast]
  rw [hδeq] at hδcond
  -- the image of `ℤ[μ']` in `𝓞 K` lands in `ℤ[θ]`
  have hιμ : algebraMap (𝓞 M) (𝓞 K) μ' = θ ^ m := by
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    rfl
  have himage : ∀ a ∈ Algebra.adjoin ℤ {μ'},
      algebraMap (𝓞 M) (𝓞 K) a ∈ Algebra.adjoin ℤ {θ} := by
    intro a ha
    have h1 : algebraMap (𝓞 M) (𝓞 K) a ∈
        (Algebra.adjoin ℤ {μ'}).map (algebraMap (𝓞 M) (𝓞 K)).toIntAlgHom :=
      ⟨a, ha, rfl⟩
    rw [AlgHom.map_adjoin, Set.image_singleton] at h1
    have h2 : (algebraMap (𝓞 M) (𝓞 K)).toIntAlgHom μ' = θ ^ m := hιμ
    rw [h2] at h1
    have h3 : Algebra.adjoin ℤ ({θ ^ m} : Set (𝓞 K)) ≤ Algebra.adjoin ℤ {θ} := by
      apply Algebra.adjoin_le
      rw [Set.singleton_subset_iff]
      exact pow_mem (Algebra.self_mem_adjoin_singleton ℤ θ) m
    exact h3 h1
  -- the certificate `w = c₀ * m θ ^ (m - 1)` lies in `conductor ℤ θ`
  set w : 𝓞 K := algebraMap (𝓞 M) (𝓞 K) c₀ * ((m : 𝓞 K) * θ ^ (m - 1)) with hw
  have hwcond : w ∈ conductor ℤ θ := by
    rw [mem_conductor_iff]
    intro b
    have hδb : (m : 𝓞 K) * θ ^ (m - 1) * b ∈ Algebra.adjoin (𝓞 M) {θ} :=
      mem_conductor_iff.mp hδcond b
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hδb
    obtain ⟨Q, hQ⟩ := hδb
    replace hQ : aeval θ Q = (m : 𝓞 K) * θ ^ (m - 1) * b := hQ
    have hsum : w * b = ∑ i ∈ Finset.range (Q.natDegree + 1),
        algebraMap (𝓞 M) (𝓞 K) (c₀ * Q.coeff i) * θ ^ i := by
      rw [hw, mul_assoc, ← hQ, Polynomial.aeval_eq_sum_range, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul, mul_assoc]
    rw [hsum]
    exact Subalgebra.sum_mem _ fun i _ => mul_mem
      (himage _ (mem_conductor_iff.mp hc₀ (Q.coeff i)))
      (pow_mem (Algebra.self_mem_adjoin_singleton ℤ θ) i)
  -- conclusion: the conductor is comaximal with `p`
  rw [RingOfIntegers.not_dvd_exponent_iff_conductor_sup_span_eq_top]
  by_contra hsup
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hsup
  have hcond𝔪 : conductor ℤ θ ≤ 𝔪 := le_trans le_sup_left hle
  have hp𝔪 : (p : 𝓞 K) ∈ 𝔪 := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hw𝔪 : w ∈ 𝔪 := hcond𝔪 hwcond
  rw [hw] at hw𝔪
  rcases h𝔪.isPrime.mem_or_mem hw𝔪 with h1 | h1
  · -- `c₀ ≡ 1 mod p` cannot lie in `𝔪`
    have hcv' := congrArg (algebraMap (𝓞 M) (𝓞 K)) hcv
    rw [map_add, map_one, map_mul, map_natCast] at hcv'
    have h2 : (1 : 𝓞 K) ∈ 𝔪 := by
      rw [← hcv']
      exact add_mem h1 (Ideal.mul_mem_left _ _ hp𝔪)
    exact h𝔪.ne_top ((Ideal.eq_top_iff_one _).mpr h2)
  · rcases h𝔪.isPrime.mem_or_mem h1 with h2 | h2
    · -- `p ∤ m`
      refine hm ?_
      have h3 := (RingOfIntegers.intCast_mem_iff_dvd h𝔪 hp𝔪 (m : ℤ)).mp
        (by rw [Int.cast_natCast]; exact h2)
      exact_mod_cast h3
    · -- `θ ∈ 𝔪` forces `p ∣ c`
      have hθ𝔪 : θ ∈ 𝔪 := h𝔪.isPrime.mem_of_pow_mem _ h2
      have hc𝔪 : ((c : ℤ) : 𝓞 K) ∈ 𝔪 := by
        rw [← hroot]
        exact Ideal.pow_mem_of_mem _ hθ𝔪 _ (by positivity)
      exact hpc ((RingOfIntegers.intCast_mem_iff_dvd h𝔪 hp𝔪 c).mp hc𝔪)

/-- **The per-prime criterion at `p`, general degree**: for `θ` a root of
`X ^ (p ^ r * m) - C c` with `r ≥ 1`, `p ∤ m` and `p ∤ c`, the prime `p` divides
`[𝓞 K : ℤ[θ]]` if and only if `p ^ 2 ∣ c ^ p ^ r - c`. -/
theorem dvd_exponent_iff_of_not_dvd {m : ℕ} (hr : 1 ≤ r) (hm : ¬p ∣ m)
    (hpc : ¬(p : ℤ) ∣ c) (hθ : minpoly ℤ θ = X ^ (p ^ r * m) - C c)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    p ∣ RingOfIntegers.exponent θ ↔ (p : ℤ) ^ 2 ∣ c ^ p ^ r - c := by
  constructor
  · intro h
    by_contra hc2
    exact not_dvd_exponent_of_sq_not_dvd_of_not_dvd hm hpc hc2 hθ hgen h
  · intro hc2
    exact dvd_exponent_of_sq_dvd hr (fun h0 => hm (by simp [h0])) hc2 hθ

end Tower

/-! ### The global criterion -/


/-- **The Jhorar–Khanduja criterion for prime-power degree** (Corollary 1.3 of
[jakharkaurkumar2023] in the case `n = p ^ r`): for `θ` with minimal polynomial
`X ^ p ^ r - c` generating `K`, the ring `ℤ[θ]` is the full ring of integers of `K` if and
only if `c` is squarefree and `p ^ 2 ∤ c ^ p ^ r - c`. -/
theorem monogenic_iff_prime_pow (hr : 1 ≤ r)
    (hθ : minpoly ℤ θ = X ^ p ^ r - C c) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    Algebra.adjoin ℤ {θ} = ⊤ ↔ Squarefree c ∧ ¬(p : ℤ) ^ 2 ∣ c ^ p ^ r - c := by
  have h2 : 2 ≤ p ^ r := by
    calc 2 ≤ p := hp.out.two_le
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ r := Nat.pow_le_pow_right hp.out.one_lt.le hr
  rw [RingOfIntegers.adjoin_eq_top_iff_forall_prime_not_dvd_exponent]
  constructor
  · intro h
    refine ⟨Int.squarefree_iff_forall_prime_sq_not_dvd.mpr fun q hq hq2 => ?_,
      fun hc2 => h p hp.out ((dvd_exponent_iff_prime_pow hr hθ hgen).mpr hc2)⟩
    haveI : Fact q.Prime := ⟨hq⟩
    have hqc : (q : ℤ) ∣ c := (dvd_pow_self _ two_ne_zero).trans hq2
    exact h q hq ((dvd_exponent_iff_of_dvd (p := q) h2 hqc hθ hgen).mpr hq2)
  · rintro ⟨hsf, hc2⟩ q hq
    haveI : Fact q.Prime := ⟨hq⟩
    rcases eq_or_ne q p with rfl | hqp
    · exact fun h => hc2 ((dvd_exponent_iff_prime_pow hr hθ hgen).mp h)
    · by_cases hqc : (q : ℤ) ∣ c
      · rw [dvd_exponent_iff_of_dvd (p := q) h2 hqc hθ hgen]
        exact Int.squarefree_iff_forall_prime_sq_not_dvd.mp hsf q hq
      · refine not_dvd_exponent_of_not_dvd (p := q) (by omega) ?_ hqc hθ hgen
        intro hdvd
        have h3 : q ∣ p ^ r := by exact_mod_cast hdvd
        exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp.out).mp (hq.dvd_of_dvd_pow h3))

/-- **The Jhorar–Khanduja criterion** (Corollary 1.3 of [jakharkaurkumar2023]), in full
generality.  Let `θ`, with minimal polynomial `X ^ n - c` over `ℤ` (`n ≥ 2`), generate the
number field `K`.  Then `ℤ[θ]` is the full ring of integers of `K` if and only if `c` is
squarefree and, for every decomposition `n = p ^ r * m` with `p` prime, `r ≥ 1`, `p ∤ m`
(that is, `r` is the exact multiplicity of `p` in `n`) and `p ∤ c`, one has
`p ^ 2 ∤ c ^ p ^ r - c`. -/
theorem monogenic_iff {n : ℕ} (hn : 2 ≤ n)
    (hθ : minpoly ℤ θ = X ^ n - C c) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    Algebra.adjoin ℤ {θ} = ⊤ ↔ Squarefree c ∧
      ∀ p r m : ℕ, p.Prime → 1 ≤ r → ¬p ∣ m → n = p ^ r * m → ¬(p : ℤ) ∣ c →
        ¬(p : ℤ) ^ 2 ∣ c ^ p ^ r - c := by
  rw [RingOfIntegers.adjoin_eq_top_iff_forall_prime_not_dvd_exponent]
  constructor
  · intro h
    refine ⟨Int.squarefree_iff_forall_prime_sq_not_dvd.mpr fun q hq hq2 => ?_,
      fun q r m hq hr hm hn' hqc hc2 => ?_⟩
    · haveI : Fact q.Prime := ⟨hq⟩
      exact h q hq ((dvd_exponent_iff_of_dvd (p := q) hn
        ((dvd_pow_self _ two_ne_zero).trans hq2) hθ hgen).mpr hq2)
    · haveI : Fact q.Prime := ⟨hq⟩
      exact h q hq (dvd_exponent_of_sq_dvd (p := q) hr (fun h0 => hm (by simp [h0])) hc2
        (hn' ▸ hθ))
  · rintro ⟨hsf, hcond⟩ q hq
    haveI : Fact q.Prime := ⟨hq⟩
    by_cases hqc : (q : ℤ) ∣ c
    · rw [dvd_exponent_iff_of_dvd (p := q) hn hqc hθ hgen]
      exact Int.squarefree_iff_forall_prime_sq_not_dvd.mp hsf q hq
    · by_cases hqn : q ∣ n
      · obtain ⟨r, m, hm, hn'⟩ := Nat.exists_eq_pow_mul_and_not_dvd
          (show n ≠ 0 by omega) q hq.ne_one
        have hr : 1 ≤ r := by
          rcases Nat.eq_zero_or_pos r with rfl | h1
          · rw [pow_zero, one_mul] at hn'
            exact absurd (hn' ▸ hqn) hm
          · exact h1
        exact not_dvd_exponent_of_sq_not_dvd_of_not_dvd (p := q) hm hqc
          (hcond q r m hq hr hm hn' hqc) (hn' ▸ hθ) hgen
      · exact not_dvd_exponent_of_not_dvd (p := q) (show n ≠ 0 by omega)
          (fun hd => hqn (by exact_mod_cast hd)) hqc hθ hgen

end NumberField.Pure
