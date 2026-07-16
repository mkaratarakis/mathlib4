/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.Monogenic.Pure

/-!
# Relative monogenicity: the toolkit over a number field base

Let `K ⊆ K₁` be an extension of number fields and `θ : 𝓞 K₁` a generator of `K₁` over `K`.
This file tests how much of the monogenicity toolkit of this directory (developed over the
base `ℤ ⊆ ℚ`) generalizes to the relative setting `𝓞 K ⊆ K`, replacing the rational prime
`p` by a prime element `π` of `𝓞 K`.  The answer is: the *necessity* half generalizes
verbatim, with no new infrastructure — Mathlib's `conductor_mul_differentIdeal` is already
stated over an arbitrary integrally closed base, and the instances relating `𝓞 K`, `𝓞 K₁`,
`K`, `K₁` all exist.

* `NumberField.Relative.aeval_derivative_minpoly_mem_conductor`: `f'(θ)` lies in the
  conductor of `𝓞 K[θ]`, where `f` is the minimal polynomial of `θ` over `𝓞 K`.
* `NumberField.Relative.exists_mul_mem_adjoin_notMem_adjoin_of_factor` and
  `NumberField.Relative.adjoin_ne_top_of_sq_factor`: the generalized obstruction lemma over
  `𝓞 K`: if `f = h ^ 2 g + π (k h) + π ^ 2 t` with `h * g` monic of degree `< deg f`, then
  `θ - π`-divisibility produces `z ∈ 𝓞 K₁ ∖ 𝓞 K[θ]` with `π z ∈ 𝓞 K[θ]`; in particular
  `𝓞 K[θ] ≠ 𝓞 K₁`.
* `NumberField.Relative.key_identity`: the key identity for pure polynomials over any
  domain `R` with a prime element `π` whose residue ring has characteristic `p`:
  `X ^ (p ^ r * m) - C c = (X ^ m - C c) ^ p ^ r + π ((X ^ m - C c) T) + C (c ^ p ^ r - c)`.
* `NumberField.Relative.adjoin_ne_top_of_sq_dvd`: **relative pure-field necessity**: if
  `θ` has minimal polynomial `X ^ (p ^ r * m) - c` over `𝓞 K` and `π ^ 2 ∣ c ^ p ^ r - c`
  for a prime element `π` above `p`, then `𝓞 K[θ] ≠ 𝓞 K₁`.

Two remarks on scope.  First, primes of `𝓞 K` need not be principal; the statements here
take a prime *element* `π`, which suffices locally (and globally when the class group
permits).  Second, the *sufficiency* half needs, in addition, a relative comaximality
criterion (the analogue of `RingOfIntegers.not_dvd_exponent_iff_conductor_sup_span_eq_top`,
with the absolute norm argument replaced by a relative one) and the Eisenstein sufficiency;
Mathlib's Eisenstein descent
(`mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt`) is already stated over a
general base and a prime element, so this is not expected to present obstacles.  This is
future work.

## References

* [A. Jakhar, S. Kaur, S. Kumar, *On power basis of a class of number fields*,
  arXiv:2303.03138 (2023)][jakharkaurkumar2023]
-/

@[expose] public section

noncomputable section

open Polynomial NumberField Ideal

namespace NumberField.Relative

variable {K K₁ : Type*} [Field K] [NumberField K] [Field K₁] [NumberField K₁]
  [Algebra K K₁] {θ : 𝓞 K₁}

/-- If `θ` generates `K₁` over `K` and `f` is its minimal polynomial over `𝓞 K`, then
`f'(θ)` belongs to the conductor of `θ` over `𝓞 K`.  Relative version of
`RingOfIntegers.aeval_derivative_minpoly_mem_conductor`. -/
theorem aeval_derivative_minpoly_mem_conductor
    (hgen : Algebra.adjoin K {(θ : K₁)} = ⊤) :
    aeval θ (derivative (minpoly (𝓞 K) θ)) ∈ conductor (𝓞 K) θ := by
  have h : Ideal.span {aeval θ (derivative (minpoly (𝓞 K) θ))} ≤ conductor (𝓞 K) θ := by
    rw [← conductor_mul_differentIdeal (𝓞 K) K K₁ θ hgen]
    exact Ideal.mul_le_right
  exact h (Ideal.mem_span_singleton_self _)

/-- **The generalized obstruction lemma over a number field base.**  Let `f` be the minimal
polynomial of `θ : 𝓞 K₁` over `𝓞 K` and `π` a prime element of `𝓞 K`.  Given a
decomposition `f = h ^ 2 g + π (k h) + π ^ 2 t` with `h * g` monic of degree `< deg f`, the
algebraic integer `z = h(θ) g(θ) / π` satisfies `π z ∈ 𝓞 K[θ]` but `z ∉ 𝓞 K[θ]`. -/
theorem exists_mul_mem_adjoin_notMem_adjoin_of_factor {π : 𝓞 K} (hπ : Prime π)
    {h g k t : (𝓞 K)[X]} (hW : (h * g).Monic)
    (hdeg : (h * g).natDegree < (minpoly (𝓞 K) θ).natDegree)
    (hfeq : minpoly (𝓞 K) θ = h ^ 2 * g + C π * (k * h) + C π ^ 2 * t) :
    ∃ z : 𝓞 K₁, algebraMap (𝓞 K) (𝓞 K₁) π * z ∈ Algebra.adjoin (𝓞 K) {θ} ∧
      z ∉ Algebra.adjoin (𝓞 K) {θ} := by
  have hint : IsIntegral (𝓞 K) θ := IsIntegral.tower_top θ.isIntegral
  set f : (𝓞 K)[X] := minpoly (𝓞 K) θ with hf
  set πι : 𝓞 K₁ := algebraMap (𝓞 K) (𝓞 K₁) π with hπι
  set πK : K₁ := algebraMap (𝓞 K₁) K₁ πι with hπK
  have hπKeq : πK = algebraMap (𝓞 K) K₁ π := by
    rw [hπK, hπι]
    exact (IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 K₁) K₁ π).symm
  have hπK0 : πK ≠ 0 := by
    rw [hπKeq, IsScalarTower.algebraMap_apply (𝓞 K) K K₁]
    simp only [ne_eq, map_eq_zero]
    exact fun h0 =>
      hπ.ne_zero (FaithfulSMul.algebraMap_injective (𝓞 K) K (by simpa using h0))
  -- the fundamental relation `πS ^ 2 S + π kθ πS + π ^ 2 tθ = 0` in `𝓞 K₁`
  set πS : 𝓞 K₁ := aeval θ h with hπSdef
  set S : 𝓞 K₁ := aeval θ g with hS
  set kθ : 𝓞 K₁ := aeval θ k with hk
  set tθ : 𝓞 K₁ := aeval θ t with ht
  have hrel : πS ^ 2 * S + πι * (kθ * πS) + πι ^ 2 * tθ = 0 := by
    have h1 : aeval θ f = 0 := hf ▸ minpoly.aeval (𝓞 K) θ
    rw [hfeq] at h1
    simp only [map_add, map_mul, map_pow, aeval_C] at h1
    rw [hπSdef, hS, hk, ht, hπι]
    linear_combination h1
  set y : 𝓞 K₁ := πS * S with hydef
  have hy : y ^ 2 + (πι * kθ) * y + (πι ^ 2 * tθ) * S = 0 := by
    rw [hydef]
    linear_combination S * hrel
  -- `z = y / π ∈ K₁` is integral over `𝓞 K₁`, so `y = π * z'` with `z' : 𝓞 K₁`
  set z : K₁ := algebraMap (𝓞 K₁) K₁ y / πK with hz
  have hzy : πK * z = algebraMap (𝓞 K₁) K₁ y := by
    rw [hz]
    field_simp
  have hzint : IsIntegral (𝓞 K₁) z := by
    refine ⟨X ^ 2 + (C kθ * X + C (tθ * S)), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_add
        (lt_of_le_of_lt Polynomial.degree_linear_le (by norm_num))
    · simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]
      have hyK := congrArg (algebraMap (𝓞 K₁) K₁) hy
      simp only [map_add, map_mul, map_pow, map_zero] at hyK
      rw [← hzy, ← hπK] at hyK
      have hp2 : πK ^ 2 ≠ 0 := pow_ne_zero _ hπK0
      have hgoal : πK ^ 2 *
          (z ^ 2 + (algebraMap (𝓞 K₁) K₁ kθ * z +
            algebraMap (𝓞 K₁) K₁ tθ * algebraMap (𝓞 K₁) K₁ S)) = 0 := by
        linear_combination hyK
      have h2 := (mul_eq_zero.mp hgoal).resolve_left hp2
      rw [map_mul]
      linear_combination h2
  have hzint' : IsIntegral ℤ z := isIntegral_trans z hzint
  obtain ⟨z', hz'⟩ := IsIntegralClosure.isIntegral_iff (A := 𝓞 K₁) |>.mp hzint'
  have hpz' : πι * z' = y := by
    apply FaithfulSMul.algebraMap_injective (𝓞 K₁) K₁
    rw [map_mul, hz', ← hπK, hzy]
  refine ⟨z', ?_, ?_⟩
  · rw [hpz', hydef, hπSdef, hS]
    exact mul_mem (Polynomial.aeval_mem_adjoin_singleton _ θ)
      (Polynomial.aeval_mem_adjoin_singleton _ θ)
  -- if `z'` were in `𝓞 K[θ]`, then `h(θ) g(θ) = π c(θ)` with `deg c < deg f`
  intro hz'mem
  have hfmonic : f.Monic := hf ▸ minpoly.monic hint
  have haevf : aeval θ f = 0 := hf ▸ minpoly.aeval (𝓞 K) θ
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hz'mem
  obtain ⟨c, hc⟩ := hz'mem
  replace hc : aeval θ c = z' := hc
  set c' : (𝓞 K)[X] := c %ₘ f with hc'
  have haevalc' : aeval θ c' = z' := by
    rw [hc', Polynomial.modByMonic_eq_sub_mul_div c f, map_sub,
      map_mul, haevf, zero_mul, sub_zero, hc]
  have hdegc' : c'.degree < f.degree :=
    Polynomial.degree_modByMonic_lt c hfmonic
  set W : (𝓞 K)[X] := h * g with hWdef
  have haevalW : aeval θ W = y := by
    rw [hWdef, map_mul, hydef, hπSdef, hS]
  have hann : aeval θ (W - C π * c') = 0 := by
    rw [map_sub, haevalW, map_mul, aeval_C, haevalc', ← hpz', hπι]
    ring
  have hfne : f ≠ 0 := minpoly.ne_zero hint
  have hdegW : W.degree < f.degree := by
    rw [Polynomial.degree_eq_natDegree hW.ne_zero, Polynomial.degree_eq_natDegree hfne]
    exact_mod_cast hdeg
  have hdeglt : (W - C π * c').degree < f.degree := by
    apply lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
    rw [max_lt_iff]
    refine ⟨hdegW, lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_⟩
    rw [Polynomial.degree_C hπ.ne_zero, zero_add]
    exact hdegc'
  have hWeq : W = C π * c' := by
    by_contra hne
    have hsubne : W - C π * c' ≠ 0 := sub_ne_zero_of_ne hne
    have hmapne : (W - C π * c').map (algebraMap (𝓞 K) K) ≠ 0 := by
      rwa [Ne, Polynomial.map_eq_zero_iff (IsFractionRing.injective (𝓞 K) K)]
    have haev : Polynomial.aeval ((θ : K₁)) ((W - C π * c').map (algebraMap (𝓞 K) K)) = 0 := by
      rw [aeval_map_algebraMap, aeval_algebraMap_apply, hann, map_zero]
    have hge := minpoly.degree_le_of_ne_zero K ((θ : K₁)) hmapne haev
    rw [minpoly.isIntegrallyClosed_eq_field_fractions K K₁ hint,
      Polynomial.degree_map_eq_of_injective (IsFractionRing.injective (𝓞 K) K),
      Polynomial.degree_map_eq_of_injective (IsFractionRing.injective (𝓞 K) K)] at hge
    exact absurd (hge.trans_lt hdeglt) (lt_irrefl _)
  -- comparing leading coefficients makes `π` a unit, contradiction
  have hlead : (1 : 𝓞 K) = π * c'.leadingCoeff := by
    have h1 := congrArg Polynomial.leadingCoeff hWeq
    rwa [hW.leadingCoeff, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C] at h1
  exact hπ.not_unit (isUnit_of_dvd_one ⟨c'.leadingCoeff, hlead⟩)

/-- **Relative non-maximality from a repeated-factor decomposition.**  Under the hypotheses
of the obstruction lemma, `𝓞 K[θ]` is not the full ring of integers of `K₁`. -/
theorem adjoin_ne_top_of_sq_factor {π : 𝓞 K} (hπ : Prime π)
    {h g k t : (𝓞 K)[X]} (hW : (h * g).Monic)
    (hdeg : (h * g).natDegree < (minpoly (𝓞 K) θ).natDegree)
    (hfeq : minpoly (𝓞 K) θ = h ^ 2 * g + C π * (k * h) + C π ^ 2 * t) :
    Algebra.adjoin (𝓞 K) {θ} ≠ ⊤ := by
  obtain ⟨z, -, hz⟩ := exists_mul_mem_adjoin_notMem_adjoin_of_factor hπ hW hdeg hfeq
  intro htop
  rw [htop] at hz
  exact hz trivial

/-- **The key identity for pure polynomials, over a domain.**  Let `R` be a domain, `π` a
prime element whose residue ring has characteristic `p` (a prime), and `c : R`.  Then, with
`h = X ^ m - C c`,
`X ^ (p ^ r * m) - C c = h ^ p ^ r + π (h T) + C (c ^ p ^ r - c)` for some `T : R[X]`. -/
theorem key_identity {R : Type*} [CommRing R] [IsDomain R] {π : R} (hπ : Prime π)
    (p : ℕ) [hp : Fact p.Prime] [hchar : CharP (R ⧸ Ideal.span {π}) p]
    (r : ℕ) {m : ℕ} (hm : m ≠ 0) (c : R) :
    ∃ T : R[X], (X ^ (p ^ r * m) - C c : R[X]) =
      (X ^ m - C c) ^ p ^ r + C π * ((X ^ m - C c) * T) + C (c ^ p ^ r - c) := by
  haveI hprime : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  set q : R →+* R ⧸ Ideal.span {π} := Ideal.Quotient.mk (Ideal.span {π}) with hq
  set hpoly : R[X] := X ^ m - C c with hh
  have hhm : hpoly.Monic := monic_X_pow_sub_C _ hm
  -- `h` divides `E := X ^ (p ^ r * m) - C (c ^ p ^ r) - h ^ p ^ r`
  have hdvd : hpoly ∣ X ^ (p ^ r * m) - C (c ^ p ^ r) - hpoly ^ p ^ r := by
    refine dvd_sub ?_ (dvd_pow_self hpoly (pow_ne_zero r hp.out.ne_zero))
    have h1 := sub_dvd_pow_sub_pow (X ^ m : R[X]) (C c) (p ^ r)
    rwa [← pow_mul, mul_comm m, ← map_pow] at h1
  obtain ⟨V, hV⟩ := hdvd
  -- modulo `π`, `E` vanishes by Frobenius, hence `π` divides `V`
  have hmapE : (X ^ (p ^ r * m) - C (c ^ p ^ r) - hpoly ^ p ^ r).map q = 0 := by
    have hfrob : ((X : (R ⧸ Ideal.span {π})[X]) ^ m - C (q c)) ^ p ^ r =
        X ^ (p ^ r * m) - C (q c) ^ p ^ r := by
      rw [sub_pow_char_pow, ← pow_mul, mul_comm m, ← map_pow]
    simp only [hh, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C, map_pow]
    rw [hfrob]
    ring
  have hpV : C π ∣ V := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    have hVmap : V.map q = 0 := by
      have h2 : hpoly.map q * V.map q = 0 := by
        rw [← Polynomial.map_mul, ← hV, hmapE]
      exact (mul_eq_zero.mp h2).resolve_left (hhm.map _).ne_zero
    have h3 := congrArg (fun w : (R ⧸ Ideal.span {π})[X] => w.coeff i) hVmap
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h3
    rw [← Ideal.mem_span_singleton]
    exact (Ideal.Quotient.eq_zero_iff_mem).mp h3
  obtain ⟨T, hT⟩ := hpV
  refine ⟨T, ?_⟩
  have hE : X ^ (p ^ r * m) - C (c ^ p ^ r) - hpoly ^ p ^ r = C π * (hpoly * T) := by
    rw [hV, hT]
    ring
  rw [Polynomial.C_sub]
  linear_combination hE

variable {p r m : ℕ}

/-- **Relative pure-field necessity.**  Let `θ : 𝓞 K₁` have minimal polynomial
`X ^ (p ^ r * m) - c` over `𝓞 K` and let `π` be a prime element of `𝓞 K` lying above the
rational prime `p` (in the sense that the residue ring of `π` has characteristic `p`).  If
`π ^ 2 ∣ c ^ p ^ r - c` and `r ≥ 1`, then `𝓞 K[θ]` is not the full ring of integers of
`K₁`.  This is the relative analogue of `NumberField.Pure.dvd_exponent_of_sq_dvd`. -/
theorem adjoin_ne_top_of_sq_dvd {π c : 𝓞 K} (hπ : Prime π) [hp : Fact p.Prime]
    [hchar : CharP ((𝓞 K) ⧸ Ideal.span {π}) p] (hr : 1 ≤ r) (hm : m ≠ 0)
    (hc2 : π ^ 2 ∣ c ^ p ^ r - c)
    (hθ : minpoly (𝓞 K) θ = X ^ (p ^ r * m) - C c) :
    Algebra.adjoin (𝓞 K) {θ} ≠ ⊤ := by
  obtain ⟨T, hT⟩ := key_identity hπ p r hm c
  obtain ⟨t₀, ht₀⟩ := hc2
  have h2 : 2 ≤ p ^ r := by
    calc 2 ≤ p := hp.out.two_le
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ r := Nat.pow_le_pow_right hp.out.one_lt.le hr
  have hhm : (X ^ m - C c : (𝓞 K)[X]).Monic := monic_X_pow_sub_C c hm
  have hsplit : (X ^ m - C c : (𝓞 K)[X]) ^ p ^ r
      = (X ^ m - C c) ^ 2 * (X ^ m - C c) ^ (p ^ r - 2) := by
    rw [← pow_add]
    congr 1
    omega
  refine adjoin_ne_top_of_sq_factor hπ
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

end NumberField.Relative
