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
  the quadratic-integrality trick produces `z = h(θ) g(θ) / π ∈ 𝓞 K₁ ∖ 𝓞 K[θ]` with
  `π z ∈ 𝓞 K[θ]`; in particular `𝓞 K[θ] ≠ 𝓞 K₁`.
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

/-! ### Relative Dedekind sufficiency: saturation at a prime element

The sufficiency half of Dedekind's criterion transfers verbatim to a number field base:
if the Dedekind conditions hold at a prime element `π` of `𝓞 K` for a decomposition
`minpoly (𝓞 K) θ = g h + π M`, then `𝓞 K[θ]` has no new denominators at `π` inside
`𝓞 K₁`.  The proof is the same elementary argument as in the absolute case
(`RingOfIntegers.not_dvd_exponent_of_bezout`), with `(ℤ, p, 𝔽_p)` replaced by
`(𝓞 K, π, 𝓞 K ⧸ (π))`. -/

section DedekindSufficiency

attribute [local instance] Ideal.Quotient.field

private theorem map_quotient_span_eq_zero_iff {R : Type*} [CommRing R] {π : R} {q : R[X]} :
    q.map (Ideal.Quotient.mk (Ideal.span {π})) = 0 ↔ C π ∣ q := by
  rw [C_dvd_iff_dvd_coeff, Polynomial.ext_iff]
  refine forall_congr' fun i => ?_
  rw [coeff_map, coeff_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

/-- Change of splitting over an arbitrary domain: if `A B + π N = g h + π M` and the
reduction of `Pi` mod `π` divides the reductions of `A`, `B`, `g`, `h`, then it divides
the reduction of `M - N`. -/
private theorem map_dvd_map_sub_of_map_dvd {R : Type*} [CommRing R] [IsDomain R]
    {π : R} (hπ : Prime π) {Pi A B g h N M : R[X]} (hPi : Pi.Monic)
    (hid : A * B + C π * N = g * h + C π * M)
    (hA : Pi.map (Ideal.Quotient.mk (Ideal.span {π}))
      ∣ A.map (Ideal.Quotient.mk (Ideal.span {π})))
    (hB : Pi.map (Ideal.Quotient.mk (Ideal.span {π}))
      ∣ B.map (Ideal.Quotient.mk (Ideal.span {π})))
    (hg : Pi.map (Ideal.Quotient.mk (Ideal.span {π}))
      ∣ g.map (Ideal.Quotient.mk (Ideal.span {π})))
    (hh : Pi.map (Ideal.Quotient.mk (Ideal.span {π}))
      ∣ h.map (Ideal.Quotient.mk (Ideal.span {π}))) :
    Pi.map (Ideal.Quotient.mk (Ideal.span {π})) ∣
      M.map (Ideal.Quotient.mk (Ideal.span {π}))
        - N.map (Ideal.Quotient.mk (Ideal.span {π})) := by
  haveI hprime : (Ideal.span {π} : Ideal R).IsPrime :=
    (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  haveI : IsDomain (R ⧸ Ideal.span {π}) := Ideal.Quotient.isDomain _
  have hp0 : (C π : R[X]) ≠ 0 := fun h0 => hπ.ne_zero (C_eq_zero.mp h0)
  have hzπ : Ideal.Quotient.mk (Ideal.span {π}) π = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self π)
  have key : ∀ X : R[X], Pi.map (Ideal.Quotient.mk (Ideal.span {π}))
      ∣ X.map (Ideal.Quotient.mk (Ideal.span {π})) →
      ∃ X₁ X₂ : R[X], X = Pi * X₁ + C π * X₂ := by
    intro X hX
    have h0 : (X %ₘ Pi).map (Ideal.Quotient.mk (Ideal.span {π})) = 0 := by
      rw [map_modByMonic _ hPi, (modByMonic_eq_zero_iff_dvd (hPi.map _)).mpr hX]
    obtain ⟨X₂, hX₂⟩ := map_quotient_span_eq_zero_iff.mp h0
    exact ⟨X /ₘ Pi, X₂, by linear_combination hX₂ - modByMonic_add_div X Pi⟩
  obtain ⟨A₁, A₂, hA'⟩ := key A hA
  obtain ⟨B₁, B₂, hB'⟩ := key B hB
  obtain ⟨g₁, g₂, hg'⟩ := key g hg
  obtain ⟨h₁, h₂, hh'⟩ := key h hh
  rw [hA', hB', hg', hh'] at hid
  have h1 : Pi ^ 2 * (A₁ * B₁ - g₁ * h₁) =
      C π * (Pi * (g₁ * h₂ + g₂ * h₁ - A₁ * B₂ - A₂ * B₁) +
        C π * (g₂ * h₂ - A₂ * B₂) + (M - N)) := by
    linear_combination hid
  have hPine : Pi.map (Ideal.Quotient.mk (Ideal.span {π})) ≠ 0 := (hPi.map _).ne_zero
  have h2 : (A₁ * B₁ - g₁ * h₁).map (Ideal.Quotient.mk (Ideal.span {π})) = 0 := by
    have := congrArg (Polynomial.map (Ideal.Quotient.mk (Ideal.span {π}))) h1
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add, map_C, hzπ,
      map_zero, zero_mul] at this
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h') hPine
    · exact h'
  obtain ⟨W, hW⟩ := map_quotient_span_eq_zero_iff.mp h2
  have h3 : Pi ^ 2 * W =
      Pi * (g₁ * h₂ + g₂ * h₁ - A₁ * B₂ - A₂ * B₁) +
        C π * (g₂ * h₂ - A₂ * B₂) + (M - N) := by
    apply mul_left_cancel₀ hp0
    linear_combination h1 - Pi ^ 2 * hW
  have h4 : M.map (Ideal.Quotient.mk (Ideal.span {π}))
        - N.map (Ideal.Quotient.mk (Ideal.span {π})) =
      (Pi.map (Ideal.Quotient.mk (Ideal.span {π}))) ^ 2
          * (W.map (Ideal.Quotient.mk (Ideal.span {π}))) -
        (Pi.map (Ideal.Quotient.mk (Ideal.span {π}))) *
          (g₁.map (Ideal.Quotient.mk (Ideal.span {π}))
              * h₂.map (Ideal.Quotient.mk (Ideal.span {π})) +
            g₂.map (Ideal.Quotient.mk (Ideal.span {π}))
              * h₁.map (Ideal.Quotient.mk (Ideal.span {π})) -
            A₁.map (Ideal.Quotient.mk (Ideal.span {π}))
              * B₂.map (Ideal.Quotient.mk (Ideal.span {π})) -
            A₂.map (Ideal.Quotient.mk (Ideal.span {π}))
              * B₁.map (Ideal.Quotient.mk (Ideal.span {π}))) := by
    have := congrArg (Polynomial.map (Ideal.Quotient.mk (Ideal.span {π}))) h3
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add,
      Polynomial.map_sub, map_C, hzπ, map_zero, zero_mul] at this
    linear_combination -this
  rw [h4]
  exact dvd_sub (Dvd.dvd.mul_right (dvd_pow_self _ two_ne_zero) _)
    (Dvd.dvd.mul_right dvd_rfl _)

omit [NumberField K₁] in
/-- **Relative Dedekind criterion, sufficiency (saturation form).**  Let `θ : 𝓞 K₁`
generate `K₁` over `K`, let `π` be a prime element of `𝓞 K`, and suppose
`minpoly (𝓞 K) θ = g h + π M` where, modulo `π`, the factor `g` is squarefree, every
irreducible factor of `h` divides `g`, and `g`, `h`, `M` generate the unit ideal.
Then `𝓞 K[θ]` is `π`-saturated in `𝓞 K₁`: any `β` with
`π β ∈ 𝓞 K[θ]` already lies in `𝓞 K[θ]`.  This is the relative version of the
sufficiency half of Dedekind's criterion
(`RingOfIntegers.not_dvd_exponent_of_bezout`). -/
theorem mem_adjoin_of_algebraMap_mul_mem {π : 𝓞 K} (hπ : Prime π)
    {g h M : (𝓞 K)[X]}
    (hf : minpoly (𝓞 K) θ = g * h + C π * M)
    (hsq : Squarefree (g.map (Ideal.Quotient.mk (Ideal.span {π}))))
    (hrad : ∀ q : (𝓞 K ⧸ Ideal.span {π})[X], Irreducible q →
      q ∣ h.map (Ideal.Quotient.mk (Ideal.span {π})) →
      q ∣ g.map (Ideal.Quotient.mk (Ideal.span {π})))
    (hbez : ∃ u v w : (𝓞 K ⧸ Ideal.span {π})[X],
      u * g.map (Ideal.Quotient.mk (Ideal.span {π})) +
        v * h.map (Ideal.Quotient.mk (Ideal.span {π})) +
        w * M.map (Ideal.Quotient.mk (Ideal.span {π})) = 1)
    {β : 𝓞 K₁} (hβ : algebraMap (𝓞 K) (𝓞 K₁) π * β ∈ Algebra.adjoin (𝓞 K) {θ}) :
    β ∈ Algebra.adjoin (𝓞 K) {θ} := by
  classical
  by_contra hβnot
  haveI hmax : (Ideal.span {π} : Ideal (𝓞 K)).IsMaximal :=
    ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ).isMaximal
      (by simpa [Ideal.span_singleton_eq_bot] using hπ.ne_zero)
  have hint : IsIntegral (𝓞 K) θ := IsIntegral.tower_top θ.isIntegral
  have hsurj : Function.Surjective (Ideal.Quotient.mk (Ideal.span {π} : Ideal (𝓞 K))) :=
    Ideal.Quotient.mk_surjective
  have hzπ : Ideal.Quotient.mk (Ideal.span {π}) π = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self π)
  have hπι0 : algebraMap (𝓞 K) (𝓞 K₁) π ≠ 0 := by
    intro h0
    apply hπ.ne_zero
    have h1 : algebraMap (𝓞 K) K₁ π = 0 := by
      rw [IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 K₁) K₁, h0, map_zero]
    rw [IsScalarTower.algebraMap_apply (𝓞 K) K K₁] at h1
    exact FaithfulSMul.algebraMap_injective (𝓞 K) K (by simpa using h1)
  have hfm : (minpoly (𝓞 K) θ).Monic := minpoly.monic hint
  -- the numerator polynomial `r` of degree `< deg f`
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hβ
  obtain ⟨c, hc⟩ := hβ
  set r := c %ₘ minpoly (𝓞 K) θ with hrdef
  have hc' : aeval θ c = algebraMap (𝓞 K) (𝓞 K₁) π * β := hc
  have hrθ : aeval θ r = algebraMap (𝓞 K) (𝓞 K₁) π * β := by
    have hdivmod := modByMonic_add_div c (minpoly (𝓞 K) θ)
    have := congrArg (aeval θ) hdivmod
    rw [map_add, map_mul, minpoly.aeval, zero_mul, add_zero] at this
    rw [← hc', ← this]
  have hr0 : r.map (Ideal.Quotient.mk (Ideal.span {π})) ≠ 0 := by
    intro h0
    obtain ⟨r', hr'⟩ := map_quotient_span_eq_zero_iff.mp h0
    apply hβnot
    have hcalc : algebraMap (𝓞 K) (𝓞 K₁) π * aeval θ r'
        = algebraMap (𝓞 K) (𝓞 K₁) π * β := by
      rw [← hrθ, hr']
      simp [aeval_C, mul_comm]
    have := mul_left_cancel₀ hπι0 hcalc
    rw [← this, Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨r', rfl⟩
  have hrne : r ≠ 0 := fun h0 => hr0 (by rw [h0, Polynomial.map_zero])
  have hrdeg : r.natDegree < (minpoly (𝓞 K) θ).natDegree :=
    natDegree_lt_natDegree hrne (degree_modByMonic_lt c hfm)
  -- the gcd `Ā` and a lift `A` with `A(θ) = π γ`
  set rbar := r.map (Ideal.Quotient.mk (Ideal.span {π})) with hrbar
  set fbar := (minpoly (𝓞 K) θ).map (Ideal.Quotient.mk (Ideal.span {π})) with hfbar
  set Abar := EuclideanDomain.gcd rbar fbar with hAbardef
  have hAdvd_r : Abar ∣ rbar := EuclideanDomain.gcd_dvd_left _ _
  have hAdvd_f : Abar ∣ fbar := EuclideanDomain.gcd_dvd_right _ _
  have hA0 : Abar ≠ 0 := fun h0 => hr0 (EuclideanDomain.gcd_eq_zero_iff.mp h0).1
  have hf0 : fbar ≠ 0 := (hfm.map _).ne_zero
  obtain ⟨A, hAmap⟩ := Polynomial.map_surjective _ hsurj Abar
  obtain ⟨u, humap⟩ := Polynomial.map_surjective _ hsurj (EuclideanDomain.gcdA rbar fbar)
  obtain ⟨v, hvmap⟩ := Polynomial.map_surjective _ hsurj (EuclideanDomain.gcdB rbar fbar)
  have hkey : (A - (r * u + minpoly (𝓞 K) θ * v)).map
      (Ideal.Quotient.mk (Ideal.span {π})) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
      hAmap, humap, hvmap, ← hrbar, ← hfbar, ← EuclideanDomain.gcd_eq_gcd_ab, ← hAbardef,
      sub_self]
  obtain ⟨w, hw⟩ := map_quotient_span_eq_zero_iff.mp hkey
  set γ : 𝓞 K₁ := β * aeval θ u + aeval θ w with hγdef
  have hAθ : aeval θ A = algebraMap (𝓞 K) (𝓞 K₁) π * γ := by
    have hAeq : A = r * u + minpoly (𝓞 K) θ * v + C π * w := by linear_combination hw
    rw [hAeq]
    simp only [map_add, map_mul, minpoly.aeval, zero_mul, add_zero, aeval_C, hrθ]
    rw [hγdef]
    ring
  -- scaled minimal polynomial of `γ` gives `Ā ^ d = f̄ k̄`
  have hγint : IsIntegral (𝓞 K) γ := IsIntegral.tower_top γ.isIntegral
  set q := minpoly (𝓞 K) γ with hqdef
  have hqm : q.Monic := minpoly.monic hγint
  set d := q.natDegree with hddef
  have hd1 : 0 < d := minpoly.natDegree_pos hγint
  have hP0 : aeval θ ((q.scaleRoots π).comp A) = 0 := by
    rw [aeval_comp, hAθ]
    exact scaleRoots_aeval_eq_zero (minpoly.aeval (𝓞 K) γ)
  have hfP : minpoly (𝓞 K) θ ∣ (q.scaleRoots π).comp A :=
    minpoly.isIntegrallyClosed_dvd hint hP0
  have hscale : (q.scaleRoots π).map (Ideal.Quotient.mk (Ideal.span {π})) = X ^ d := by
    ext i
    rw [coeff_map, coeff_scaleRoots, ← hddef, coeff_X_pow, map_mul, map_pow, hzπ]
    rcases lt_trichotomy i d with hlt | heq | hgt
    · rw [if_neg hlt.ne]
      have hne : d - i ≠ 0 := Nat.sub_ne_zero_of_lt hlt
      rw [zero_pow hne, mul_zero]
    · rw [if_pos heq]
      have hcd : q.coeff i = 1 := by rw [heq, hddef]; exact hqm.coeff_natDegree
      have hdi : d - i = 0 := by omega
      rw [hcd, hdi, pow_zero, mul_one, map_one]
    · rw [if_neg hgt.ne']
      have hc0 : q.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (hddef ▸ hgt)
      rw [hc0, map_zero, zero_mul]
  have hkdvd : fbar ∣ Abar ^ d := by
    have := Polynomial.map_dvd (Ideal.Quotient.mk (Ideal.span {π})) hfP
    rwa [Polynomial.map_comp, hscale, hAmap, X_pow_comp, ← hfbar] at this
  obtain ⟨k, hk⟩ := hkdvd
  -- the complementary factor `B̄` and a monic irreducible factor `π̄` of it
  obtain ⟨Bbar, hBbar⟩ := id hAdvd_f
  have hB0 : Bbar ≠ 0 := fun h0 => hf0 (by rw [hBbar, h0, mul_zero])
  have hdegA : Abar.natDegree < fbar.natDegree := by
    have h1 : Abar.natDegree ≤ rbar.natDegree := natDegree_le_of_dvd hAdvd_r hr0
    have h2 : rbar.natDegree ≤ r.natDegree := natDegree_map_le
    have h3 : fbar.natDegree = (minpoly (𝓞 K) θ).natDegree := hfm.natDegree_map _
    omega
  have hBunit : ¬ IsUnit Bbar := by
    intro hu
    have hdeg : fbar.natDegree = Abar.natDegree := by
      rw [hBbar, natDegree_mul hA0 hB0, natDegree_eq_zero_of_isUnit hu, add_zero]
    omega
  obtain ⟨π₀, hπ₀irr, hπ₀dvd⟩ := WfDvdMonoid.exists_irreducible_factor hBunit hB0
  set πb := normalize π₀ with hπbdef
  have hπbirr : Irreducible πb := (associated_normalize π₀).irreducible hπ₀irr
  have hπbmonic : πb.Monic := monic_normalize hπ₀irr.ne_zero
  have hπbB : πb ∣ Bbar := by
    rw [hπbdef, normalize_dvd_iff]
    exact hπ₀dvd
  have hcancel : Abar ^ (d - 1) = Bbar * k := by
    apply mul_left_cancel₀ hA0
    have hpow : Abar * Abar ^ (d - 1) = Abar ^ d := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hpow, hk, hBbar]
    ring
  have hπbA : πb ∣ Abar := by
    rcases Nat.lt_or_ge d 2 with hlt | hge
    · exfalso
      have hd_eq : d = 1 := by omega
      rw [hd_eq] at hcancel
      simp only [Nat.sub_self, pow_zero] at hcancel
      exact hBunit (isUnit_of_dvd_one ⟨k, hcancel⟩)
    · have hπpow : πb ∣ Abar ^ (d - 1) := hcancel ▸ hπbB.mul_right k
      exact hπbirr.prime.dvd_of_dvd_pow hπpow
  have hπbf : πb ∣ fbar := hπbA.trans hAdvd_f
  -- `π̄` divides `ḡ` and `h̄`
  have hfgh : fbar = g.map (Ideal.Quotient.mk (Ideal.span {π}))
      * h.map (Ideal.Quotient.mk (Ideal.span {π})) := by
    have := congrArg (Polynomial.map (Ideal.Quotient.mk (Ideal.span {π}))) hf
    simpa only [Polynomial.map_add, Polynomial.map_mul, map_C, hzπ, map_zero, C_0,
      zero_mul, add_zero] using this
  have hπbg : πb ∣ g.map (Ideal.Quotient.mk (Ideal.span {π})) := by
    rcases hπbirr.prime.dvd_mul.mp (hfgh ▸ hπbf) with hcase | hcase
    · exact hcase
    · exact hrad πb hπbirr hcase
  have hπbh : πb ∣ h.map (Ideal.Quotient.mk (Ideal.span {π})) := by
    obtain ⟨g₁, hg₁⟩ := hπbg
    have hπ2 : πb ^ 2 ∣ fbar := by
      rw [hBbar, sq]
      exact mul_dvd_mul hπbA hπbB
    have hstep : πb ∣ g₁ * h.map (Ideal.Quotient.mk (Ideal.span {π})) := by
      have hh2 : πb * (g₁ * h.map (Ideal.Quotient.mk (Ideal.span {π}))) =
          g.map (Ideal.Quotient.mk (Ideal.span {π}))
            * h.map (Ideal.Quotient.mk (Ideal.span {π})) := by
        rw [hg₁]
        ring
      have := hfgh ▸ hπ2
      rw [← hh2, sq] at this
      exact (mul_dvd_mul_iff_left hπbirr.ne_zero).mp this
    rcases hπbirr.prime.dvd_mul.mp hstep with hcase | hcase
    · exfalso
      apply hπbirr.not_isUnit
      apply hsq πb
      rw [hg₁]
      exact mul_dvd_mul_left πb hcase
    · exact hcase
  -- the polynomial `N` with `f = A B + π N`, and `π̄ ∣ N̄`
  obtain ⟨B, hBmap⟩ := Polynomial.map_surjective _ hsurj Bbar
  have hN0 : (minpoly (𝓞 K) θ - A * B).map (Ideal.Quotient.mk (Ideal.span {π})) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_mul, hAmap, hBmap, ← hfbar, ← hBbar, sub_self]
  obtain ⟨N, hN⟩ := map_quotient_span_eq_zero_iff.mp hN0
  have hNθ : aeval θ N = -(γ * aeval θ B) := by
    apply mul_left_cancel₀ hπι0
    have hh0 := congrArg (aeval θ) hN
    simp only [map_sub, map_mul, minpoly.aeval, zero_sub, aeval_C] at hh0
    linear_combination -hh0 - aeval θ B * hAθ
  set Q : (𝓞 K)[X] := ∑ i ∈ Finset.range (d + 1), C (q.coeff i) * B ^ (d - i) * (-N) ^ i
    with hQdef
  have hQθ : aeval θ Q = 0 := by
    rw [hQdef, map_sum]
    have hterm : ∀ i ∈ Finset.range (d + 1),
        aeval θ (C (q.coeff i) * B ^ (d - i) * (-N) ^ i) =
          algebraMap (𝓞 K) (𝓞 K₁) (q.coeff i) * γ ^ i * (aeval θ B) ^ d := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hile : i ≤ d := by omega
      rw [map_mul, map_mul, map_pow, map_pow, map_neg, hNθ, neg_neg, aeval_C, mul_pow]
      have hBpow : (aeval θ B) ^ (d - i) * (aeval θ B) ^ i = (aeval θ B) ^ d :=
        pow_sub_mul_pow (aeval θ B) hile
      calc algebraMap (𝓞 K) (𝓞 K₁) (q.coeff i) * (aeval θ B) ^ (d - i)
            * (γ ^ i * (aeval θ B) ^ i)
          = algebraMap (𝓞 K) (𝓞 K₁) (q.coeff i) * γ ^ i *
            ((aeval θ B) ^ (d - i) * (aeval θ B) ^ i) := by ring
        _ = algebraMap (𝓞 K) (𝓞 K₁) (q.coeff i) * γ ^ i * (aeval θ B) ^ d := by
            rw [hBpow]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
    have hsum := (aeval_eq_sum_range (R := 𝓞 K) (p := q) γ).symm
    simp only [Algebra.smul_def] at hsum
    rw [hsum, minpoly.aeval, zero_mul]
  have hfQ : minpoly (𝓞 K) θ ∣ Q := minpoly.isIntegrallyClosed_dvd hint hQθ
  have hπbN : πb ∣ N.map (Ideal.Quotient.mk (Ideal.span {π})) := by
    have hπbQ : πb ∣ Q.map (Ideal.Quotient.mk (Ideal.span {π})) :=
      hπbf.trans (Polynomial.map_dvd _ hfQ)
    have hQmap : Q.map (Ideal.Quotient.mk (Ideal.span {π})) =
        ∑ i ∈ Finset.range (d + 1),
          C (Ideal.Quotient.mk (Ideal.span {π}) (q.coeff i)) * Bbar ^ (d - i) *
            (-(N.map (Ideal.Quotient.mk (Ideal.span {π})))) ^ i := by
      rw [hQdef, Polynomial.map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow,
        Polynomial.map_neg, map_C, hBmap]
    have hcd : q.coeff d = 1 := by rw [hddef]; exact hqm.coeff_natDegree
    have hsplit : Q.map (Ideal.Quotient.mk (Ideal.span {π})) =
        (-(N.map (Ideal.Quotient.mk (Ideal.span {π})))) ^ d +
          ∑ i ∈ Finset.range d,
            C (Ideal.Quotient.mk (Ideal.span {π}) (q.coeff i)) * Bbar ^ (d - i) *
              (-(N.map (Ideal.Quotient.mk (Ideal.span {π})))) ^ i := by
      rw [hQmap, Finset.sum_range_succ, hcd, map_one, map_one, Nat.sub_self, pow_zero]
      ring
    have hπbsum : πb ∣ ∑ i ∈ Finset.range d,
        C (Ideal.Quotient.mk (Ideal.span {π}) (q.coeff i)) * Bbar ^ (d - i) *
          (-(N.map (Ideal.Quotient.mk (Ideal.span {π})))) ^ i := by
      refine Finset.dvd_sum fun i hi => ?_
      rw [Finset.mem_range] at hi
      have : πb ∣ Bbar ^ (d - i) := hπbB.trans (dvd_pow_self Bbar (Nat.sub_ne_zero_of_lt hi))
      exact ((this.mul_left _).mul_right _)
    have hπbpow : πb ∣ (-(N.map (Ideal.Quotient.mk (Ideal.span {π})))) ^ d := by
      have := dvd_sub hπbQ hπbsum
      rw [hsplit, add_sub_cancel_right] at this
      exact this
    have := hπbirr.prime.dvd_of_dvd_pow hπbpow
    rwa [dvd_neg] at this
  -- change of splitting transfers `π̄ ∣ N̄` to `π̄ ∣ M̄`
  obtain ⟨Pi, hPimap, _, hPimonic⟩ :=
    lifts_and_degree_eq_and_monic ((mem_lifts πb).mpr
      (Polynomial.map_surjective _ hsurj πb)) hπbmonic
  have hid : A * B + C π * N = g * h + C π * M := by
    linear_combination hf - hN
  have hπbMN : πb ∣ M.map (Ideal.Quotient.mk (Ideal.span {π}))
      - N.map (Ideal.Quotient.mk (Ideal.span {π})) := by
    have := map_dvd_map_sub_of_map_dvd hπ hPimonic hid
      (hPimap ▸ (hπbA.trans (dvd_of_eq hAmap.symm)))
      (hPimap ▸ (hπbB.trans (dvd_of_eq hBmap.symm)))
      (hPimap ▸ hπbg) (hPimap ▸ hπbh)
    rwa [hPimap] at this
  have hπbM : πb ∣ M.map (Ideal.Quotient.mk (Ideal.span {π})) := by
    have := dvd_add hπbMN hπbN
    rwa [sub_add_cancel] at this
  -- contradiction with the Bézout certificate
  obtain ⟨u', v', w', hbez'⟩ := hbez
  apply hπbirr.not_isUnit
  apply isUnit_of_dvd_one
  rw [← hbez']
  exact dvd_add (dvd_add (hπbg.mul_left u') (hπbh.mul_left v')) (hπbM.mul_left w')

end DedekindSufficiency

end NumberField.Relative
