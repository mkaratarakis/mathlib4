/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.Monogenic.PowerCompositional.Examples

/-!
# Monogenity of composed and iterated cyclotomic polynomials

Let `Φ k` denote the cyclotomic polynomial of index `k`.  Cyclotomic polynomials are
monogenic: `ℤ[ζ] = 𝓞 ℚ(ζ)`.  This file asks whether monogenity survives composition, and
answers it affirmatively for the `2`-power cyclotomic polynomials, whose composites are
therefore examples of monogenic polynomials of arbitrarily large degree.

The main result is that
`Φ (2 ^ (m + 1)) ∘ Φ (2 ^ (n + 1)) = (X ^ 2 ^ n + 1) ^ 2 ^ m + 1`
is irreducible and monogenic for all `m` and `n`.  Taking `m = n` this says that the
**second iterate** of `Φ (2 ^ (n + 1))` is monogenic.

## The proof, and why it avoids discriminants

Harrington and Jones prove that `Φ (p ^ m) ∘ Φ (2 ^ n)` is monogenic by computing the
discriminant of the composition, reading off that only `2` and `p` can divide the index, and
then treating those two primes by Dedekind's criterion.  That discriminant computation rests
on a formula for the discriminant of a composition which is not in Mathlib, and whose proof
needs resultants of polynomials of symbolic degree.

The route taken here dispenses with it.  Monogenity is `∀ q, ¬ IsIndexDivisor q T` by
Uchida's criterion, and an index divisor `q` of `T` forces the reduction of `T` mod `q` to
have a repeated factor.  So it is enough to show, for every odd `q`, that the reduction is
*separable*, and this is a Bézout identity that can be written down explicitly: with
`G = X ^ b + 1` and `T = G ^ a + 1` one has
`derivative T = C a * G ^ (a - 1) * (C b * X ^ (b - 1))`,
and `T` is coprime to each of the three factors, since

* `1 * T + (-G ^ (a - 1)) * G = 1` exhibits coprimality with `G`;
* `T (0) = 2` is invertible mod `q`, which gives coprimality with `X`;
* `a` and `b` are powers of `2`, hence invertible mod `q`.

The prime `2` is then handled by observing that `T` is `2`-Eisenstein, which also delivers
irreducibility for free.  Only the constant term and the reduction mod `2` are ever
computed; no discriminant, resultant or ramification theory appears.

## Main results

* `Polynomial.not_isIndexDivisor_of_squarefree_map`: a prime whose reduction of `g` is
  squarefree is not an index divisor of `g`.  This is the general, reusable half.
* `Polynomial.separable_map_pow_add_one_pow_add_one`: separability of the reduction of
  `(X ^ b + 1) ^ a + 1` at every prime not dividing `2 * a * b`.
* `Polynomial.isEisensteinAt_two_pow_add_one_pow_add_one`: `(X ^ b + 1) ^ (2 ^ k) + 1` is
  `2`-Eisenstein.
* `Polynomial.forall_not_isIndexDivisor_cyclotomic_comp`: no prime is an index divisor of
  `Φ (2 ^ (m + 1)) ∘ Φ (2 ^ (n + 1))`.
* `NumberField.adjoin_eq_top_of_minpoly_eq_cyclotomic_comp` and
  `NumberField.adjoin_eq_top_of_minpoly_eq_cyclotomic_comp_self`: the resulting number
  fields are monogenic, the latter for the second iterate `Φ (2 ^ (n + 1)) ∘ Φ (2 ^ (n + 1))`.

## References

* [J. Harrington, L. Jones, *Monogenic cyclotomic compositions*][HarringtonJones2019]
* [K. Uchida, *When is `ℤ[θ]` the ring of integers?*][Uchida1977]
-/

@[expose] public section

noncomputable section

open Polynomial NumberField

namespace Polynomial

/-! ### Squarefree reductions are not index divisors -/

/-- If the reduction of `g` modulo `p` is squarefree then `p` is not an index divisor of
`g`: membership of `g` in `⟨p, Pi⟩ ^ 2` forces the square of the reduction of `Pi` to divide
that of `g`, so the reduction of `Pi` is a unit, contradicting its irreducibility.

This is the discriminant-free replacement for "only the primes dividing the discriminant can
divide the index". -/
theorem not_isIndexDivisor_of_squarefree_map {p : ℕ} [Fact p.Prime] {g : ℤ[X]}
    (hsq : Squarefree (g.map (Int.castRingHom (ZMod p)))) : ¬ IsIndexDivisor p g := by
  rintro ⟨Pi, hPim, hPiirr, hmem⟩
  have hdvd : (Pi.map (Int.castRingHom (ZMod p))) ^ 2 ∣ g.map (Int.castRingHom (ZMod p)) := by
    have h := sq_span_pair_le_span_pair_sq hmem
    rwa [mem_span_pair_C_natCast_iff, Polynomial.map_pow] at h
  exact hPiirr.not_isUnit (hsq _ (by rwa [← sq]))

/-! ### The polynomials `Φ (2 ^ (n + 1))` -/

/-- The cyclotomic polynomial of index a power of two: `Φ (2 ^ (n + 1)) = X ^ 2 ^ n + 1`. -/
theorem cyclotomic_two_pow_succ (R : Type*) [CommRing R] (n : ℕ) :
    cyclotomic (2 ^ (n + 1)) R = X ^ 2 ^ n + 1 := by
  rw [cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
  simp [Finset.sum_range_succ, add_comm]

/-- Composing two `2`-power cyclotomic polynomials produces `(X ^ b + 1) ^ a + 1`. -/
theorem cyclotomic_two_pow_succ_comp (R : Type*) [CommRing R] (m n : ℕ) :
    (cyclotomic (2 ^ (m + 1)) R).comp (cyclotomic (2 ^ (n + 1)) R) =
      (X ^ 2 ^ n + 1) ^ 2 ^ m + 1 := by
  rw [cyclotomic_two_pow_succ, cyclotomic_two_pow_succ, add_comp, pow_comp, X_comp, one_comp]

/-! ### Separability of the reduction at odd primes -/

section Separable

variable {F : Type*} [Field F]

/-- A polynomial over a field is coprime to `X - C d` as soon as it does not vanish at
`d`. -/
private theorem isCoprime_X_sub_C_of_eval_ne_zero {f : F[X]} {d : F}
    (h : f.eval d ≠ 0) : IsCoprime f (X - C d) := by
  refine ⟨C (f.eval d)⁻¹, -(C (f.eval d)⁻¹ * (f /ₘ (X - C d))), ?_⟩
  have hmd := modByMonic_add_div f (X - C d)
  rw [modByMonic_X_sub_C_eq_C_eval] at hmd
  have hinv : C (f.eval d)⁻¹ * C (f.eval d) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ h, map_one]
  linear_combination hinv - C (f.eval d)⁻¹ * hmd

/-- A polynomial over a field is coprime to any nonzero constant. -/
private theorem isCoprime_C_of_ne_zero {f : F[X]} {c : F} (hc : c ≠ 0) :
    IsCoprime f (C c) := by
  refine ⟨0, C c⁻¹, ?_⟩
  rw [zero_mul, zero_add, ← map_mul, inv_mul_cancel₀ hc, map_one]

end Separable

/-- **Separability away from `2`, `a` and `b`.**  The reduction modulo `q` of
`(X ^ b + 1) ^ a + 1` is separable for every prime `q` that is odd and divides neither `a`
nor `b`.

The derivative factors as `C a * G ^ (a - 1) * (C b * X ^ (b - 1))` with `G = X ^ b + 1`,
and the polynomial is coprime to each factor: to `G` because `T - G ^ (a - 1) * G = 1`
identically, to `X` because `T (0) = 2` is invertible, and to the constants `a` and `b`
because they are invertible. -/
theorem separable_map_pow_add_one_pow_add_one {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {q : ℕ} [hq : Fact q.Prime] (hq2 : q ≠ 2) (hqa : ¬ q ∣ a) (hqb : ¬ q ∣ b) :
    Separable ((((X ^ b + 1) ^ a + 1 : ℤ[X])).map (Int.castRingHom (ZMod q))) := by
  have hmap : (((X ^ b + 1) ^ a + 1 : ℤ[X])).map (Int.castRingHom (ZMod q)) =
      ((X : (ZMod q)[X]) ^ b + 1) ^ a + 1 := by
    simp [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_one]
  rw [hmap]
  set G : (ZMod q)[X] := X ^ b + 1 with hG
  set T : (ZMod q)[X] := G ^ a + 1 with hT
  -- The three factors of the derivative.
  have hderiv : derivative T = C (a : ZMod q) * G ^ (a - 1) * (C (b : ZMod q) * X ^ (b - 1)) := by
    rw [hT, derivative_add, derivative_one, add_zero, derivative_pow, hG, derivative_add,
      derivative_one, add_zero, derivative_X_pow]
  -- `T` is coprime to `G`, by an identity with no remainder.
  have hcopG : IsCoprime T G := by
    refine ⟨1, -G ^ (a - 1), ?_⟩
    rw [one_mul, hT, neg_mul, ← pow_succ, Nat.sub_add_cancel ha]
    ring
  -- `T (0) = 2`, which is invertible since `q` is odd.
  have hevalT : T.eval 0 = 2 := by
    rw [hT, hG]
    simp [zero_pow hb.ne']
    ring
  have htwo : (2 : ZMod q) ≠ 0 := by
    intro h
    have h2 : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_two).mp
      ((CharP.cast_eq_zero_iff (ZMod q) q 2).mp h2))
  have hcopX : IsCoprime T X := by
    have h := isCoprime_X_sub_C_of_eval_ne_zero (f := T) (d := 0) (by rw [hevalT]; exact htwo)
    rwa [map_zero, sub_zero] at h
  -- The constants `a` and `b` are invertible mod `q`.
  have hane : (a : ZMod q) ≠ 0 := fun h =>
    hqa ((CharP.cast_eq_zero_iff (ZMod q) q a).mp h)
  have hbne : (b : ZMod q) ≠ 0 := fun h =>
    hqb ((CharP.cast_eq_zero_iff (ZMod q) q b).mp h)
  rw [Separable, hderiv]
  exact ((isCoprime_C_of_ne_zero hane).mul_right (hcopG.pow_right)).mul_right
    ((isCoprime_C_of_ne_zero hbne).mul_right (hcopX.pow_right))

/-! ### The prime `2`: the composition is Eisenstein -/

section Eisenstein

variable {a b : ℕ}

/-- `(X ^ b + 1) ^ a + 1` is monic. -/
theorem monic_pow_add_one_pow_add_one (ha : 0 < a) (hb : 0 < b) :
    (((X ^ b + 1) ^ a + 1 : ℤ[X])).Monic := by
  have hG : ((X ^ b + 1 : ℤ[X])).Monic := by
    simpa using monic_X_pow_add_C (1 : ℤ) hb.ne'
  have hGd : ((X ^ b + 1 : ℤ[X])).natDegree = b := by
    simpa using natDegree_X_pow_add_C (R := ℤ) (n := b) (r := 1)
  refine (hG.pow a).add_of_left ?_
  rw [degree_one, degree_eq_natDegree (hG.pow a).ne_zero, hG.natDegree_pow, hGd]
  exact_mod_cast Nat.mul_pos ha hb

/-- The degree of `(X ^ b + 1) ^ a + 1` is `a * b`. -/
theorem natDegree_pow_add_one_pow_add_one (ha : 0 < a) (hb : 0 < b) :
    (((X ^ b + 1) ^ a + 1 : ℤ[X])).natDegree = a * b := by
  have hG : ((X ^ b + 1 : ℤ[X])).Monic := by
    simpa using monic_X_pow_add_C (1 : ℤ) hb.ne'
  have hGd : ((X ^ b + 1 : ℤ[X])).natDegree = b := by
    simpa using natDegree_X_pow_add_C (R := ℤ) (n := b) (r := 1)
  have hlt : (1 : ℤ[X]).degree < ((X ^ b + 1 : ℤ[X]) ^ a).degree := by
    rw [degree_one, degree_eq_natDegree (hG.pow a).ne_zero, hG.natDegree_pow, hGd]
    exact_mod_cast Nat.mul_pos ha hb
  rw [natDegree_add_eq_left_of_degree_lt hlt, hG.natDegree_pow, hGd]

/-- The constant term of `(X ^ b + 1) ^ a + 1` is `2`. -/
theorem coeff_zero_pow_add_one_pow_add_one (hb : 0 < b) :
    (((X ^ b + 1) ^ a + 1 : ℤ[X])).coeff 0 = 2 := by
  rw [coeff_zero_eq_eval_zero]
  simp [zero_pow hb.ne']

/-- Modulo `2`, the polynomial `(X ^ b + 1) ^ (2 ^ k) + 1` is the monomial `X ^ (2 ^ k * b)`:
the exponent is a power of the characteristic, so the inner `+ 1` is raised along with
`X ^ b`, and the two resulting constant terms cancel. -/
theorem map_pow_add_one_pow_add_one_zmod_two (k : ℕ) :
    (((X ^ b + 1) ^ (2 ^ k) + 1 : ℤ[X])).map (Int.castRingHom (ZMod 2)) =
      X ^ (2 ^ k * b) := by
  have hmap : (((X ^ b + 1) ^ (2 ^ k) + 1 : ℤ[X])).map (Int.castRingHom (ZMod 2)) =
      ((X : (ZMod 2)[X]) ^ b + 1) ^ (2 ^ k) + 1 := by
    simp [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_one]
  rw [hmap, add_pow_char_pow, one_pow, ← pow_mul, mul_comm b (2 ^ k), add_assoc,
    CharTwo.add_self_eq_zero, add_zero]

/-- **The composition is `2`-Eisenstein.**  `(X ^ b + 1) ^ (2 ^ k) + 1` is Eisenstein at `2`:
its reduction mod `2` is `X ^ (2 ^ k * b)` and its constant term is `2`. -/
theorem isEisensteinAt_two_pow_add_one_pow_add_one (hb : 0 < b) (k : ℕ) :
    (((X ^ b + 1) ^ (2 ^ k) + 1 : ℤ[X])).IsEisensteinAt
      (Submodule.span ℤ {(2 : ℤ)}) := by
  have hpos : 0 < 2 ^ k := by positivity
  have hmonic := monic_pow_add_one_pow_add_one (a := 2 ^ k) (b := b) hpos hb
  have hdeg := natDegree_pow_add_one_pow_add_one (a := 2 ^ k) (b := b) hpos hb
  refine ⟨?_, ?_, ?_⟩
  · rw [hmonic.leadingCoeff]
    rw [Ideal.mem_span_singleton]
    omega
  · intro i hi
    rw [hdeg] at hi
    have h := congrArg (fun p => Polynomial.coeff p i) (map_pow_add_one_pow_add_one_zmod_two
      (b := b) k)
    simp only [coeff_map, coeff_X_pow, Int.coe_castRingHom, if_neg (show i ≠ 2 ^ k * b by
      omega)] at h
    rw [Ideal.mem_span_singleton]
    have h2 : ((2 : ℕ) : ℤ) ∣ (((X ^ b + 1) ^ 2 ^ k + 1 : ℤ[X])).coeff i :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h
    simpa using h2
  · rw [coeff_zero_pow_add_one_pow_add_one hb, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    omega

end Eisenstein

/-! ### No prime is an index divisor -/

/-- **No prime is an index divisor of `(X ^ 2 ^ l + 1) ^ 2 ^ k + 1`.**

For `q = 2` this is Eisenstein; for odd `q` the reduction is separable, hence squarefree,
because `q` divides neither of the two-power exponents. -/
theorem forall_not_isIndexDivisor_pow_add_one_pow_add_one (k l : ℕ) :
    ∀ q : ℕ, q.Prime →
      ¬ IsIndexDivisor q (((X ^ 2 ^ l + 1) ^ 2 ^ k + 1 : ℤ[X])) := by
  intro q hqp
  haveI : Fact q.Prime := ⟨hqp⟩
  have hka : 0 < 2 ^ k := by positivity
  have hlb : 0 < 2 ^ l := by positivity
  by_cases hq2 : q = 2
  · subst hq2
    refine RingOfIntegers.not_isIndexDivisor_of_isEisensteinAt
      (monic_pow_add_one_pow_add_one hka hlb) ?_
      (isEisensteinAt_two_pow_add_one_pow_add_one hlb k)
    rw [natDegree_pow_add_one_pow_add_one hka hlb]
    exact Nat.mul_pos hka hlb
  · have hnd : ∀ j : ℕ, ¬ q ∣ 2 ^ j := fun j hdvd =>
      hq2 ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow hdvd))
    exact not_isIndexDivisor_of_squarefree_map
      (separable_map_pow_add_one_pow_add_one hka hlb hq2 (hnd k) (hnd l)).squarefree

/-- **No prime is an index divisor of `Φ (2 ^ (m + 1)) ∘ Φ (2 ^ (n + 1))`.** -/
theorem forall_not_isIndexDivisor_cyclotomic_comp (m n : ℕ) :
    ∀ q : ℕ, q.Prime →
      ¬ IsIndexDivisor q ((cyclotomic (2 ^ (m + 1)) ℤ).comp (cyclotomic (2 ^ (n + 1)) ℤ)) := by
  rw [cyclotomic_two_pow_succ_comp]
  exact forall_not_isIndexDivisor_pow_add_one_pow_add_one m n

/-- The composition `Φ (2 ^ (m + 1)) ∘ Φ (2 ^ (n + 1))` is irreducible over `ℤ`, being
`2`-Eisenstein. -/
theorem irreducible_cyclotomic_comp (m n : ℕ) :
    Irreducible ((cyclotomic (2 ^ (m + 1)) ℤ).comp (cyclotomic (2 ^ (n + 1)) ℤ)) := by
  have hka : 0 < 2 ^ m := by positivity
  have hlb : 0 < 2 ^ n := by positivity
  have hprime : Ideal.IsPrime (Submodule.span ℤ {(2 : ℤ)}) :=
    (Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_two
  rw [cyclotomic_two_pow_succ_comp]
  refine (isEisensteinAt_two_pow_add_one_pow_add_one hlb m).irreducible hprime
    (monic_pow_add_one_pow_add_one hka hlb).isPrimitive ?_
  rw [natDegree_pow_add_one_pow_add_one hka hlb]
  exact Nat.mul_pos hka hlb

end Polynomial

namespace NumberField

open Polynomial

/-- **The composition of two `2`-power cyclotomic polynomials is monogenic.**  If `θ`
generates a number field `K` over `ℚ` and has minimal polynomial
`Φ (2 ^ (m + 1)) ∘ Φ (2 ^ (n + 1))`, then `ℤ[θ] = 𝓞 K`. -/
theorem adjoin_eq_top_of_minpoly_eq_cyclotomic_comp {K : Type*} [Field K] [NumberField K]
    {θ : 𝓞 K} {m n : ℕ} (hθ : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hmin : minpoly ℤ θ = (cyclotomic (2 ^ (m + 1)) ℤ).comp (cyclotomic (2 ^ (n + 1)) ℤ)) :
    Algebra.adjoin ℤ {θ} = ⊤ := by
  rw [← RingOfIntegers.forall_not_isIndexDivisor_iff_adjoin_eq_top hθ, hmin]
  exact forall_not_isIndexDivisor_cyclotomic_comp m n

/-- **The second iterate of a `2`-power cyclotomic polynomial is monogenic.**  This is the
case `m = n` of `adjoin_eq_top_of_minpoly_eq_cyclotomic_comp`: if `θ` generates `K` and its
minimal polynomial is `Φ (2 ^ (n + 1)) ∘ Φ (2 ^ (n + 1))`, then `ℤ[θ] = 𝓞 K`. -/
theorem adjoin_eq_top_of_minpoly_eq_cyclotomic_comp_self {K : Type*} [Field K] [NumberField K]
    {θ : 𝓞 K} {n : ℕ} (hθ : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hmin : minpoly ℤ θ = (cyclotomic (2 ^ (n + 1)) ℤ).comp (cyclotomic (2 ^ (n + 1)) ℤ)) :
    Algebra.adjoin ℤ {θ} = ⊤ :=
  adjoin_eq_top_of_minpoly_eq_cyclotomic_comp hθ hmin

end NumberField
