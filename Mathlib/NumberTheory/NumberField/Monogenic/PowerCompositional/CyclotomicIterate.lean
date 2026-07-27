/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.Monogenic.PowerCompositional.Examples
public import Mathlib.NumberTheory.NumberField.Monogenic.PowerCompositional.GeneralBase

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

For iterates of arbitrary depth, written `(f.comp ·)^[r] X`:

* `Polynomial.comp_iterate_add` and `Polynomial.derivative_comp_iterate`: composition of
  iterates adds the exponents, and the derivative of an iterate is the product of `f'` along
  the orbit.  Both hold for any polynomial.
* `Polynomial.isEisensteinAt_two_comp_iterate`: **every even iterate of `Φ (2 ^ (k + 1))` is
  Eisenstein at `2`**, hence irreducible.  The odd iterates are not: their constant terms are
  odd.
* `Polynomial.separable_map_comp_iterate`: the reduction of an iterate mod `q` is separable
  as soon as `q` divides neither `b` nor a member of the *critical orbit*
  `Q 1 (0), …, Q r (0)`, where `Q j` is the `j`-fold iterate.
* `Polynomial.forall_not_isIndexDivisor_comp_iterate` and
  `NumberField.adjoin_eq_top_of_minpoly_eq_comp_iterate`: consequently the index divisors of
  an even iterate are confined to the odd primes dividing the critical orbit.

The critical orbit begins `1, 2`, so for the second iterate the condition is vacuous and
`Polynomial.forall_not_isIndexDivisor_comp_iterate_two` is unconditional, recovering the
main theorem.

Those hypotheses are then removed entirely in favour of a sharp criterion:

* `Polynomial.isIndexDivisor_comp_iterate_iff_exists_sq_dvd`: for `q` not dividing `b`,
  **`q` is an index divisor of the `r`-fold iterate if and only if `q ^ 2` divides one of the
  first `r` members of the critical orbit**.  A prime that meets the orbit is harmless; only a
  *square* obstructs.
* `Polynomial.forall_not_isIndexDivisor_comp_iterate_iff_squarefree` and
  `NumberField.adjoin_eq_top_iff_forall_squarefree_of_minpoly_eq_comp_iterate`: consequently,
  for `r` odd the `(r + 1)`-fold iterate of `Φ (2 ^ (k + 1))` is monogenic **if and only if**
  `c 1, …, c (r + 1)` are squarefree.  The prime `2` never obstructs, an even iterate being
  Eisenstein there.

This is best possible: the two directions are `isIndexDivisor_comp_iterate_of_sq_dvd` and
`not_isIndexDivisor_comp_iterate_of_not_sq_dvd`.  For `k = 1` the orbit is
`1, 2, 5, 26, 677, 458330, …`, squarefree as far as it has been computed, so every iterate
whose orbit one can factor is monogenic; whether the orbit is squarefree forever is a
Wieferich-type question, not settled here.

Two hypotheses are then removed.

* **Parity.**  An odd iterate is not Eisenstein at `2`, but its translate by `1` is, since
  `Q r (1) = c (r + 1)` lands at an even index of the orbit and so is exactly divisible by
  `2`.  Index divisors are a translation invariant
  (`Polynomial.isIndexDivisor_comp_X_add_C_iff`), so `2` is never an index divisor of any
  iterate (`Polynomial.not_isIndexDivisor_two_comp_iterate'`), every iterate is irreducible
  (`Polynomial.irreducible_comp_iterate`), and the criterion holds for all `r`
  (`Polynomial.forall_not_isIndexDivisor_comp_iterate_iff_squarefree'`,
  `NumberField.adjoin_eq_top_iff_forall_squarefree_of_minpoly_eq_comp_iterate'`).
* **The constant term.**  Nothing in the odd-prime argument used the value `1`, only that
  `0` is the sole critical point and has full multiplicity `b`.  The hypotheses are therefore
  packaged as `f = X ^ b + C A`, and the criterion holds for every *unicritical* polynomial
  (`Polynomial.isIndexDivisor_comp_iterate_pow_add_C_iff`) — in particular for `X ^ b - A`,
  hence for iterates of pure polynomials.  At `r = 1` it specialises to the classical
  statement that a prime `q ∤ b` divides the index of a root of `X ^ b + A` exactly when
  `q ^ 2 ∣ A` (`Polynomial.isIndexDivisor_pow_add_C_iff`).

What remains special to the cyclotomic case is only the prime `2`, which divides `b = 2 ^ k`
and so is invisible to the separability argument; it is handled by Eisenstein instead.

## References

* [J. Harrington, L. Jones, *Monogenic cyclotomic compositions*][HarringtonJones2019]
* [K. Uchida, *When is `ℤ[θ]` the ring of integers?*][Uchida1977]
-/

set_option linter.style.longFile 1800

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

namespace Polynomial

/-! ### Arbitrary iterates

The `r`-fold iterate of `f` is written `(f.comp ·)^[r] X`.  The two lemmas below hold for
any polynomial and are what make the analysis of an iterate possible: composition of
iterates adds the exponents, and the derivative of an iterate is the product of the
derivative of `f` along the orbit, by the chain rule. -/

section CompIterate

variable {R : Type*} [CommRing R]

/-- Iterating `f` first `i` and then `m` times is iterating it `m + i` times. -/
theorem comp_iterate_add (f : R[X]) (m i : ℕ) :
    (f.comp ·)^[m + i] X = ((f.comp ·)^[m] X).comp ((f.comp ·)^[i] X) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_add, Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      comp_assoc]

/-- **Chain rule for iterates**: the derivative of the `r`-fold iterate of `f` is the
product of `f'` evaluated along the orbit `X, f, f ∘ f, …`. -/
theorem derivative_comp_iterate (f : R[X]) (r : ℕ) :
    derivative ((f.comp ·)^[r] X) =
      ∏ i ∈ Finset.range r, (derivative f).comp ((f.comp ·)^[i] X) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', derivative_comp, ih, Finset.prod_range_succ]

variable [IsDomain R]

/-- The degree of an iterate is the degree of `f` raised to the number of steps. -/
theorem natDegree_comp_iterate (f : R[X]) (r : ℕ) :
    ((f.comp ·)^[r] X).natDegree = f.natDegree ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', natDegree_comp, ih, pow_succ']

/-- An iterate of a monic polynomial of positive degree is monic. -/
theorem monic_comp_iterate {f : R[X]} (hf : f.Monic) (hfd : 0 < f.natDegree) (r : ℕ) :
    ((f.comp ·)^[r] X).Monic := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact hf.comp ih (by rw [natDegree_comp_iterate]; exact (Nat.pow_pos hfd).ne')

end CompIterate

/-! ### The critical orbit of `X ^ b + 1` -/

section Orbit

variable {b : ℕ}

/-- One step of the iteration for a general unicritical `f = X ^ b + A`:
`Q (r + 1) = Q r ^ b + A`. -/
theorem comp_iterate_succ_eq {R : Type*} [CommRing R] {f : R[X]} {A : R} (hf : f = X ^ b + C A)
    (r : ℕ) :
    (f.comp ·)^[r + 1] X = ((f.comp ·)^[r] X) ^ b + C A := by
  rw [Function.iterate_succ_apply', hf, add_comp, pow_comp, X_comp, C_comp]

/-- One step of the iteration: `Q (r + 1) = Q r ^ b + 1`. -/
theorem comp_iterate_pow_add_one_succ (r : ℕ) :
    (((X ^ b + 1 : ℤ[X])).comp ·)^[r + 1] X =
      ((((X ^ b + 1 : ℤ[X])).comp ·)^[r] X) ^ b + 1 :=
  comp_iterate_succ_eq (A := 1) rfl r

/-- Along the orbit the constant terms alternate in parity: `Q r (0)` is odd exactly when
`r` is odd.  This is what makes every *even* iterate Eisenstein at `2`. -/
theorem odd_eval_zero_comp_iterate_iff (hb : 0 < b) (r : ℕ) :
    Odd (((((X ^ b + 1 : ℤ[X])).comp ·)^[r] X).eval 0) ↔ Odd r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [comp_iterate_pow_add_one_succ, eval_add, eval_pow, eval_one,
      ← Int.not_even_iff_odd, ← Nat.not_even_iff_odd, Int.even_add_one, Nat.even_add_one,
      not_not, not_not, Int.even_pow' hb.ne', ← Int.not_odd_iff_even, ← Nat.not_odd_iff_even]
    exact not_congr ih

/-- For `b` even, the constant term of an *even* iterate is `2` mod `4`: it is `c ^ b + 1`
for an odd `c`, and an odd `b`-th power with `b` even is `1` mod `4`. -/
theorem not_four_dvd_eval_zero_comp_iterate (hb : 0 < b) (hbe : Even b) {r : ℕ} (hr : Odd r) :
    ¬ (4 : ℤ) ∣ ((((X ^ b + 1 : ℤ[X])).comp ·)^[r + 1] X).eval 0 := by
  obtain ⟨c, hc⟩ := (odd_eval_zero_comp_iterate_iff hb r).mpr hr
  rw [comp_iterate_pow_add_one_succ, eval_add, eval_pow, eval_one, hc]
  obtain ⟨b', hb'⟩ := hbe
  obtain ⟨d, hd⟩ : Odd ((2 * c + 1 : ℤ) ^ b') := (Int.odd_pow' (by omega)).mpr ⟨c, rfl⟩
  rw [hb', show b' + b' = b' * 2 by ring, pow_mul, hd,
    show ((2 * d + 1 : ℤ)) ^ 2 + 1 = 4 * (d * d + d) + 2 by ring]
  rintro ⟨e, he⟩
  omega

end Orbit

/-! ### Separability of an iterate away from the critical orbit -/

/-- **An iterate is coprime to every earlier member of its orbit**, modulo any prime not
dividing the corresponding constant term.

Since `Q r = Q (r - i) ∘ Q i` and `Q (r - i) - Q (r - i) (0)` is divisible by `X`, one has
`Q r = C (Q (r - i) (0)) + Q i * W`; if the constant is invertible mod `q` this *is* a Bézout
identity for `Q r` and `Q i`. -/
theorem isCoprime_map_comp_iterate {f : ℤ[X]} {q : ℕ} [Fact q.Prime] {r i : ℕ} (hi : i < r)
    (horb : ¬ (q : ℤ) ∣ ((f.comp ·)^[r - i] X).eval 0) :
    IsCoprime (((f.comp ·)^[r] X).map (Int.castRingHom (ZMod q)))
      (((f.comp ·)^[i] X).map (Int.castRingHom (ZMod q))) := by
  obtain ⟨V, hV⟩ : (X : ℤ[X]) ∣
      ((f.comp ·)^[r - i] X) - C (((f.comp ·)^[r - i] X).eval 0) := by
    rw [X_dvd_iff, coeff_sub, coeff_C_zero, ← coeff_zero_eq_eval_zero, sub_self]
  set c : ℤ := ((f.comp ·)^[r - i] X).eval 0 with hc
  have hcomp : ((f.comp ·)^[r] X) = (((f.comp ·)^[r - i] X)).comp (((f.comp ·)^[i] X)) := by
    have h := comp_iterate_add f (r - i) i
    rwa [Nat.sub_add_cancel hi.le] at h
  have hQm : ((f.comp ·)^[r - i] X) = C c + X * V := by linear_combination hV
  have hsplit : ((f.comp ·)^[r] X) =
      C c + ((f.comp ·)^[i] X) * V.comp ((f.comp ·)^[i] X) := by
    rw [hcomp, hQm, add_comp, mul_comp, C_comp, X_comp]
  have hcne : ((c : ℤ) : ZMod q) ≠ 0 := fun h =>
    horb ((ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp h)
  refine ⟨C ((c : ℤ) : ZMod q)⁻¹,
    -(C ((c : ℤ) : ZMod q)⁻¹ *
      (V.comp ((f.comp ·)^[i] X)).map (Int.castRingHom (ZMod q))), ?_⟩
  have hmap : ((f.comp ·)^[r] X).map (Int.castRingHom (ZMod q)) =
      C ((c : ℤ) : ZMod q) + ((f.comp ·)^[i] X).map (Int.castRingHom (ZMod q)) *
        (V.comp ((f.comp ·)^[i] X)).map (Int.castRingHom (ZMod q)) := by
    rw [hsplit]; simp
  have hinv : C ((c : ℤ) : ZMod q)⁻¹ * C ((c : ℤ) : ZMod q) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hcne, map_one]
  rw [hmap]
  linear_combination hinv

/-- Separability of the reduction of an iterate, given coprimality with each factor of the
derivative supplied by the chain rule. -/
theorem separable_map_comp_iterate_of_isCoprime {f : ℤ[X]} {q : ℕ} [Fact q.Prime] {r : ℕ}
    (hcop : ∀ i, i < r → IsCoprime (((f.comp ·)^[r] X).map (Int.castRingHom (ZMod q)))
      (((derivative f).comp ((f.comp ·)^[i] X)).map (Int.castRingHom (ZMod q)))) :
    Separable (((f.comp ·)^[r] X).map (Int.castRingHom (ZMod q))) := by
  rw [separable_def, derivative_map, derivative_comp_iterate, Polynomial.map_prod]
  exact IsCoprime.prod_right fun i hi => hcop i (Finset.mem_range.mp hi)

/-- **The reduction of an iterate is separable away from `b` and the critical orbit.**
If the prime `q` divides neither `b` nor any of the constant terms `Q j (0)` for
`1 ≤ j ≤ r`, then the reduction mod `q` of the `r`-fold iterate of `X ^ b + 1` is separable,
hence squarefree, hence `q` is not an index divisor.

This is the discriminant-free bound on the index divisors of an arbitrary iterate: only the
primes dividing `b` or the critical orbit `Q 1 (0), …, Q r (0)` survive. -/
theorem separable_map_comp_iterate {f : ℤ[X]} {A : ℤ} {b q : ℕ} (hf : f = X ^ b + C A)
    [Fact q.Prime] (hqb : ¬ q ∣ b) {r : ℕ}
    (horb : ∀ j, 0 < j → j ≤ r →
      ¬ (q : ℤ) ∣ ((f.comp ·)^[j] X).eval 0) :
    Separable ((((f.comp ·)^[r] X)).map (Int.castRingHom (ZMod q))) := by
  have hbne : ((b : ℤ) : ZMod q) ≠ 0 := fun h =>
    hqb ((CharP.cast_eq_zero_iff (ZMod q) q b).mp (by exact_mod_cast h))
  refine separable_map_comp_iterate_of_isCoprime fun i hi => ?_
  have hif : ((derivative f).comp
        ((f.comp ·)^[i] X)).map (Int.castRingHom (ZMod q)) =
      C ((b : ℤ) : ZMod q) *
        (((f.comp ·)^[i] X).map (Int.castRingHom (ZMod q))) ^ (b - 1) := by
    rw [hf, derivative_add, derivative_C, add_zero, derivative_X_pow, mul_comp, C_comp,
      pow_comp, X_comp]
    simp
  rw [hif]
  exact (isCoprime_C_of_ne_zero hbne).mul_right
    ((isCoprime_map_comp_iterate hi (horb (r - i) (by omega) (by omega))).pow_right)

/-! ### Even iterates are Eisenstein at `2` -/

section EisensteinIterate

variable {k : ℕ}

/-- Modulo `2`, the `r`-fold iterate of `X ^ (2 ^ k) + 1` is `X ^ (b ^ r)` plus the parity of
`r`: raising to the power `2 ^ k`, a power of the characteristic, is additive, so the
constant term flips at every step. -/
theorem map_comp_iterate_zmod_two (r : ℕ) :
    ((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[r] X).map (Int.castRingHom (ZMod 2)) =
      X ^ (2 ^ k) ^ r + C ((r : ℕ) : ZMod 2) := by
  have hb : 0 < 2 ^ k := by positivity
  have hxb : ∀ x : ZMod 2, x ^ 2 ^ k = x := by
    intro x
    have hx : x = 0 ∨ x = 1 := by revert x; decide
    rcases hx with rfl | rfl
    · simp [zero_pow hb.ne']
    · simp
  induction r with
  | zero => simp
  | succ r ih =>
    rw [comp_iterate_pow_add_one_succ, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_one, ih, add_pow_char_pow, ← pow_mul, ← C_pow, hxb,
      show (2 ^ k) ^ r * 2 ^ k = (2 ^ k) ^ (r + 1) from (pow_succ _ _).symm, add_assoc]
    congr 1
    rw [← C_1, ← map_add]
    congr 1
    push_cast
    ring

/-- **Every even iterate of `Φ (2 ^ (k + 1))` is Eisenstein at `2`**, hence irreducible: its
reduction mod `2` is the monomial `X ^ (2 ^ k) ^ (r + 1)`, because `r + 1` is even, and its
constant term is `2` mod `4`, because it is `c ^ b + 1` for an odd `c` and an even `b`. -/
theorem isEisensteinAt_two_comp_iterate (hk : 0 < k) {r : ℕ} (hr : Odd r) :
    ((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[r + 1] X).IsEisensteinAt
      (Submodule.span ℤ {(2 : ℤ)}) := by
  have hb : 0 < 2 ^ k := by positivity
  have hbe : Even (2 ^ k) := (Nat.even_pow' hk.ne').mpr even_two
  have hfm : ((X ^ 2 ^ k + 1 : ℤ[X])).Monic := by
    simpa using monic_X_pow_add_C (1 : ℤ) hb.ne'
  have hfd : ((X ^ 2 ^ k + 1 : ℤ[X])).natDegree = 2 ^ k := by
    simpa using natDegree_X_pow_add_C (R := ℤ) (n := 2 ^ k) (r := 1)
  have hmonic := monic_comp_iterate hfm (by omega) (r + 1)
  have hdeg : ((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[r + 1] X).natDegree = (2 ^ k) ^ (r + 1) := by
    rw [natDegree_comp_iterate, hfd]
  have hmap : ((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[r + 1] X).map (Int.castRingHom (ZMod 2)) =
      X ^ (2 ^ k) ^ (r + 1) := by
    obtain ⟨t, ht⟩ := hr
    rw [map_comp_iterate_zmod_two (r + 1), show r + 1 = 2 * (t + 1) by omega, Nat.cast_mul,
      show ((2 : ℕ) : ZMod 2) = 0 by decide, zero_mul, map_zero, add_zero,
      show 2 * (t + 1) = r + 1 by omega]
  refine ⟨?_, ?_, ?_⟩
  · rw [hmonic.leadingCoeff, Ideal.mem_span_singleton]
    omega
  · intro i hi
    rw [hdeg] at hi
    have h := congrArg (fun p => Polynomial.coeff p i) hmap
    simp only [coeff_map, coeff_X_pow, Int.coe_castRingHom,
      if_neg (show i ≠ (2 ^ k) ^ (r + 1) by omega)] at h
    rw [Ideal.mem_span_singleton]
    have h2 : ((2 : ℕ) : ℤ) ∣ ((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[r + 1] X).coeff i :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h
    simpa using h2
  · rw [coeff_zero_eq_eval_zero, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro hdvd
    exact not_four_dvd_eval_zero_comp_iterate hb hbe hr (by simpa using hdvd)

end EisensteinIterate

end Polynomial

namespace Polynomial

/-! ### Index divisors of an arbitrary iterate -/

/-- **`2` is never an index divisor of an even iterate of `Φ (2 ^ (k + 1))`**, since such an
iterate is Eisenstein at `2`. -/
theorem not_isIndexDivisor_two_comp_iterate {k : ℕ} (hk : 0 < k) {r : ℕ} (hr : Odd r) :
    ¬ IsIndexDivisor 2 ((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[r + 1] X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb : 0 < 2 ^ k := by positivity
  have hfm : ((X ^ 2 ^ k + 1 : ℤ[X])).Monic := by
    simpa using monic_X_pow_add_C (1 : ℤ) hb.ne'
  have hfd : ((X ^ 2 ^ k + 1 : ℤ[X])).natDegree = 2 ^ k := by
    simpa using natDegree_X_pow_add_C (R := ℤ) (n := 2 ^ k) (r := 1)
  refine RingOfIntegers.not_isIndexDivisor_of_isEisensteinAt
    (monic_comp_iterate hfm (by omega) (r + 1)) ?_ (isEisensteinAt_two_comp_iterate hk hr)
  rw [natDegree_comp_iterate, hfd]
  positivity

/-- **A prime dividing neither `b` nor the critical orbit is never an index divisor of an
iterate of `X ^ b + 1`.** -/
theorem not_isIndexDivisor_comp_iterate_of_not_dvd_orbit {f : ℤ[X]} {A : ℤ} {b q : ℕ}
    (hf : f = X ^ b + C A) [Fact q.Prime] (hqb : ¬ q ∣ b) {r : ℕ}
    (horb : ∀ j, 0 < j → j ≤ r →
      ¬ (q : ℤ) ∣ ((f.comp ·)^[j] X).eval 0) :
    ¬ IsIndexDivisor q ((f.comp ·)^[r] X) :=
  not_isIndexDivisor_of_squarefree_map (separable_map_comp_iterate hf hqb horb).squarefree

/-- **The index divisors of an even iterate of `Φ (2 ^ (k + 1))` are confined to the critical
orbit.**  If no odd prime dividing one of the constant terms `Q j (0)`, `1 ≤ j ≤ r + 1`, is an
index divisor, then no prime at all is, and the iterate is monogenic.

The prime `2` is excluded outright by Eisenstein; every other prime not meeting the orbit is
excluded by separability.  This is the discriminant-free analogue of Harrington and Jones'
step "only `2` and `p` divide the discriminant". -/
theorem forall_not_isIndexDivisor_comp_iterate {k : ℕ} (hk : 0 < k) {r : ℕ} (hr : Odd r)
    (horb : ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ j, 0 < j → j ≤ r + 1 →
      ¬ (q : ℤ) ∣ ((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[j] X).eval 0) :
    ∀ q : ℕ, q.Prime → ¬ IsIndexDivisor q ((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[r + 1] X) := by
  intro q hqp
  haveI : Fact q.Prime := ⟨hqp⟩
  by_cases hq2 : q = 2
  · subst hq2
    exact not_isIndexDivisor_two_comp_iterate hk hr
  · refine not_isIndexDivisor_comp_iterate_of_not_dvd_orbit (A := 1) rfl ?_ (horb q hqp hq2)
    intro hdvd
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow hdvd))

/-! ### The beginning of the critical orbit -/

/-- `Q 1 (0) = 1`. -/
theorem eval_zero_comp_iterate_one {b : ℕ} (hb : 0 < b) :
    ((((X ^ b + 1 : ℤ[X])).comp ·)^[1] X).eval 0 = 1 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, comp_iterate_pow_add_one_succ]
  simp [zero_pow hb.ne']

/-- `Q 2 (0) = 2`. -/
theorem eval_zero_comp_iterate_two {b : ℕ} (hb : 0 < b) :
    ((((X ^ b + 1 : ℤ[X])).comp ·)^[2] X).eval 0 = 2 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, comp_iterate_pow_add_one_succ, eval_add, eval_pow,
    eval_one, eval_zero_comp_iterate_one hb, one_pow]
  norm_num

/-- **The second iterate meets the orbit condition unconditionally**, since the critical
orbit starts `1, 2`: no odd prime divides either.  So the general iterate theorem recovers
the unconditional monogenity of `Φ (2 ^ (k + 1)) ∘ Φ (2 ^ (k + 1))`. -/
theorem forall_not_isIndexDivisor_comp_iterate_two {k : ℕ} (hk : 0 < k) :
    ∀ q : ℕ, q.Prime → ¬ IsIndexDivisor q ((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[2] X) := by
  have hb : 0 < 2 ^ k := by positivity
  refine forall_not_isIndexDivisor_comp_iterate hk odd_one ?_
  intro q hqp hq2 j hj0 hj2
  have hq2' := hqp.two_le
  interval_cases j
  · rw [eval_zero_comp_iterate_one hb]
    intro h
    have := Int.le_of_dvd one_pos h
    omega
  · rw [eval_zero_comp_iterate_two hb]
    intro h
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp
      (by exact_mod_cast h))

end Polynomial

namespace NumberField

open Polynomial

/-- **Monogenity of an even iterate of a `2`-power cyclotomic polynomial.**  If `θ` generates
a number field `K` over `ℚ` and its minimal polynomial is the `(r + 1)`-fold iterate of
`Φ (2 ^ (k + 1)) = X ^ (2 ^ k) + 1` with `r` odd, and no odd prime dividing the critical
orbit `Q 1 (0), …, Q (r + 1) (0)` divides that orbit, then `ℤ[θ] = 𝓞 K`. -/
theorem adjoin_eq_top_of_minpoly_eq_comp_iterate {K : Type*} [Field K] [NumberField K]
    {θ : 𝓞 K} {k r : ℕ} (hk : 0 < k) (hr : Odd r)
    (hθ : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hmin : minpoly ℤ θ = (((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[r + 1] X)
    (horb : ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ j, 0 < j → j ≤ r + 1 →
      ¬ (q : ℤ) ∣ ((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[j] X).eval 0) :
    Algebra.adjoin ℤ {θ} = ⊤ := by
  rw [← RingOfIntegers.forall_not_isIndexDivisor_iff_adjoin_eq_top hθ, hmin]
  exact forall_not_isIndexDivisor_comp_iterate hk hr horb

end NumberField

namespace Polynomial

/-! ### The critical orbit, sharply

The results above exclude every prime that misses the critical orbit
`c j = Q j (0)`.  This section determines exactly what happens at a prime that meets it,
and shows that the answer depends only on the *first* index at which it does, and only to
first order: `q` is an index divisor precisely when `q ^ 2` divides that first constant term.

The mechanism is that the orbit starts at the critical point `0` of `X ^ b + 1`, so
`Q m - C (c m)` is divisible by `X ^ b`; composing with `Q (r - m)` gives
`Q r = C (c m) + Q (r - m) ^ b * W`.  Since `b ≥ 2`, the second summand lies in
`⟨q, Pi⟩ ^ 2` for any `Pi` dividing the reduction of `Q (r - m)`, so membership of `Q r`
is decided by the constant `c m` alone. -/

section CriticalOrbit

/-- An iterate is congruent to a constant modulo any earlier iterate: `Q r ≡ c (r - i)` mod
`Q i`.  This is `Q r = Q (r - i) ∘ Q i` together with `X ∣ Q (r - i) - C (c (r - i))`. -/
theorem comp_iterate_dvd_sub_C {R : Type*} [CommRing R] (f : R[X]) {i r : ℕ} (hir : i ≤ r) :
    ((f.comp ·)^[i] X) ∣
      ((f.comp ·)^[r] X) - C (((f.comp ·)^[r - i] X).eval 0) := by
  obtain ⟨V, hV⟩ : (X : R[X]) ∣
      ((f.comp ·)^[r - i] X) - C (((f.comp ·)^[r - i] X).eval 0) := by
    rw [X_dvd_iff, coeff_sub, coeff_C_zero, ← coeff_zero_eq_eval_zero, sub_self]
  set c : R := ((f.comp ·)^[r - i] X).eval 0 with hc
  have hcomp : ((f.comp ·)^[r] X) = (((f.comp ·)^[r - i] X)).comp (((f.comp ·)^[i] X)) := by
    have h := comp_iterate_add f (r - i) i
    rwa [Nat.sub_add_cancel hir] at h
  have hQ : ((f.comp ·)^[r - i] X) = C c + X * V := by linear_combination hV
  refine ⟨V.comp ((f.comp ·)^[i] X), ?_⟩
  rw [hcomp, hQ, add_comp, mul_comp, C_comp, X_comp]
  ring

/-- **The critical orbit is periodic modulo `q`** once it hits `0`: if `q ∣ c m` then
`c (j + m) ≡ c j` for every `j`, since the orbit is generated by iterating `f`. -/
theorem dvd_eval_zero_comp_iterate_add {R : Type*} [CommRing R] {f : R[X]} {q : R} {m : ℕ}
    (hm : q ∣ ((f.comp ·)^[m] X).eval 0) (j : ℕ) :
    q ∣ ((f.comp ·)^[j + m] X).eval 0 - ((f.comp ·)^[j] X).eval 0 := by
  have hstep : ∀ t : ℕ, ((f.comp ·)^[t + 1] X).eval 0 =
      f.eval (((f.comp ·)^[t] X).eval 0) := by
    intro t
    rw [Function.iterate_succ_apply', eval_comp]
  induction j with
  | zero => simpa using hm
  | succ j ih =>
    rw [show j + 1 + m = (j + m) + 1 by omega, hstep, hstep]
    exact ih.trans (sub_dvd_eval_sub _ _ f)

variable {f : ℤ[X]} {A : ℤ} {b : ℕ}

/-- `X ^ b` divides `Q (m + 1) - C (c (m + 1))`: the orbit starts at `0`, which is a
critical point of `X ^ b + 1` of order `b`. -/
theorem X_pow_dvd_comp_iterate_succ_sub_C {R : Type*} [CommRing R] {f : R[X]} {A : R}
    (hf : f = X ^ b + C A) (hb : 0 < b) (m : ℕ) :
    (X : R[X]) ^ b ∣ ((f.comp ·)^[m + 1] X) -
      C (((f.comp ·)^[m + 1] X).eval 0) := by
  induction m with
  | zero =>
    rw [comp_iterate_succ_eq hf]
    simp [zero_pow hb.ne']
  | succ m ih =>
    rw [comp_iterate_succ_eq hf, eval_add, eval_pow, eval_C, map_add, map_pow,
      show ((((f.comp ·)^[m + 1] X)) ^ b + C A -
        ((C (((f.comp ·)^[m + 1] X).eval 0)) ^ b + C A)) =
        ((f.comp ·)^[m + 1] X) ^ b -
          (C (((f.comp ·)^[m + 1] X).eval 0)) ^ b by ring]
    exact ih.trans (sub_dvd_pow_sub_pow _ _ b)

/-- **The splitting that decides everything**: for `1 ≤ m ≤ r`,
`Q r = C (c m) + Q (r - m) ^ b * W`. -/
theorem comp_iterate_eq_C_add_pow_mul {R : Type*} [CommRing R] {f : R[X]} {A : R}
    (hf : f = X ^ b + C A) (hb : 0 < b) {m r : ℕ} (hm : 0 < m) (hmr : m ≤ r) :
    ∃ W : R[X], ((f.comp ·)^[r] X) =
      C (((f.comp ·)^[m] X).eval 0) +
        ((f.comp ·)^[r - m] X) ^ b * W := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨V, hV⟩ := X_pow_dvd_comp_iterate_succ_sub_C hf hb m'
  set c : R := ((f.comp ·)^[m' + 1] X).eval 0 with hc
  have hcomp : ((f.comp ·)^[r] X) =
      ((f.comp ·)^[m' + 1] X).comp
        ((f.comp ·)^[r - (m' + 1)] X) := by
    have h := comp_iterate_add f (m' + 1) (r - (m' + 1))
    rwa [show m' + 1 + (r - (m' + 1)) = r by omega] at h
  have hQ : ((f.comp ·)^[m' + 1] X) = C c + X ^ b * V := by
    linear_combination hV
  exact ⟨V.comp ((f.comp ·)^[r - (m' + 1)] X), by
    rw [hcomp, hQ, add_comp, mul_comp, C_comp, pow_comp, X_comp]⟩

/-! ### The sharp criterion at an odd prime -/

variable {q : ℕ}

/-- **Sufficiency.**  Let `m` be the *first* index whose constant term `c m` is divisible by
`q`.  If `q ^ 2` does not divide `c m`, then `q` is not an index divisor of any iterate.

Suppose `Q r ∈ ⟨q, Pi⟩ ^ 2`.  Then `Pi` divides the reduction of `Q r` twice, hence divides
its derivative, hence — by the chain rule and `q ∤ b` — divides some `Q i` with `i < r`.
Since `Q r ≡ c (r - i)` mod `Q i`, that forces `q ∣ c (r - i)`; minimality of `m` gives
`m ≤ r - i` and periodicity gives `q ∣ c (r - i - m)`, so `Pi` divides the reduction of
`Q (r - m)` as well.  Now `Q (r - m) ^ b ∈ ⟨q, Pi⟩ ^ 2` because `b ≥ 2`, so the splitting
`Q r = C (c m) + Q (r - m) ^ b * W` puts the constant `C (c m)` in `⟨q, Pi⟩ ^ 2`, which
forces `q ^ 2 ∣ c m`. -/
theorem not_isIndexDivisor_comp_iterate_of_not_sq_dvd (hf : f = X ^ b + C A) (hb : 2 ≤ b)
    [hq : Fact q.Prime]
    (hqb : ¬ q ∣ b) {r m : ℕ} (hm : 0 < m) (hmr : m ≤ r)
    (hdvd : (q : ℤ) ∣ ((f.comp ·)^[m] X).eval 0)
    (hsq : ¬ (q : ℤ) ^ 2 ∣ ((f.comp ·)^[m] X).eval 0)
    (hmin : ∀ j, 0 < j → j < m →
      ¬ (q : ℤ) ∣ ((f.comp ·)^[j] X).eval 0) :
    ¬ IsIndexDivisor q ((f.comp ·)^[r] X) := by
  rintro ⟨Pi, hPim, hPiirr, hmem⟩
  have hPi0 : Pi.map (Int.castRingHom (ZMod q)) ≠ 0 := hPiirr.ne_zero
  -- The reduction of `Pi` divides that of `Q r` twice.
  have hdvd2 : (Pi.map (Int.castRingHom (ZMod q))) ^ 2 ∣
      ((f.comp ·)^[r] X).map (Int.castRingHom (ZMod q)) := by
    have h := sq_span_pair_le_span_pair_sq hmem
    rwa [mem_span_pair_C_natCast_iff, Polynomial.map_pow] at h
  have hPiQr : (Pi.map (Int.castRingHom (ZMod q))) ∣
      ((f.comp ·)^[r] X).map (Int.castRingHom (ZMod q)) :=
    (dvd_pow_self _ two_ne_zero).trans hdvd2
  -- Hence it divides the derivative, hence some member of the orbit.
  have hPider : (Pi.map (Int.castRingHom (ZMod q))) ∣
      derivative (((f.comp ·)^[r] X).map (Int.castRingHom (ZMod q))) := by
    obtain ⟨g, hg⟩ := hdvd2
    refine ⟨C 2 * derivative (Pi.map (Int.castRingHom (ZMod q))) * g +
      (Pi.map (Int.castRingHom (ZMod q))) * derivative g, ?_⟩
    rw [hg, derivative_mul, derivative_pow]
    ring
  have hbne : ((b : ℤ) : ZMod q) ≠ 0 := fun h =>
    hqb ((CharP.cast_eq_zero_iff (ZMod q) q b).mp (by exact_mod_cast h))
  have hif : ∀ i : ℕ, ((derivative f).comp
        ((f.comp ·)^[i] X)).map (Int.castRingHom (ZMod q)) =
      C ((b : ℤ) : ZMod q) *
        (((f.comp ·)^[i] X).map (Int.castRingHom (ZMod q))) ^ (b - 1) := by
    intro i
    rw [hf, derivative_add, derivative_C, add_zero, derivative_X_pow, mul_comp, C_comp,
      pow_comp, X_comp]
    simp
  obtain ⟨i, hiR, hPiQi⟩ : ∃ i, i < r ∧ (Pi.map (Int.castRingHom (ZMod q))) ∣
      ((f.comp ·)^[i] X).map (Int.castRingHom (ZMod q)) := by
    rw [derivative_map, derivative_comp_iterate, Polynomial.map_prod] at hPider
    obtain ⟨i, hi, hdvdi⟩ := ((hPiirr.prime).dvd_finsetProd_iff _).mp hPider
    refine ⟨i, Finset.mem_range.mp hi, ?_⟩
    rw [hif i] at hdvdi
    rcases (hPiirr.prime).dvd_mul.mp hdvdi with h | h
    · exact absurd (isUnit_of_dvd_unit h (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hbne)))
        hPiirr.not_isUnit
    · exact (hPiirr.prime).dvd_of_dvd_pow h
  -- Being a common factor of `Q i` and `Q r` forces `q ∣ c (r - i)`.
  have hCdvd : ∀ s : ℕ, i ≤ s →
      (Pi.map (Int.castRingHom (ZMod q))) ∣
        ((f.comp ·)^[s] X).map (Int.castRingHom (ZMod q)) -
        C ((((f.comp ·)^[s - i] X).eval 0 : ℤ) : ZMod q) := by
    intro s hs
    refine hPiQi.trans ?_
    have h := Polynomial.map_dvd (Int.castRingHom (ZMod q))
      (comp_iterate_dvd_sub_C f hs)
    simpa using h
  have hqc : (q : ℤ) ∣ ((f.comp ·)^[r - i] X).eval 0 := by
    by_contra hno
    have hne : (((((f.comp ·)^[r - i] X).eval 0 : ℤ)) : ZMod q) ≠ 0 :=
      fun h => hno ((ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp h)
    have hCc := (hPiQr.sub (hCdvd r hiR.le))
    rw [sub_sub_cancel] at hCc
    exact hPiirr.not_isUnit
      (isUnit_of_dvd_unit hCc (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hne)))
  -- Minimality and periodicity move the divisibility down by `m`.
  have htm : m ≤ r - i := by
    by_contra h
    exact hmin (r - i) (by omega) (by omega) hqc
  have hqtm : (q : ℤ) ∣ ((f.comp ·)^[r - i - m] X).eval 0 := by
    have h := dvd_eval_zero_comp_iterate_add (f := f) hdvd (r - i - m)
    rw [show r - i - m + m = r - i by omega] at h
    have h2 := hqc.sub h
    rwa [sub_sub_cancel] at h2
  have hPirm : (Pi.map (Int.castRingHom (ZMod q))) ∣
      ((f.comp ·)^[r - m] X).map (Int.castRingHom (ZMod q)) := by
    have h := hCdvd (r - m) (by omega)
    rw [show r - m - i = r - i - m by omega,
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hqtm, map_zero, sub_zero] at h
    exact h
  -- The `b`-th power lands in the square of the ideal, so the constant term must too.
  have hmemb : ((f.comp ·)^[r - m] X) ^ b ∈
      (Ideal.span {C (q : ℤ), Pi} : Ideal ℤ[X]) ^ 2 :=
    Ideal.pow_le_pow_right hb (Ideal.pow_mem_pow (mem_span_pair_C_natCast_iff.mpr hPirm) b)
  obtain ⟨W, hW⟩ := comp_iterate_eq_C_add_pow_mul hf (by omega) hm hmr
  obtain ⟨c, hc⟩ := hdvd
  have hqc' : ¬ (q : ℤ) ∣ c := fun ⟨d, hd⟩ => hsq ⟨d, by rw [hc, hd]; ring⟩
  have hCm : C (q : ℤ) * C c ∈ (Ideal.span {C (q : ℤ), Pi} : Ideal ℤ[X]) ^ 2 := by
    have heq : C (q : ℤ) * C c =
        ((f.comp ·)^[r] X) -
          ((f.comp ·)^[r - m] X) ^ b * W := by
      rw [← map_mul, ← hc]
      linear_combination -hW
    rw [heq]
    exact Ideal.sub_mem _ hmem (Ideal.mul_mem_right _ _ hmemb)
  have hCcmem := mem_span_pair_of_C_mul_mem_sq hPi0 hCm
  rw [mem_span_pair_C_natCast_iff, Polynomial.map_C] at hCcmem
  have hcne : ((c : ℤ) : ZMod q) ≠ 0 := fun h =>
    hqc' ((ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp h)
  exact hPiirr.not_isUnit
    (isUnit_of_dvd_unit hCcmem (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcne)))

/-- **Necessity.**  If `q ^ 2` divides some `c m` with `1 ≤ m ≤ r`, then `q` *is* an index
divisor of `Q r`: take `Pi` to be any monic irreducible factor of the reduction of
`Q (r - m)`.  Then `Q (r - m) ^ b ∈ ⟨q, Pi⟩ ^ 2` because `b ≥ 2`, while
`C (c m) ∈ ⟨q⟩ ^ 2 ⊆ ⟨q, Pi⟩ ^ 2`, so the splitting
`Q r = C (c m) + Q (r - m) ^ b * W` puts `Q r` itself in `⟨q, Pi⟩ ^ 2`. -/
theorem isIndexDivisor_comp_iterate_of_sq_dvd (hf : f = X ^ b + C A) (hb : 2 ≤ b)
    [hq : Fact q.Prime] {r m : ℕ}
    (hm : 0 < m) (hmr : m ≤ r)
    (hsq : (q : ℤ) ^ 2 ∣ ((f.comp ·)^[m] X).eval 0) :
    IsIndexDivisor q ((f.comp ·)^[r] X) := by
  have hb0 : 0 < b := by omega
  have hfm : f.Monic := by
    rw [hf]; exact monic_X_pow_add_C A hb0.ne'
  have hfd : f.natDegree = b := by
    rw [hf]; exact natDegree_X_pow_add_C
  -- The reduction of `Q (r - m)` is monic of positive degree, so it has a monic irreducible
  -- factor.
  have hQm : ((f.comp ·)^[r - m] X).Monic :=
    monic_comp_iterate hfm (by omega) (r - m)
  have hQdeg : (((f.comp ·)^[r - m] X).map
      (Int.castRingHom (ZMod q))).natDegree = b ^ (r - m) := by
    rw [hQm.natDegree_map, natDegree_comp_iterate, hfd]
  have hQne : (((f.comp ·)^[r - m] X).map (Int.castRingHom (ZMod q))) ≠ 0 :=
    (hQm.map _).ne_zero
  have hQnu : ¬ IsUnit ((((f.comp ·)^[r - m] X)).map
      (Int.castRingHom (ZMod q))) := by
    intro hu
    have hz := natDegree_eq_zero_of_isUnit hu
    rw [hQdeg] at hz
    have hpos : 0 < b ^ (r - m) := by positivity
    omega
  obtain ⟨i, hi, hidvd⟩ := WfDvdMonoid.exists_irreducible_factor hQnu hQne
  have hπirr : Irreducible (normalize i) := (normalize_associated i).symm.irreducible hi
  have hπm : (normalize i).Monic := monic_normalize hi.ne_zero
  have hπdvd : (normalize i) ∣ ((f.comp ·)^[r - m] X).map
      (Int.castRingHom (ZMod q)) := (normalize_associated i).dvd.trans hidvd
  -- Lift it to a monic polynomial over `ℤ`.
  have hsurj : Function.Surjective (Int.castRingHom (ZMod q)) := ZMod.intCast_surjective
  obtain ⟨Pi, hPimap, -, hPimonic⟩ :=
    lifts_and_degree_eq_and_monic ((mem_lifts _).mpr
      (Polynomial.map_surjective _ hsurj (normalize i))) hπm
  refine ⟨Pi, hPimonic, by rw [hPimap]; exact hπirr, ?_⟩
  -- Both summands of the splitting lie in the square of the ideal.
  have hmem1 : ((f.comp ·)^[r - m] X) ∈
      (Ideal.span {C (q : ℤ), Pi} : Ideal ℤ[X]) :=
    mem_span_pair_C_natCast_iff.mpr (by rw [hPimap]; exact hπdvd)
  have hmemb : ((f.comp ·)^[r - m] X) ^ b ∈
      (Ideal.span {C (q : ℤ), Pi} : Ideal ℤ[X]) ^ 2 :=
    Ideal.pow_le_pow_right hb (Ideal.pow_mem_pow hmem1 b)
  obtain ⟨d, hd⟩ := hsq
  have hmemC : C (((f.comp ·)^[m] X).eval 0) ∈
      (Ideal.span {C (q : ℤ), Pi} : Ideal ℤ[X]) ^ 2 := by
    have hCq : (C (q : ℤ) : ℤ[X]) ∈ (Ideal.span {C (q : ℤ), Pi} : Ideal ℤ[X]) :=
      Ideal.subset_span (by simp)
    have heq : C (((f.comp ·)^[m] X).eval 0) = C (q : ℤ) ^ 2 * C d := by
      rw [← map_pow, ← map_mul, ← hd]
    rw [heq]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hCq 2)
  obtain ⟨W, hW⟩ := comp_iterate_eq_C_add_pow_mul hf hb0 hm hmr
  rw [hW]
  exact Ideal.add_mem _ hmemC (Ideal.mul_mem_right _ _ hmemb)

/-- **The sharp criterion at an odd prime.**  `q` is an index divisor of the `r`-fold
iterate of `X ^ b + 1` exactly when the critical orbit meets `q` within the first `r` steps
*and* does so to order at least two at the first such step.

So the only obstruction to monogenity is a square factor at the first point where the orbit
falls into `q`; a first hit that is exactly divisible by `q` is harmless. -/
theorem isIndexDivisor_comp_iterate_iff (hf : f = X ^ b + C A) (hb : 2 ≤ b) [Fact q.Prime]
    (hqb : ¬ q ∣ b) (r : ℕ) :
    IsIndexDivisor q ((f.comp ·)^[r] X) ↔
      ∃ m, 0 < m ∧ m ≤ r ∧ (q : ℤ) ^ 2 ∣ ((f.comp ·)^[m] X).eval 0 ∧
        ∀ j, 0 < j → j < m →
          ¬ (q : ℤ) ∣ ((f.comp ·)^[j] X).eval 0 := by
  classical
  refine ⟨fun hidx => ?_, ?_⟩
  · by_contra hno
    push Not at hno
    by_cases hex : ∃ j, 0 < j ∧ j ≤ r ∧ (q : ℤ) ∣ ((f.comp ·)^[j] X).eval 0
    · -- The orbit meets `q`; take the first time it does.
      obtain ⟨j₀, hj₀0, hj₀r, hj₀d⟩ := hex
      have hP : ∃ j, 0 < j ∧ (q : ℤ) ∣ ((f.comp ·)^[j] X).eval 0 :=
        ⟨j₀, hj₀0, hj₀d⟩
      set m := Nat.find hP with hmdef
      obtain ⟨hm0, hmd⟩ := Nat.find_spec hP
      have hmmin : ∀ j, 0 < j → j < m →
          ¬ (q : ℤ) ∣ ((f.comp ·)^[j] X).eval 0 := by
        intro j hj0 hjm hjd
        exact Nat.find_min hP hjm ⟨hj0, hjd⟩
      have hmr : m ≤ r := le_trans (Nat.find_le ⟨hj₀0, hj₀d⟩) hj₀r
      have hnsq : ¬ (q : ℤ) ^ 2 ∣ ((f.comp ·)^[m] X).eval 0 := by
        intro h
        obtain ⟨j, hj0, hjm, hjd⟩ := hno m hm0 hmr h
        exact hmmin j hj0 hjm hjd
      exact not_isIndexDivisor_comp_iterate_of_not_sq_dvd hf hb hqb hm0 hmr hmd hnsq hmmin hidx
    · -- The orbit misses `q` entirely, so the reduction is separable.
      push Not at hex
      exact not_isIndexDivisor_comp_iterate_of_not_dvd_orbit hf hqb
        (fun j hj0 hjr => hex j hj0 hjr) hidx
  · rintro ⟨m, hm, hmr, hsq, -⟩
    exact isIndexDivisor_comp_iterate_of_sq_dvd hf hb hm hmr hsq

end CriticalOrbit

end Polynomial

namespace Polynomial

/-! ### Monogenity of an even iterate, with the sharp hypothesis -/

/-- **Monogenity of an even iterate of `Φ (2 ^ (k + 1))`, sharply.**  No prime is an index
divisor of the `(r + 1)`-fold iterate, `r` odd, provided that at every odd prime `q` the
critical orbit's *first* hit is exactly divisible by `q`.

Compared with `forall_not_isIndexDivisor_comp_iterate`, whose hypothesis asks that no odd
prime meet the orbit at all — and is therefore vacuous beyond the second iterate, since
`c 3 = 2 ^ (2 ^ k) + 1` is odd and greater than one — this asks only that the first hit not
be a square.  By `isIndexDivisor_comp_iterate_iff` the hypothesis cannot be weakened. -/
theorem forall_not_isIndexDivisor_comp_iterate_of_first_hit {k : ℕ} (hk : 0 < k) {r : ℕ}
    (hr : Odd r)
    (horb : ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ m, 0 < m → m ≤ r + 1 →
      (∀ j, 0 < j → j < m →
        ¬ (q : ℤ) ∣ ((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[j] X).eval 0) →
      ¬ (q : ℤ) ^ 2 ∣ ((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[m] X).eval 0) :
    ∀ q : ℕ, q.Prime →
      ¬ IsIndexDivisor q ((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[r + 1] X) := by
  have hb2 : 2 ≤ 2 ^ k := by simpa using Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hk
  intro q hqp
  haveI : Fact q.Prime := ⟨hqp⟩
  by_cases hq2 : q = 2
  · subst hq2
    exact not_isIndexDivisor_two_comp_iterate hk hr
  · have hqb : ¬ q ∣ 2 ^ k := fun hdvd =>
      hq2 ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow hdvd))
    intro hidx
    obtain ⟨m, hm0, hmr, hsq, hmin⟩ :=
      (isIndexDivisor_comp_iterate_iff (A := 1) rfl hb2 hqb _).mp hidx
    exact horb q hqp hq2 m hm0 hmr hmin hsq

/-- **Monogenity of an even iterate from a squarefree critical orbit.**  This is the
practical form: if the first `r + 1` values of the critical orbit are squarefree integers,
then the `(r + 1)`-fold iterate of `Φ (2 ^ (k + 1))` is monogenic.

For `k = 1` the orbit is `1, 2, 5, 26, 677, 458330, …`, all squarefree so far, so every even
iterate whose orbit has been checked is monogenic. -/
theorem forall_not_isIndexDivisor_comp_iterate_of_squarefree {k : ℕ} (hk : 0 < k) {r : ℕ}
    (hr : Odd r)
    (hsf : ∀ m, 0 < m → m ≤ r + 1 →
      Squarefree (((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[m] X).eval 0)) :
    ∀ q : ℕ, q.Prime →
      ¬ IsIndexDivisor q ((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[r + 1] X) :=
  forall_not_isIndexDivisor_comp_iterate_of_first_hit hk hr
    fun q hqp _ m hm0 hmr _ =>
      Int.squarefree_iff_forall_prime_sq_not_dvd.mp (hsf m hm0 hmr) q hqp

end Polynomial

namespace NumberField

open Polynomial

/-- **Monogenity of an even iterate of a `2`-power cyclotomic polynomial, sharply.**  If `θ`
generates `K` over `ℚ` and its minimal polynomial is the `(r + 1)`-fold iterate of
`Φ (2 ^ (k + 1)) = X ^ (2 ^ k) + 1` with `r` odd, and the critical orbit's first hit at each
odd prime is exactly divisible by that prime, then `ℤ[θ] = 𝓞 K`. -/
theorem adjoin_eq_top_of_minpoly_eq_comp_iterate_of_first_hit {K : Type*} [Field K]
    [NumberField K] {θ : 𝓞 K} {k r : ℕ} (hk : 0 < k) (hr : Odd r)
    (hθ : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hmin : minpoly ℤ θ = (((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[r + 1] X)
    (horb : ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ m, 0 < m → m ≤ r + 1 →
      (∀ j, 0 < j → j < m →
        ¬ (q : ℤ) ∣ ((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[j] X).eval 0) →
      ¬ (q : ℤ) ^ 2 ∣ ((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[m] X).eval 0) :
    Algebra.adjoin ℤ {θ} = ⊤ := by
  rw [← RingOfIntegers.forall_not_isIndexDivisor_iff_adjoin_eq_top hθ, hmin]
  exact forall_not_isIndexDivisor_comp_iterate_of_first_hit hk hr horb

/-- **Monogenity of an even iterate from a squarefree critical orbit.** -/
theorem adjoin_eq_top_of_minpoly_eq_comp_iterate_of_squarefree {K : Type*} [Field K]
    [NumberField K] {θ : 𝓞 K} {k r : ℕ} (hk : 0 < k) (hr : Odd r)
    (hθ : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hmin : minpoly ℤ θ = (((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[r + 1] X)
    (hsf : ∀ m, 0 < m → m ≤ r + 1 →
      Squarefree (((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[m] X).eval 0)) :
    Algebra.adjoin ℤ {θ} = ⊤ := by
  rw [← RingOfIntegers.forall_not_isIndexDivisor_iff_adjoin_eq_top hθ, hmin]
  exact forall_not_isIndexDivisor_comp_iterate_of_squarefree hk hr hsf

end NumberField

namespace Polynomial

/-! ### The criterion in its simplest form

The minimality clause in `isIndexDivisor_comp_iterate_iff` can be dropped: the necessity
half needs no minimality, so being an index divisor is equivalent to the plain statement
that `q ^ 2` divides *some* member of the critical orbit. -/

/-- **The criterion, simplified.**  A prime `q` not dividing `b` is an index divisor of the
`r`-fold iterate of `X ^ b + 1` exactly when `q ^ 2` divides one of the first `r` values of
the critical orbit. -/
theorem isIndexDivisor_comp_iterate_iff_exists_sq_dvd {f : ℤ[X]} {A : ℤ} {b q : ℕ}
    (hf : f = X ^ b + C A) (hb : 2 ≤ b) [Fact q.Prime] (hqb : ¬ q ∣ b) (r : ℕ) :
    IsIndexDivisor q ((f.comp ·)^[r] X) ↔
      ∃ m, 0 < m ∧ m ≤ r ∧
        (q : ℤ) ^ 2 ∣ ((f.comp ·)^[m] X).eval 0 := by
  refine ⟨fun h => ?_,
    fun ⟨m, h1, h2, h3⟩ => isIndexDivisor_comp_iterate_of_sq_dvd hf hb h1 h2 h3⟩
  obtain ⟨m, h1, h2, h3, -⟩ := (isIndexDivisor_comp_iterate_iff hf hb hqb r).mp h
  exact ⟨m, h1, h2, h3⟩

/-- **The complete answer for even iterates.**  For `r` odd and `k ≥ 1`, the `(r + 1)`-fold
iterate of `Φ (2 ^ (k + 1)) = X ^ (2 ^ k) + 1` is monogenic **if and only if** the first
`r + 1` values of the critical orbit `c m = Q m (0)` are squarefree integers.

Both directions come from `isIndexDivisor_comp_iterate_of_sq_dvd` and
`isIndexDivisor_comp_iterate_iff`; the prime `2` never obstructs, since an even iterate is
`2`-Eisenstein, consistent with the fact that `4` divides no member of the orbit. -/
theorem forall_not_isIndexDivisor_comp_iterate_iff_squarefree {k : ℕ} (hk : 0 < k) {r : ℕ}
    (hr : Odd r) :
    (∀ q : ℕ, q.Prime → ¬ IsIndexDivisor q ((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[r + 1] X)) ↔
      ∀ m, 0 < m → m ≤ r + 1 →
        Squarefree (((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[m] X).eval 0) := by
  have hb2 : 2 ≤ 2 ^ k := by simpa using Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hk
  refine ⟨fun h m hm0 hmr => ?_, forall_not_isIndexDivisor_comp_iterate_of_squarefree hk hr⟩
  rw [Int.squarefree_iff_forall_prime_sq_not_dvd]
  intro q hqp hsq
  haveI : Fact q.Prime := ⟨hqp⟩
  exact h q hqp (isIndexDivisor_comp_iterate_of_sq_dvd (A := 1) rfl hb2 hm0 hmr hsq)

end Polynomial

namespace NumberField

open Polynomial

/-- **Monogenity of an even iterate of a `2`-power cyclotomic polynomial, exactly.**  If `θ`
generates `K` over `ℚ` and its minimal polynomial is the `(r + 1)`-fold iterate of
`Φ (2 ^ (k + 1))` with `r` odd, then `ℤ[θ] = 𝓞 K` **if and only if** the first `r + 1`
values of the critical orbit are squarefree. -/
theorem adjoin_eq_top_iff_forall_squarefree_of_minpoly_eq_comp_iterate {K : Type*} [Field K]
    [NumberField K] {θ : 𝓞 K} {k r : ℕ} (hk : 0 < k) (hr : Odd r)
    (hθ : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hmin : minpoly ℤ θ = (((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[r + 1] X) :
    Algebra.adjoin ℤ {θ} = ⊤ ↔
      ∀ m, 0 < m → m ≤ r + 1 →
        Squarefree (((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[m] X).eval 0) := by
  rw [← RingOfIntegers.forall_not_isIndexDivisor_iff_adjoin_eq_top hθ, hmin]
  exact forall_not_isIndexDivisor_comp_iterate_iff_squarefree hk hr

end NumberField

namespace Polynomial

/-! ### Removing the parity hypothesis

The results above treat even iterates, which are Eisenstein at `2` outright.  An odd iterate
is not: its constant term is odd.  But its *translate* by `1` is, because `Q r (1) = c (r + 1)`
is the next member of the orbit, which for `r` odd sits at an even index and so is exactly
divisible by `2`.  Since index divisors are invariant under `X ↦ X + c`, this disposes of the
odd case too, and the parity hypothesis disappears from every statement. -/

section Translate

/-- Index divisors are unchanged by the translation `X ↦ X + c`: the substitution is a ring
automorphism of `ℤ[X]` fixing `C p`, so it carries the ideal `⟨p, Pi⟩` to `⟨p, Pi (X + c)⟩`
and preserves monicity and irreducibility of reductions. -/
private theorem isIndexDivisor_comp_X_add_C_of {p : ℕ} [Fact p.Prime] {g : ℤ[X]} (c : ℤ)
    (h : IsIndexDivisor p g) : IsIndexDivisor p (g.comp (X + C c)) := by
  obtain ⟨Pi, hPim, hPiirr, hmem⟩ := h
  have he : ∀ u : (ZMod p)[X],
      (Polynomial.algEquivAevalXAddC (((c : ℤ) : ZMod p))) u =
        u.comp (X + C ((c : ℤ) : ZMod p)) := by
    intro u
    simp [Polynomial.algEquivAevalXAddC, Polynomial.aeval_def, Polynomial.comp]
  refine ⟨Pi.comp (X + C c), hPim.comp_X_add_C c, ?_, ?_⟩
  · have hmapc : ((X + C c : ℤ[X]).map (Int.castRingHom (ZMod p))) =
        X + C ((c : ℤ) : ZMod p) := by
      rw [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, Int.coe_castRingHom]
    rw [Polynomial.map_comp, hmapc, ← he]
    exact (MulEquiv.irreducible_iff
      (Polynomial.algEquivAevalXAddC (((c : ℤ) : ZMod p))).toMulEquiv).mpr hPiirr
  · obtain ⟨u, v, w, huvw⟩ := Ideal.mem_span_pair_sq_iff.mp hmem
    refine Ideal.mem_span_pair_sq_iff.mpr
      ⟨u.comp (X + C c), v.comp (X + C c), w.comp (X + C c), ?_⟩
    rw [huvw]
    simp [add_comp, mul_comp, pow_comp]

/-- **Index divisors are a translation invariant.** -/
theorem isIndexDivisor_comp_X_add_C_iff {p : ℕ} [Fact p.Prime] (g : ℤ[X]) (c : ℤ) :
    IsIndexDivisor p (g.comp (X + C c)) ↔ IsIndexDivisor p g := by
  refine ⟨fun h => ?_, isIndexDivisor_comp_X_add_C_of c⟩
  have h2 := isIndexDivisor_comp_X_add_C_of (-c) h
  rwa [comp_assoc, show ((X : ℤ[X]) + C c).comp (X + C (-c)) = X by
    simp [add_comp], comp_X] at h2

end Translate

section OddIterate

variable {b k : ℕ}

/-- Evaluating an iterate at `1` shifts the critical orbit by one step:
`Q r (1) = c (r + 1)`, because `1 = f (0) = c 1`. -/
theorem eval_one_comp_iterate (hb : 0 < b) (r : ℕ) :
    ((((X ^ b + 1 : ℤ[X])).comp ·)^[r] X).eval 1 =
      ((((X ^ b + 1 : ℤ[X])).comp ·)^[r + 1] X).eval 0 := by
  have h := comp_iterate_add (X ^ b + 1 : ℤ[X]) r 1
  rw [h, eval_comp]
  congr 1
  rw [show (1 : ℕ) = 0 + 1 from rfl, comp_iterate_pow_add_one_succ]
  simp [zero_pow hb.ne']

/-- **An odd iterate becomes Eisenstein at `2` after translating by `1`.**  Its reduction
mod `2` is `X ^ (b ^ r) + 1 = (X + 1) ^ (b ^ r)`, which the translation turns into a
monomial, and its constant term becomes `Q r (1) = c (r + 1)`, exactly divisible by `2`
since `r + 1` is even. -/
theorem isEisensteinAt_two_comp_iterate_comp_X_add_one (hk : 0 < k) {r : ℕ} (hr : Odd r) :
    ((((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[r] X)).comp (X + C 1)).IsEisensteinAt
      (Submodule.span ℤ {(2 : ℤ)}) := by
  have hb : 0 < 2 ^ k := by positivity
  have hbe : Even (2 ^ k) := (Nat.even_pow' hk.ne').mpr even_two
  have hfm : ((X ^ 2 ^ k + 1 : ℤ[X])).Monic := by
    simpa using monic_X_pow_add_C (1 : ℤ) hb.ne'
  have hfd : ((X ^ 2 ^ k + 1 : ℤ[X])).natDegree = 2 ^ k := by
    simpa using natDegree_X_pow_add_C (R := ℤ) (n := 2 ^ k) (r := 1)
  have hQmonic := monic_comp_iterate hfm (by omega) r
  have hmonic := hQmonic.comp_X_add_C (1 : ℤ)
  have hdeg : (((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[r] X).comp (X + C 1)).natDegree =
      (2 ^ k) ^ r := by
    rw [natDegree_comp, natDegree_X_add_C, mul_one, natDegree_comp_iterate, hfd]
  -- The reduction mod `2` is a monomial.
  have hmap : ((((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[r] X)).comp (X + C 1)).map
      (Int.castRingHom (ZMod 2)) = X ^ (2 ^ k) ^ r := by
    obtain ⟨t, ht⟩ := hr
    rw [Polynomial.map_comp, map_comp_iterate_zmod_two r]
    simp only [Polynomial.map_add, Polynomial.map_X, Polynomial.map_one, eq_intCast,
      Int.cast_one, add_comp, pow_comp, X_comp, C_comp]
    rw [show ((r : ℕ) : ZMod 2) = 1 by
      rw [ht, Nat.cast_add, Nat.cast_mul, show ((2 : ℕ) : ZMod 2) = 0 by decide]; ring]
    rw [show ((2 : ℕ) ^ k) ^ r = 2 ^ (k * r) by rw [← pow_mul], add_pow_char_pow, one_pow,
      add_assoc, C_1, CharTwo.add_self_eq_zero, add_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [hmonic.leadingCoeff, Ideal.mem_span_singleton]
    omega
  · intro i hi
    rw [hdeg] at hi
    have h := congrArg (fun u => Polynomial.coeff u i) hmap
    simp only [coeff_map, coeff_X_pow, Int.coe_castRingHom,
      if_neg (show i ≠ (2 ^ k) ^ r by omega)] at h
    rw [Ideal.mem_span_singleton]
    have h2 : ((2 : ℕ) : ℤ) ∣
        (((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[r] X).comp (X + C 1)).coeff i :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h
    simpa using h2
  · rw [coeff_zero_eq_eval_zero, eval_comp, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    simp only [eval_add, eval_X, eval_C, zero_add]
    rw [eval_one_comp_iterate hb r]
    intro hdvd
    exact not_four_dvd_eval_zero_comp_iterate hb hbe hr (by simpa using hdvd)

/-- **`2` is never an index divisor of an odd iterate either.** -/
theorem not_isIndexDivisor_two_comp_iterate_odd (hk : 0 < k) {r : ℕ} (hr : Odd r) :
    ¬ IsIndexDivisor 2 ((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[r] X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb : 0 < 2 ^ k := by positivity
  have hfm : ((X ^ 2 ^ k + 1 : ℤ[X])).Monic := by
    simpa using monic_X_pow_add_C (1 : ℤ) hb.ne'
  have hfd : ((X ^ 2 ^ k + 1 : ℤ[X])).natDegree = 2 ^ k := by
    simpa using natDegree_X_pow_add_C (R := ℤ) (n := 2 ^ k) (r := 1)
  rw [← isIndexDivisor_comp_X_add_C_iff _ (1 : ℤ)]
  refine RingOfIntegers.not_isIndexDivisor_of_isEisensteinAt
    ((monic_comp_iterate hfm (by omega) r).comp_X_add_C 1) ?_
    (isEisensteinAt_two_comp_iterate_comp_X_add_one hk hr)
  rw [natDegree_comp, natDegree_X_add_C, mul_one, natDegree_comp_iterate, hfd]
  positivity

/-- **`2` is never an index divisor of any iterate**, whatever the parity. -/
theorem not_isIndexDivisor_two_comp_iterate' (hk : 0 < k) {r : ℕ} (hr : 0 < r) :
    ¬ IsIndexDivisor 2 ((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[r] X) := by
  rcases Nat.even_or_odd r with he | ho
  · obtain ⟨t, ht⟩ := he
    have hto : Odd (t + t - 1) := by
      rcases Nat.eq_zero_or_pos t with rfl | h
      · omega
      · exact ⟨t - 1, by omega⟩
    have : r = (t + t - 1) + 1 := by omega
    rw [this]
    exact not_isIndexDivisor_two_comp_iterate hk hto
  · exact not_isIndexDivisor_two_comp_iterate_odd hk ho

/-- **The complete answer, with no parity hypothesis.**  For `k ≥ 1` and any `r ≥ 1`, the
`r`-fold iterate of `Φ (2 ^ (k + 1))` is monogenic **if and only if** the first `r` values of
the critical orbit are squarefree. -/
theorem forall_not_isIndexDivisor_comp_iterate_iff_squarefree' (hk : 0 < k) {r : ℕ}
    (hr : 0 < r) :
    (∀ q : ℕ, q.Prime → ¬ IsIndexDivisor q ((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[r] X)) ↔
      ∀ m, 0 < m → m ≤ r →
        Squarefree (((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[m] X).eval 0) := by
  have hb2 : 2 ≤ 2 ^ k := by simpa using Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hk
  refine ⟨fun h m hm0 hmr => ?_, fun h q hqp => ?_⟩
  · rw [Int.squarefree_iff_forall_prime_sq_not_dvd]
    intro q hqp hsq
    haveI : Fact q.Prime := ⟨hqp⟩
    exact h q hqp (isIndexDivisor_comp_iterate_of_sq_dvd (A := 1) rfl hb2 hm0 hmr hsq)
  · haveI : Fact q.Prime := ⟨hqp⟩
    by_cases hq2 : q = 2
    · subst hq2
      exact not_isIndexDivisor_two_comp_iterate' hk hr
    · have hqb : ¬ q ∣ 2 ^ k := fun hdvd =>
        hq2 ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow hdvd))
      intro hidx
      obtain ⟨m, hm0, hmr, hsq⟩ :=
        (isIndexDivisor_comp_iterate_iff_exists_sq_dvd (A := 1) rfl hb2 hqb _).mp hidx
      exact (Int.squarefree_iff_forall_prime_sq_not_dvd.mp (h m hm0 hmr)) q hqp hsq

end OddIterate

end Polynomial

namespace Polynomial

section AllIterates

variable {b k : ℕ}

/-- **Every iterate of `Φ (2 ^ (k + 1))` is irreducible over `ℤ`**: it is Eisenstein at `2`
for `r` even, and its translate by `1` is for `r` odd. -/
theorem irreducible_comp_iterate (hk : 0 < k) {r : ℕ} (hr : 0 < r) :
    Irreducible ((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[r] X) := by
  have hb : 0 < 2 ^ k := by positivity
  have hprime : Ideal.IsPrime (Submodule.span ℤ {(2 : ℤ)}) :=
    (Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_two
  have hfm : ((X ^ 2 ^ k + 1 : ℤ[X])).Monic := by
    simpa using monic_X_pow_add_C (1 : ℤ) hb.ne'
  have hfd : ((X ^ 2 ^ k + 1 : ℤ[X])).natDegree = 2 ^ k := by
    simpa using natDegree_X_pow_add_C (R := ℤ) (n := 2 ^ k) (r := 1)
  have hQmonic := monic_comp_iterate hfm (by omega) r
  have hQdeg : ((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[r] X).natDegree = (2 ^ k) ^ r := by
    rw [natDegree_comp_iterate, hfd]
  rcases Nat.even_or_odd r with he | ho
  · obtain ⟨t, ht⟩ := he
    have hto : Odd (t + t - 1) := by
      rcases Nat.eq_zero_or_pos t with rfl | h
      · omega
      · exact ⟨t - 1, by omega⟩
    have hrw : r = (t + t - 1) + 1 := by omega
    rw [hrw]
    refine (isEisensteinAt_two_comp_iterate hk hto).irreducible hprime
      (monic_comp_iterate hfm (by omega) _).isPrimitive ?_
    rw [natDegree_comp_iterate, hfd]
    positivity
  · -- Transfer irreducibility back along the translation `X ↦ X + 1`.
    have he1 : ∀ u : ℤ[X], (Polynomial.algEquivAevalXAddC (1 : ℤ)) u = u.comp (X + C 1) := by
      intro u
      simp [Polynomial.algEquivAevalXAddC, Polynomial.aeval_def, Polynomial.comp]
    refine (MulEquiv.irreducible_iff
      (Polynomial.algEquivAevalXAddC (1 : ℤ)).toMulEquiv).mp ?_
    rw [show ((Polynomial.algEquivAevalXAddC (1 : ℤ)).toMulEquiv
      ((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[r] X)) =
        ((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[r] X).comp (X + C 1) from he1 _]
    refine (isEisensteinAt_two_comp_iterate_comp_X_add_one hk ho).irreducible hprime
      (hQmonic.comp_X_add_C 1).isPrimitive ?_
    rw [natDegree_comp, natDegree_X_add_C, mul_one, hQdeg]
    positivity

/-- **A necessary condition with no hypotheses at all.**  If some iterate of `X ^ b + 1`
with `b ≥ 2` is monogenic, then the critical orbit is squarefree up to that point.  Note
that no assumption is made on `b` beyond `b ≥ 2`: the necessity half of the criterion needs
neither `q ∤ b` nor that `b` be a power of `2`. -/
theorem squarefree_eval_zero_of_forall_not_isIndexDivisor {f : ℤ[X]} {A : ℤ} {b : ℕ}
    (hf : f = X ^ b + C A) (hb : 2 ≤ b) {r : ℕ}
    (h : ∀ q : ℕ, q.Prime → ¬ IsIndexDivisor q ((f.comp ·)^[r] X)) :
    ∀ m, 0 < m → m ≤ r →
      Squarefree (((f.comp ·)^[m] X).eval 0) := by
  intro m hm0 hmr
  rw [Int.squarefree_iff_forall_prime_sq_not_dvd]
  intro q hqp hsq
  haveI : Fact q.Prime := ⟨hqp⟩
  exact h q hqp (isIndexDivisor_comp_iterate_of_sq_dvd hf hb hm0 hmr hsq)

end AllIterates

end Polynomial

namespace NumberField

open Polynomial

/-- **Monogenity of an arbitrary iterate of a `2`-power cyclotomic polynomial.**  If `θ`
generates `K` over `ℚ` and its minimal polynomial is the `r`-fold iterate of
`Φ (2 ^ (k + 1)) = X ^ (2 ^ k) + 1`, then `ℤ[θ] = 𝓞 K` **if and only if** the first `r`
values of the critical orbit are squarefree.  No parity hypothesis on `r` is needed. -/
theorem adjoin_eq_top_iff_forall_squarefree_of_minpoly_eq_comp_iterate' {K : Type*} [Field K]
    [NumberField K] {θ : 𝓞 K} {k r : ℕ} (hk : 0 < k) (hr : 0 < r)
    (hθ : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hmin : minpoly ℤ θ = (((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[r] X) :
    Algebra.adjoin ℤ {θ} = ⊤ ↔
      ∀ m, 0 < m → m ≤ r →
        Squarefree (((((X ^ 2 ^ k + 1 : ℤ[X])).comp ·)^[m] X).eval 0) := by
  rw [← RingOfIntegers.forall_not_isIndexDivisor_iff_adjoin_eq_top hθ, hmin]
  exact forall_not_isIndexDivisor_comp_iterate_iff_squarefree' hk hr

end NumberField

namespace Polynomial

/-! ### The criterion for a general unicritical polynomial

Nothing in the criterion used the constant term `1`.  The hypotheses are packaged as
`f = X ^ b + C A`, so the results apply verbatim to every *unicritical* polynomial: one whose
only critical point is `0`, of full multiplicity `b`.  This covers `X ^ b - A` as well, and
so the pure polynomials, whose iterates were not previously reachable. -/

/-- **The criterion for `X ^ b + A`.**  For a prime `q` not dividing `b`, `q` is an index
divisor of the `r`-fold iterate of `X ^ b + A` exactly when `q ^ 2` divides one of the first
`r` values of the critical orbit of `0`. -/
theorem isIndexDivisor_comp_iterate_pow_add_C_iff {b q : ℕ} (hb : 2 ≤ b) [Fact q.Prime]
    (hqb : ¬ q ∣ b) (A : ℤ) (r : ℕ) :
    IsIndexDivisor q ((((X ^ b + C A : ℤ[X])).comp ·)^[r] X) ↔
      ∃ m, 0 < m ∧ m ≤ r ∧
        (q : ℤ) ^ 2 ∣ ((((X ^ b + C A : ℤ[X])).comp ·)^[m] X).eval 0 :=
  isIndexDivisor_comp_iterate_iff_exists_sq_dvd rfl hb hqb r

/-- **The case `r = 1`**: a prime `q` not dividing `b` is an index divisor of `X ^ b + A`
exactly when `q ^ 2 ∣ A`.  The critical orbit has a single relevant term, `c 1 = A`. -/
theorem isIndexDivisor_pow_add_C_iff {b q : ℕ} (hb : 2 ≤ b) [Fact q.Prime] (hqb : ¬ q ∣ b)
    (A : ℤ) :
    IsIndexDivisor q ((X ^ b + C A : ℤ[X])) ↔ (q : ℤ) ^ 2 ∣ A := by
  have hone : ((((X ^ b + C A : ℤ[X])).comp ·)^[1] X) = X ^ b + C A := by
    rw [Function.iterate_one, comp_X]
  have heval : ((((X ^ b + C A : ℤ[X])).comp ·)^[1] X).eval 0 = A := by
    rw [hone, eval_add, eval_pow, eval_X, eval_C, zero_pow (by omega), zero_add]
  rw [← hone, isIndexDivisor_comp_iterate_pow_add_C_iff hb hqb A 1]
  refine ⟨fun ⟨m, hm0, hm1, hsq⟩ => ?_, fun h => ⟨1, one_pos, le_refl _, by rwa [heval]⟩⟩
  rw [show m = 1 by omega, heval] at hsq
  exact hsq

end Polynomial

namespace Monogenic

/-! ### The criterion over an arbitrary base

Everything above is stated over `ℤ`, but nothing in the argument is special to it.  The
proof uses only ideal calculus in `R[X]` and the fact that the residue ring `R ⧸ (π)` is a
field, so it goes through verbatim over any domain `R` and any element `π` generating a
maximal ideal — a Dedekind domain and a prime of it, in particular the ring of integers of a
number field, where the conclusion is *relative* monogenity.

The general statement replaces `Polynomial.IsIndexDivisor` by its definition, since that
notion is set up over `ℤ` only; by `Monogenic.mem_span_pair_iff_map_dvd` the two agree. -/

section IterateBase

attribute [local instance] Ideal.Quotient.field

open Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] {π : R}
  [hmax : (Ideal.span {π} : Ideal R).IsMaximal] {f : R[X]} {A : R} {b : ℕ}

/-- **The criterion over an arbitrary base, hard direction.**  If the `r`-fold iterate of
`f = X ^ b + A` lies in the square of a maximal ideal `⟨π, Pi⟩` of `R[X]`, then `π ^ 2`
divides one of the first `r` values of the critical orbit.

The proof is the one used over `ℤ`: `Pi` divides the reduction of the iterate twice, hence
its derivative, hence — by the chain rule and `π ∤ b` — some earlier member `Q i` of the
orbit; congruence `Q r ≡ c (r - i)` mod `Q i` then puts `π` into the orbit.  Taking the first
index `m` at which that happens and using periodicity mod `π`, `Pi` divides the reduction of
`Q (r - m)`, whose `b`-th power lies in `⟨π, Pi⟩ ^ 2` since `b ≥ 2`; the splitting
`Q r = C (c m) + Q (r - m) ^ b * W` then forces the constant `c m` into `⟨π, Pi⟩ ^ 2`, which
for a constant means exactly `π ^ 2 ∣ c m`. -/
theorem exists_sq_dvd_of_exists_mem_sq (hπ : Prime π) (hf : f = X ^ b + C A) (hb : 2 ≤ b)
    (hπb : ¬ π ∣ (b : R)) {r : ℕ}
    (h : ∃ Pi : R[X], Pi.Monic ∧
      Irreducible (Pi.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
      ((f.comp ·)^[r] X) ∈ (Ideal.span {C π, Pi} : Ideal (R[X])) ^ 2) :
    ∃ m, 0 < m ∧ m ≤ r ∧ π ^ 2 ∣ ((f.comp ·)^[m] X).eval 0 := by
  classical
  obtain ⟨Pi, hPim, hPiirr, hmem⟩ := h
  have hPi0 : Pi.map (Ideal.Quotient.mk (Ideal.span {π})) ≠ 0 := hPiirr.ne_zero
  -- `Pi` divides the reduction of the iterate twice.
  have hdvd2 : (Pi.map (Ideal.Quotient.mk (Ideal.span {π}))) ^ 2 ∣
      ((f.comp ·)^[r] X).map (Ideal.Quotient.mk (Ideal.span {π})) := by
    have h2 := sq_span_pair_le_span_pair_sq hmem
    rwa [mem_span_pair_iff_map_dvd, Polynomial.map_pow] at h2
  have hPiQr : (Pi.map (Ideal.Quotient.mk (Ideal.span {π}))) ∣
      ((f.comp ·)^[r] X).map (Ideal.Quotient.mk (Ideal.span {π})) :=
    (dvd_pow_self _ two_ne_zero).trans hdvd2
  have hPider : (Pi.map (Ideal.Quotient.mk (Ideal.span {π}))) ∣
      derivative (((f.comp ·)^[r] X).map (Ideal.Quotient.mk (Ideal.span {π}))) := by
    obtain ⟨g, hg⟩ := hdvd2
    refine ⟨C 2 * derivative (Pi.map (Ideal.Quotient.mk (Ideal.span {π}))) * g +
      (Pi.map (Ideal.Quotient.mk (Ideal.span {π}))) * derivative g, ?_⟩
    rw [hg, derivative_mul, derivative_pow]
    ring
  have hbne : (Ideal.Quotient.mk (Ideal.span {π})) (b : R) ≠ 0 := fun hz =>
    hπb (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))
  have hif : ∀ i : ℕ, ((derivative f).comp ((f.comp ·)^[i] X)).map
        (Ideal.Quotient.mk (Ideal.span {π})) =
      C ((Ideal.Quotient.mk (Ideal.span {π})) (b : R)) *
        (((f.comp ·)^[i] X).map (Ideal.Quotient.mk (Ideal.span {π}))) ^ (b - 1) := by
    intro i
    rw [hf, derivative_add, derivative_C, add_zero, derivative_X_pow, mul_comp, C_comp,
      pow_comp, X_comp]
    simp
  -- Hence `Pi` divides some earlier member of the orbit.
  obtain ⟨i, hiR, hPiQi⟩ : ∃ i, i < r ∧ (Pi.map (Ideal.Quotient.mk (Ideal.span {π}))) ∣
      (((f.comp ·)^[i] X).map (Ideal.Quotient.mk (Ideal.span {π}))) := by
    rw [derivative_map, derivative_comp_iterate, Polynomial.map_prod] at hPider
    obtain ⟨i, hi, hdvdi⟩ := ((hPiirr.prime).dvd_finsetProd_iff _).mp hPider
    refine ⟨i, Finset.mem_range.mp hi, ?_⟩
    rw [hif i] at hdvdi
    rcases (hPiirr.prime).dvd_mul.mp hdvdi with hu | hu
    · exact absurd (isUnit_of_dvd_unit hu (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hbne)))
        hPiirr.not_isUnit
    · exact (hPiirr.prime).dvd_of_dvd_pow hu
  -- A common factor of `Q i` and `Q r` puts `π` into the orbit.
  have hCdvd : ∀ s : ℕ, i ≤ s →
      (Pi.map (Ideal.Quotient.mk (Ideal.span {π}))) ∣
        ((f.comp ·)^[s] X).map (Ideal.Quotient.mk (Ideal.span {π})) -
        C ((Ideal.Quotient.mk (Ideal.span {π})) (((f.comp ·)^[s - i] X).eval 0)) := by
    intro s hs
    refine hPiQi.trans ?_
    have h2 := Polynomial.map_dvd (Ideal.Quotient.mk (Ideal.span {π}))
      (comp_iterate_dvd_sub_C f hs)
    simpa using h2
  have hqc : π ∣ ((f.comp ·)^[r - i] X).eval 0 := by
    by_contra hno
    have hne : (Ideal.Quotient.mk (Ideal.span {π})) (((f.comp ·)^[r - i] X).eval 0) ≠ 0 :=
      fun hz => hno (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))
    have hCc := hPiQr.sub (hCdvd r hiR.le)
    rw [sub_sub_cancel] at hCc
    exact hPiirr.not_isUnit
      (isUnit_of_dvd_unit hCc (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hne)))
  -- Take the first index at which the orbit meets `π`.
  have hP : ∃ j, 0 < j ∧ π ∣ ((f.comp ·)^[j] X).eval 0 := ⟨r - i, by omega, hqc⟩
  set m := Nat.find hP with hmdef
  obtain ⟨hm0, hmd⟩ := Nat.find_spec hP
  have hmmin : ∀ j, 0 < j → j < m → ¬ π ∣ ((f.comp ·)^[j] X).eval 0 := fun j hj0 hjm hjd =>
    Nat.find_min hP hjm ⟨hj0, hjd⟩
  have hmt : m ≤ r - i := Nat.find_le ⟨by omega, hqc⟩
  have hmr : m ≤ r := by omega
  refine ⟨m, hm0, hmr, ?_⟩
  -- Periodicity moves the divisibility down by `m`.
  have hqtm : π ∣ ((f.comp ·)^[r - i - m] X).eval 0 := by
    have h2 := dvd_eval_zero_comp_iterate_add (f := f) hmd (r - i - m)
    rw [show r - i - m + m = r - i by omega] at h2
    have h3 := hqc.sub h2
    rwa [sub_sub_cancel] at h3
  have hPirm : (Pi.map (Ideal.Quotient.mk (Ideal.span {π}))) ∣
      ((f.comp ·)^[r - m] X).map (Ideal.Quotient.mk (Ideal.span {π})) := by
    have h2 := hCdvd (r - m) (by omega)
    rw [show r - m - i = r - i - m by omega,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hqtm), map_zero,
      sub_zero] at h2
    exact h2
  -- The `b`-th power lands in the square of the ideal, so the constant term must too.
  have hmemb : ((f.comp ·)^[r - m] X) ^ b ∈ (Ideal.span {C π, Pi} : Ideal (R[X])) ^ 2 :=
    Ideal.pow_le_pow_right hb (Ideal.pow_mem_pow (mem_span_pair_iff_map_dvd.mpr hPirm) b)
  obtain ⟨W, hW⟩ := comp_iterate_eq_C_add_pow_mul hf (by omega) hm0 hmr
  obtain ⟨c, hc⟩ := hmd
  have hCm : C π * C c ∈ (Ideal.span {C π, Pi} : Ideal (R[X])) ^ 2 := by
    have heq : C π * C c = ((f.comp ·)^[r] X) - ((f.comp ·)^[r - m] X) ^ b * W := by
      rw [← map_mul, ← hc]
      linear_combination -hW
    rw [heq]
    exact Ideal.sub_mem _ hmem (Ideal.mul_mem_right _ _ hmemb)
  have hCcmem := mem_span_pair_of_C_mul_mem_sq hπ hPi0 hCm
  rw [mem_span_pair_iff_map_dvd, Polynomial.map_C] at hCcmem
  have hcz : (Ideal.Quotient.mk (Ideal.span {π})) c = 0 := by
    by_contra hne
    exact hPiirr.not_isUnit
      (isUnit_of_dvd_unit hCcmem (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hne)))
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hcz)
  exact ⟨d, by rw [hc, hd]; ring⟩

/-- **The criterion over an arbitrary base, easy direction.**  If `π ^ 2` divides some
member of the critical orbit then the iterate lies in the square of a maximal ideal: take
`Pi` to be any monic irreducible factor of the reduction of `Q (r - m)`. -/
theorem exists_mem_sq_of_sq_dvd (hf : f = X ^ b + C A) (hb : 2 ≤ b) {r m : ℕ}
    (hm : 0 < m) (hmr : m ≤ r) (hsq : π ^ 2 ∣ ((f.comp ·)^[m] X).eval 0) :
    ∃ Pi : R[X], Pi.Monic ∧
      Irreducible (Pi.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
      ((f.comp ·)^[r] X) ∈ (Ideal.span {C π, Pi} : Ideal (R[X])) ^ 2 := by
  classical
  have hb0 : 0 < b := by omega
  have hfm : f.Monic := by rw [hf]; exact monic_X_pow_add_C A hb0.ne'
  have hfd : f.natDegree = b := by rw [hf]; exact natDegree_X_pow_add_C
  have hQm : ((f.comp ·)^[r - m] X).Monic := monic_comp_iterate hfm (by omega) (r - m)
  have hQdeg : (((f.comp ·)^[r - m] X).map
      (Ideal.Quotient.mk (Ideal.span {π}))).natDegree = b ^ (r - m) := by
    rw [hQm.natDegree_map, natDegree_comp_iterate, hfd]
  have hQne : (((f.comp ·)^[r - m] X).map (Ideal.Quotient.mk (Ideal.span {π}))) ≠ 0 :=
    (hQm.map _).ne_zero
  have hQnu : ¬ IsUnit ((((f.comp ·)^[r - m] X)).map
      (Ideal.Quotient.mk (Ideal.span {π}))) := by
    intro hu
    have hz := natDegree_eq_zero_of_isUnit hu
    rw [hQdeg] at hz
    have hpos : 0 < b ^ (r - m) := by positivity
    omega
  obtain ⟨i, hi, hidvd⟩ := WfDvdMonoid.exists_irreducible_factor hQnu hQne
  have hπirr : Irreducible (normalize i) := (normalize_associated i).symm.irreducible hi
  have hπm : (normalize i).Monic := monic_normalize hi.ne_zero
  have hπdvd : (normalize i) ∣ ((f.comp ·)^[r - m] X).map
      (Ideal.Quotient.mk (Ideal.span {π})) := (normalize_associated i).dvd.trans hidvd
  have hsurj : Function.Surjective (Ideal.Quotient.mk (Ideal.span {π} : Ideal R)) :=
    Ideal.Quotient.mk_surjective
  obtain ⟨Pi, hPimap, -, hPimonic⟩ :=
    lifts_and_degree_eq_and_monic ((mem_lifts _).mpr
      (Polynomial.map_surjective _ hsurj (normalize i))) hπm
  refine ⟨Pi, hPimonic, by rw [hPimap]; exact hπirr, ?_⟩
  have hmem1 : ((f.comp ·)^[r - m] X) ∈ (Ideal.span {C π, Pi} : Ideal (R[X])) :=
    mem_span_pair_iff_map_dvd.mpr (by rw [hPimap]; exact hπdvd)
  have hmemb : ((f.comp ·)^[r - m] X) ^ b ∈ (Ideal.span {C π, Pi} : Ideal (R[X])) ^ 2 :=
    Ideal.pow_le_pow_right hb (Ideal.pow_mem_pow hmem1 b)
  obtain ⟨d, hd⟩ := hsq
  have hmemC : C (((f.comp ·)^[m] X).eval 0) ∈ (Ideal.span {C π, Pi} : Ideal (R[X])) ^ 2 := by
    have hCq : (C π : R[X]) ∈ (Ideal.span {C π, Pi} : Ideal (R[X])) :=
      Ideal.subset_span (by simp)
    have heq : C (((f.comp ·)^[m] X).eval 0) = C π ^ 2 * C d := by
      rw [← map_pow, ← map_mul, ← hd]
    rw [heq]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hCq 2)
  obtain ⟨W, hW⟩ := comp_iterate_eq_C_add_pow_mul hf hb0 hm hmr
  rw [hW]
  exact Ideal.add_mem _ hmemC (Ideal.mul_mem_right _ _ hmemb)

/-- **The criterion over an arbitrary base.**  For `π` generating a maximal ideal of a domain
`R` and not dividing `b`, the `r`-fold iterate of the unicritical polynomial `X ^ b + A` lies
in the square of a maximal ideal `⟨π, Pi⟩` of `R[X]` — equivalently, `π` is an index divisor
of it — **exactly when** `π ^ 2` divides one of the first `r` values of the critical orbit. -/
theorem exists_mem_sq_iff (hπ : Prime π) (hf : f = X ^ b + C A) (hb : 2 ≤ b)
    (hπb : ¬ π ∣ (b : R)) (r : ℕ) :
    (∃ Pi : R[X], Pi.Monic ∧
      Irreducible (Pi.map (Ideal.Quotient.mk (Ideal.span {π}))) ∧
      ((f.comp ·)^[r] X) ∈ (Ideal.span {C π, Pi} : Ideal (R[X])) ^ 2) ↔
    ∃ m, 0 < m ∧ m ≤ r ∧ π ^ 2 ∣ ((f.comp ·)^[m] X).eval 0 :=
  ⟨exists_sq_dvd_of_exists_mem_sq hπ hf hb hπb,
    fun ⟨_, hm, hmr, hsq⟩ => exists_mem_sq_of_sq_dvd hf hb hm hmr hsq⟩

end IterateBase

end Monogenic
