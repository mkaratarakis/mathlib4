/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.NumberTheory.NumberField.Monogenic.KaurKumar
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.Tactic.NormNum.Prime

/-!
# Witnesses for the Kaur–Kumar theorem

The Kaur–Kumar theorem `NumberField.KaurKumar.monogenic_iff` is stated for an algebraic
integer `θ : 𝓞 K` whose minimal polynomial over `ℤ` is `X ^ n + A (B X + 1) ^ m` and which
generates `K` over `ℚ`.  This file shows that these hypotheses are satisfiable, so that the
theorem is not vacuous: from any monic `f : ℤ[X]` which is irreducible over `ℚ` we build a
number field `K` and an algebraic integer `θ : 𝓞 K` with `minpoly ℤ θ = f` and `ℚ(θ) = K`.

## Main results

* `NumberField.KaurKumar.minpoly_rootOfMonic` and `NumberField.KaurKumar.adjoin_rootOfMonic`:
  for monic `f : ℤ[X]` irreducible over `ℚ`, the root `θ` of `f` in the number field
  `K = ℚ[X] / (f)` is an algebraic integer with `minpoly ℤ θ = f` and `Algebra.adjoin ℚ {θ} = ⊤`.
  These discharge the hypotheses `hθ` and `hgen` of the Kaur–Kumar theorem.
* `NumberField.KaurKumar.monogenic_adjoinRoot_iff`: the Kaur–Kumar theorem restated purely in
  terms of the polynomial `X ^ n + A (B X + 1) ^ m`, with no hypothetical `θ` around.
* `NumberField.KaurKumar.monogenic_adjoinRoot_iff_of_squarefree`: the same statement for
  squarefree `A ≠ ±1`, where irreducibility is automatic (Eisenstein), so that no
  irreducibility hypothesis remains at all.
* `NumberField.KaurKumar.Example.adjoin_theta_eq_top`: a completely explicit witness, the root
  `θ` of `f = X ^ 3 + 2 (X + 1) ^ 2 = X ^ 3 + 2 X ^ 2 + 4 X + 2`, for which the Kaur–Kumar
  theorem yields `ℤ[θ] = 𝓞 K`.

## Implementation notes

The `ℚ`-algebra structure on `AdjoinRoot g` found by instance search for a number field is
`DivisionRing.toRatAlgebra`, not `AdjoinRoot.instAlgebra`; the two are definitionally equal
(and equal by `Algebra.algebra_rat_subsingleton`), but not syntactically, so the `AdjoinRoot`
lemmas about `minpoly ℚ` have to be transported by `exact` rather than by `rw`.
-/

@[expose] public section

noncomputable section

open Polynomial NumberField

namespace NumberField.KaurKumar

/-! ### The number field defined by a monic integer polynomial -/

section AdjoinRootWitness

/-- An integer polynomial viewed as a rational polynomial. -/
abbrev ratMap (f : ℤ[X]) : ℚ[X] := f.map (Int.castRingHom ℚ)

/-- The field `ℚ[X] / (f)` attached to an integer polynomial `f` irreducible over `ℚ`.
It is a number field, by `AdjoinRoot.instNumberFieldRat`. -/
abbrev rootField (f : ℤ[X]) : Type := AdjoinRoot (ratMap f)

variable (f : ℤ[X]) [Fact (Irreducible (ratMap f))]

example : NumberField (rootField f) := inferInstance

/-- The root of a monic integer polynomial `f` in `rootField f` is an algebraic integer. -/
theorem isIntegral_root (hf : f.Monic) : IsIntegral ℤ (AdjoinRoot.root (ratMap f)) :=
  ⟨f, hf, by
    rw [← Polynomial.aeval_def, AdjoinRoot.aeval_eq_of_algebra, algebraMap_int_eq]
    exact AdjoinRoot.mk_self⟩

/-- The root of a monic integer polynomial `f`, as an algebraic integer of `rootField f`. -/
def rootOfMonic (hf : f.Monic) : 𝓞 (rootField f) :=
  ⟨AdjoinRoot.root (ratMap f), isIntegral_root f hf⟩

@[simp]
theorem coe_rootOfMonic (hf : f.Monic) :
    ((rootOfMonic f hf : 𝓞 (rootField f)) : rootField f) = AdjoinRoot.root (ratMap f) :=
  rfl

/-- The minimal polynomial over `ℚ` of the root of a monic `f` is `f` itself, viewed over `ℚ`. -/
theorem minpoly_root_rat (hf : f.Monic) :
    minpoly ℚ (AdjoinRoot.root (ratMap f)) = ratMap f := by
  have h := AdjoinRoot.minpoly_root (K := ℚ) (f := ratMap f)
    (Fact.out : Irreducible (ratMap f)).ne_zero
  rw [(hf.map (Int.castRingHom ℚ)).leadingCoeff, inv_one, map_one, mul_one] at h
  exact h

/-- **The minimal polynomial of the constructed algebraic integer is `f`.**  This discharges
the hypothesis `hθ` of `NumberField.KaurKumar.monogenic_iff`. -/
theorem minpoly_rootOfMonic (hf : f.Monic) : minpoly ℤ (rootOfMonic f hf) = f := by
  have h := minpoly.isIntegrallyClosed_eq_field_fractions' (R := ℤ) (K := ℚ)
    (S := rootField f) (isIntegral_root f hf)
  rw [minpoly_root_rat f hf, algebraMap_int_eq] at h
  rw [← RingOfIntegers.minpoly_coe, coe_rootOfMonic]
  exact Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective h.symm

/-- **The constructed algebraic integer generates the field over `ℚ`.**  This discharges the
hypothesis `hgen` of `NumberField.KaurKumar.monogenic_iff`. -/
theorem adjoin_rootOfMonic (hf : f.Monic) :
    Algebra.adjoin ℚ {((rootOfMonic f hf : 𝓞 (rootField f)) : rootField f)} = ⊤ := by
  rw [coe_rootOfMonic]
  exact AdjoinRoot.adjoinRoot_eq_top

end AdjoinRootWitness

/-! ### The Kaur–Kumar theorem as a statement about polynomials -/

section PolynomialVersion

variable {n m : ℕ} {A B : ℤ}

/-- `X ^ n + A (B X + 1) ^ m` is monic when `m < n`. -/
theorem monic_jones' (hmn : m < n) : (X ^ n + C A * (C B * X + 1) ^ m : ℤ[X]).Monic := by
  refine Polynomial.monic_X_pow_add (lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_)
  have h1 : (C B * X + 1 : ℤ[X]).degree ≤ 1 := by
    simpa using Polynomial.degree_linear_le (a := B) (b := (1 : ℤ))
  have h2 : ((C B * X + 1 : ℤ[X]) ^ m).degree ≤ (m : WithBot ℕ) := by
    refine (Polynomial.degree_pow_le _ _).trans ?_
    calc (m : ℕ) • (C B * X + 1 : ℤ[X]).degree ≤ (m : ℕ) • (1 : WithBot ℕ) :=
          nsmul_le_nsmul_right h1 m
      _ = (m : WithBot ℕ) := by simp [nsmul_eq_mul]
  calc (C A).degree + ((C B * X + 1 : ℤ[X]) ^ m).degree ≤ 0 + (m : WithBot ℕ) :=
        add_le_add Polynomial.degree_C_le h2
    _ = (m : WithBot ℕ) := zero_add _
    _ < (n : WithBot ℕ) := by exact_mod_cast hmn

/-- **The Kaur–Kumar theorem, purely in terms of the polynomial.**  Let
`f = X ^ n + A (B X + 1) ^ m` with `1 ≤ m < n` and `gcd (n, m B) = 1`, and assume that `f` is
irreducible over `ℚ`.  Let `θ` be the root of `f` in the number field `K = ℚ[X] / (f)`.  Then
`ℤ[θ] = 𝓞 K` if and only if `A` and `D n m A B` are squarefree.

Unlike `NumberField.KaurKumar.monogenic_iff`, this version has no hypotheses about an abstract
`θ`, and hence cannot be vacuous; it is applied to an explicit polynomial in
`NumberField.KaurKumar.Example.adjoin_theta_eq_top`. -/
theorem monogenic_adjoinRoot_iff (hm : 0 < m) (hmn : m < n)
    (hgcd : IsCoprime (n : ℤ) ((m : ℤ) * B))
    [Fact (Irreducible (ratMap (X ^ n + C A * (C B * X + 1) ^ m)))] :
    Algebra.adjoin ℤ {rootOfMonic (X ^ n + C A * (C B * X + 1) ^ m) (monic_jones' hmn)} = ⊤ ↔
      Squarefree A ∧ Squarefree (D n m A B) :=
  monogenic_iff hm hmn hgcd (minpoly_rootOfMonic _ (monic_jones' hmn))
    (adjoin_rootOfMonic _ (monic_jones' hmn))

/-- For squarefree `A ≠ ±1` and `m < n`, the polynomial `X ^ n + A (B X + 1) ^ m` is
irreducible over `ℚ` (Eisenstein at a prime factor of `A` together with Gauss' lemma),
packaged as a `Fact` so that it can be used as the instance required by `rootField`. -/
theorem fact_irreducible_jones (hA : Squarefree A) (hA1 : A.natAbs ≠ 1) (hmn : m < n) :
    Fact (Irreducible (ratMap (X ^ n + C A * (C B * X + 1) ^ m))) :=
  ⟨(Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    (monic_jones' hmn).isPrimitive).mp (irreducible_of_squarefree hA hA1 hmn)⟩

/-- **The Kaur–Kumar theorem for squarefree `A`, with no irreducibility hypothesis.**
Let `A` be squarefree with `A ≠ ±1`, let `1 ≤ m < n` and `gcd (n, m B) = 1`.  Then
`f = X ^ n + A (B X + 1) ^ m` is automatically irreducible (`fact_irreducible_jones`), and
its root `θ` in the number field `K = ℚ[X] / (f)` satisfies `ℤ[θ] = 𝓞 K` if and only if
`D n m A B` is squarefree. -/
theorem monogenic_adjoinRoot_iff_of_squarefree (hA : Squarefree A) (hA1 : A.natAbs ≠ 1)
    (hm : 0 < m) (hmn : m < n) (hgcd : IsCoprime (n : ℤ) ((m : ℤ) * B)) :
    haveI := fact_irreducible_jones (B := B) hA hA1 hmn
    (Algebra.adjoin ℤ {rootOfMonic (X ^ n + C A * (C B * X + 1) ^ m) (monic_jones' hmn)} = ⊤ ↔
      Squarefree (D n m A B)) := by
  haveI := fact_irreducible_jones (B := B) hA hA1 hmn
  rw [monogenic_adjoinRoot_iff hm hmn hgcd]
  exact and_iff_right hA

end PolynomialVersion

/-! ### An explicit witness -/

namespace Example

/-- The polynomial `X ^ 3 + 2 (X + 1) ^ 2 = X ^ 3 + 2 X ^ 2 + 4 X + 2`, in the shape
`X ^ n + A (B X + 1) ^ m` with `n = 3`, `m = 2`, `A = 2`, `B = 1`. -/
def f : ℤ[X] := X ^ 3 + C 2 * (C 1 * X + 1) ^ 2

theorem f_eq : f = X ^ 3 + C 2 * X ^ 2 + C 4 * X + C 2 := by
  simp only [f, map_one, map_ofNat, one_mul]
  ring

theorem f_monic : f.Monic := monic_jones' (n := 3) (m := 2) (by norm_num)

/-- `f` is irreducible over `ℤ`, by Eisenstein's criterion at `2`. -/
theorem f_irreducible : Irreducible f :=
  irreducible_of_prime (A := 2) (B := 1) (n := 3) (m := 2) Int.prime_two (by norm_num)

/-- `f` is irreducible over `ℚ`, by Gauss' lemma. -/
instance : Fact (Irreducible (ratMap f)) :=
  ⟨(Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    f_monic.isPrimitive).mp f_irreducible⟩

/-- The number field `K = ℚ[X] / (X ^ 3 + 2 X ^ 2 + 4 X + 2)`, of degree `3` over `ℚ`. -/
abbrev K : Type := rootField f

/-- The algebraic integer `θ ∈ 𝓞 K` given by the class of `X`: a root of `f`. -/
def θ : 𝓞 K := rootOfMonic f f_monic

/-- The hypothesis `hθ` of `NumberField.KaurKumar.monogenic_iff` holds for `θ`. -/
theorem minpoly_theta : minpoly ℤ θ = X ^ 3 + C 2 * (C 1 * X + 1) ^ 2 :=
  minpoly_rootOfMonic f f_monic

/-- The hypothesis `hgen` of `NumberField.KaurKumar.monogenic_iff` holds for `θ`. -/
theorem adjoin_rat_theta : Algebra.adjoin ℚ {(θ : K)} = ⊤ :=
  adjoin_rootOfMonic f f_monic

theorem D_eq : D 3 2 2 1 = 19 := by norm_num [D]

theorem squarefree_two : Squarefree (2 : ℤ) := Int.prime_two.irreducible.squarefree

theorem squarefree_nineteen : Squarefree (19 : ℤ) :=
  (Int.prime_iff_natAbs_prime.mpr (by norm_num)).irreducible.squarefree

/-- **A concrete witness for the Kaur–Kumar theorem.**  For the number field
`K = ℚ[X] / (X ^ 3 + 2 X ^ 2 + 4 X + 2)` and the root `θ` of that polynomial, all the
hypotheses of `NumberField.KaurKumar.monogenic_iff` are satisfied (with `n = 3`, `m = 2`,
`A = 2`, `B = 1`), and the theorem yields that `ℤ[θ]` is the full ring of integers of `K`,
since `A = 2` and `D 3 2 2 1 = 19` are both squarefree.  In particular, the hypotheses of
`monogenic_iff` are satisfiable, so the Kaur–Kumar theorem is not vacuously true. -/
theorem adjoin_theta_eq_top : Algebra.adjoin ℤ {θ} = ⊤ := by
  rw [monogenic_iff (θ := θ) (n := 3) (m := 2) (A := 2) (B := 1) (by norm_num) (by norm_num)
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) minpoly_theta adjoin_rat_theta]
  exact ⟨squarefree_two, D_eq ▸ squarefree_nineteen⟩

end Example

end NumberField.KaurKumar
