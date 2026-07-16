/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.Monogenic.DoubleRoot

/-!
# The Kaur–Kumar theorem on monogenicity of `X ^ n + A (B X + 1) ^ m`

Let `f = X ^ n + A (B X + 1) ^ m ∈ ℤ[X]` be irreducible, with `1 ≤ m < n` and
`gcd (n, m B) = 1`, and let `θ` be a root of `f` generating the number field `K`.  This file
proves the theorem of Kaur and Kumar [kaurkumar2023], conjectured by Jones [jones2019], that
`ℤ[θ]` is the full ring of integers of `K` if and only if both `A` and
`D = n ^ n + (-1) ^ (n + m) B ^ n (n - m) ^ (n - m) m ^ m A` are squarefree.

## Main results

* `NumberField.KaurKumar.dvd_exponent_iff`: the local (per-prime) refinement of the
  Kaur–Kumar theorem: a rational prime `p` divides the index `[𝓞 K : ℤ[θ]]` if and only if
  `p ^ 2 ∣ A` or `p ^ 2 ∣ D`.
* `NumberField.KaurKumar.monogenic_iff`: the Kaur–Kumar theorem.
* `NumberField.KaurKumar.irreducible_of_prime`: `X ^ n + A (B X + 1) ^ m` is irreducible
  when `A` is prime (Eisenstein).
* `NumberField.KaurKumar.monogenic_iff_of_prime`: Jones' conjecture: for prime `A`, the
  polynomial is monogenic if and only if `D` is squarefree.

## Implementation notes

The proof follows [kaurkumar2023], but replaces every use of Dedekind's criterion (not
available in Mathlib) by the two criteria of
`Mathlib/NumberTheory/NumberField/Monogenic/DoubleRoot.lean`, which are proved via the
conductor-different identity.  The discriminant formula for `f` (due to Jones) is likewise
avoided: all congruences are derived directly from the relation
`(B (n - m)) ^ n f(a) ≡ (-1) ^ n D mod N` for any `N` dividing `B (n - m) a + n`.

## References

* [S. Kaur, S. Kumar, *On a conjecture of Lenny Jones about certain monogenic polynomials*,
  Bull. Aust. Math. Soc. (2023)][kaurkumar2023]
-/

@[expose] public section

noncomputable section

open Polynomial NumberField Ideal

namespace NumberField.KaurKumar

/-! ### Elementary facts about the polynomial `X ^ n + A (B X + 1) ^ m` -/

section PolynomialLemmas

variable {n m : ℕ} {A B : ℤ}

private theorem degree_C_mul_pow_lt (hmn : m < n) :
    (C A * (C B * X + 1) ^ m).degree < (n : WithBot ℕ) := by
  apply lt_of_le_of_lt (Polynomial.degree_mul_le _ _)
  have h1 : (C B * X + 1 : ℤ[X]).degree ≤ 1 := by
    simpa using Polynomial.degree_linear_le (a := B) (b := (1 : ℤ))
  have h2 : ((C B * X + 1 : ℤ[X]) ^ m).degree ≤ (m : WithBot ℕ) := by
    refine (Polynomial.degree_pow_le _ _).trans ?_
    calc (m : ℕ) • (C B * X + 1 : ℤ[X]).degree ≤ (m : ℕ) • (1 : WithBot ℕ) :=
          nsmul_le_nsmul_right h1 m
      _ = (m : WithBot ℕ) := by
          simp [nsmul_eq_mul]
  calc (C A).degree + ((C B * X + 1 : ℤ[X]) ^ m).degree ≤ 0 + (m : WithBot ℕ) :=
        add_le_add Polynomial.degree_C_le h2
    _ = (m : WithBot ℕ) := zero_add _
    _ < (n : WithBot ℕ) := by exact_mod_cast hmn

private theorem monic_jones (hmn : m < n) :
    (X ^ n + C A * (C B * X + 1) ^ m).Monic :=
  Polynomial.monic_X_pow_add (degree_C_mul_pow_lt hmn)

private theorem degree_jones (hmn : m < n) :
    (X ^ n + C A * (C B * X + 1) ^ m).degree = (n : WithBot ℕ) := by
  rw [Polynomial.degree_add_eq_left_of_degree_lt
    (by rw [Polynomial.degree_X_pow]; exact degree_C_mul_pow_lt hmn),
    Polynomial.degree_X_pow]

private theorem natDegree_jones (hmn : m < n) :
    (X ^ n + C A * (C B * X + 1) ^ m).natDegree = n :=
  Polynomial.natDegree_eq_of_degree_eq_some (degree_jones hmn)

private theorem eval_jones (a : ℤ) :
    (X ^ n + C A * (C B * X + 1) ^ m).eval a = a ^ n + A * (B * a + 1) ^ m := by
  simp

private theorem derivative_jones :
    derivative (X ^ n + C A * (C B * X + 1) ^ m) =
      C (n : ℤ) * X ^ (n - 1) + C ((m : ℤ) * A * B) * (C B * X + 1) ^ (m - 1) := by
  have hu : derivative (C B * X + 1 : ℤ[X]) = C B := by
    rw [derivative_add, derivative_one, derivative_C_mul, derivative_X, mul_one, add_zero]
  rw [derivative_add, derivative_X_pow, derivative_C_mul, derivative_pow, hu, C_mul, C_mul]
  ring

private theorem eval_derivative_jones (a : ℤ) :
    (derivative (X ^ n + C A * (C B * X + 1) ^ m)).eval a =
      n * a ^ (n - 1) + m * A * B * (B * a + 1) ^ (m - 1) := by
  rw [derivative_jones]
  simp

private theorem eval_derivative_derivative_jones (a : ℤ) :
    (derivative (derivative (X ^ n + C A * (C B * X + 1) ^ m))).eval a =
      (n : ℤ) * ((n - 1 : ℕ) : ℤ) * a ^ (n - 2) +
        (m : ℤ) * ((m - 1 : ℕ) : ℤ) * A * B ^ 2 * (B * a + 1) ^ (m - 2) := by
  have hu : derivative (C B * X + 1 : ℤ[X]) = C B := by
    rw [derivative_add, derivative_one, derivative_C_mul, derivative_X, mul_one, add_zero]
  rw [derivative_jones, derivative_add, derivative_C_mul, derivative_C_mul, derivative_X_pow,
    derivative_pow, hu]
  have h2 : n - 1 - 1 = n - 2 := by omega
  have h3 : m - 1 - 1 = m - 2 := by omega
  simp only [h2, h3, eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_one]
  ring

private theorem coeff_jones_lt {i : ℕ} (hi : i < n) :
    (X ^ n + C A * (C B * X + 1) ^ m).coeff i = A * ((C B * X + 1) ^ m).coeff i := by
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega), zero_add,
    Polynomial.coeff_C_mul]

private theorem coeff_jones_zero (hn : 0 < n) :
    (X ^ n + C A * (C B * X + 1) ^ m : ℤ[X]).coeff 0 = A := by
  rw [coeff_jones_lt hn, Polynomial.coeff_zero_eq_eval_zero]
  simp

/-- If `q ∣ A` and `q ^ 2 ∤ A`, the polynomial is Eisenstein at `q`. -/
private theorem isEisensteinAt_jones {q : ℤ} (hq : Prime q) (hmn : m < n)
    (hqA : q ∣ A) (hqA2 : ¬q ^ 2 ∣ A) :
    (X ^ n + C A * (C B * X + 1) ^ m).IsEisensteinAt (Submodule.span ℤ {q}) :=
  (monic_jones hmn).isEisensteinAt_of_mem_of_notMem
    (fun h => hq.not_unit (isUnit_of_dvd_one
      (Ideal.mem_span_singleton.mp ((Ideal.eq_top_iff_one _).mp h))))
    (fun {i} hi => by
      rw [natDegree_jones hmn] at hi
      rw [coeff_jones_lt hi, Ideal.mem_span_singleton]
      exact hqA.mul_right _)
    (by
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton,
        coeff_jones_zero (Nat.zero_lt_of_lt hmn)]
      exact hqA2)

/-- `X ^ n + A (B X + 1) ^ m` is irreducible when `A` is prime (Eisenstein's criterion). -/
theorem irreducible_of_prime (hA : Prime A) (hmn : m < n) :
    Irreducible (X ^ n + C A * (C B * X + 1) ^ m) :=
  (isEisensteinAt_jones hA hmn dvd_rfl fun h =>
      hA.not_unit (hA.irreducible.squarefree A (by rwa [← sq]))).irreducible
    ((Ideal.span_singleton_prime hA.ne_zero).mpr hA) (monic_jones hmn).isPrimitive
    (by rw [natDegree_jones hmn]; omega)

end PolynomialLemmas

/-! ### The quantity `D` and integer congruences -/

/-- The discriminant-like constant
`D = n ^ n + (-1) ^ (n + m) B ^ n (n - m) ^ (n - m) m ^ m A`
of the Kaur–Kumar theorem: for `f = X ^ n + A (B X + 1) ^ m` with `m < n`, the polynomial
`f` is monogenic if and only if `A` and `D n m A B` are squarefree, see `monogenic_iff`. -/
def D (n m : ℕ) (A B : ℤ) : ℤ :=
  (n : ℤ) ^ n + (-1) ^ (n + m) * B ^ n * ((n : ℤ) - m) ^ (n - m) * (m : ℤ) ^ m * A

section IntegerLemmas

variable {p n m : ℕ} {A B : ℤ}

private theorem neg_pow_identity :
    (-(n : ℤ)) ^ n + A * B ^ n * ((n : ℤ) - m) ^ (n - m) * (-(m : ℤ)) ^ m =
      (-1) ^ n * D n m A B := by
  rw [D, neg_pow, neg_pow, pow_add]
  have hone : ((-1 : ℤ)) ^ n * ((-1 : ℤ)) ^ n = 1 := by
    rw [← mul_pow]; norm_num
  linear_combination
    (-(A * B ^ n * ((n : ℤ) - m) ^ (n - m) * (-1 : ℤ) ^ m * (m : ℤ) ^ m)) * hone

/-- The fundamental congruence: if `N ∣ B (n - m) a + n` then
`(B (n - m)) ^ n f(a) ≡ (-1) ^ n D mod N`. -/
private theorem modEq_key (hmn : m ≤ n) {a N : ℤ}
    (hα : N ∣ B * ((n : ℤ) - m) * a + n) :
    (B * ((n : ℤ) - m)) ^ n * (a ^ n + A * (B * a + 1) ^ m) ≡
      (-1) ^ n * D n m A B [ZMOD N] := by
  set z : ℤ := B * ((n : ℤ) - m) with hz
  have hza : z * a ≡ -(n : ℤ) [ZMOD N] := by
    rw [Int.modEq_iff_dvd]
    have h1 : -(n : ℤ) - z * a = -(z * a + n) := by ring
    rw [h1]
    exact dvd_neg.mpr hα
  have h1 : (z * a) ^ n ≡ (-(n : ℤ)) ^ n [ZMOD N] := hza.pow n
  have h2 : ((n : ℤ) - m) * (B * a + 1) ≡ -(m : ℤ) [ZMOD N] := by
    have : ((n : ℤ) - m) * (B * a + 1) = z * a + ((n : ℤ) - m) := by rw [hz]; ring
    rw [this]
    calc z * a + ((n : ℤ) - m) ≡ -(n : ℤ) + ((n : ℤ) - m) [ZMOD N] := hza.add_right _
      _ = -(m : ℤ) := by ring
  have h2n : (((n : ℤ) - m) * (B * a + 1)) ^ m ≡ (-(m : ℤ)) ^ m [ZMOD N] := h2.pow m
  -- expand the left-hand side
  have hsplit : ((n : ℤ) - m) ^ n = ((n : ℤ) - m) ^ (n - m) * ((n : ℤ) - m) ^ m :=
    (pow_sub_mul_pow _ hmn).symm
  have hexp : z ^ n * (a ^ n + A * (B * a + 1) ^ m) =
      (z * a) ^ n + A * B ^ n * ((n : ℤ) - m) ^ (n - m) *
        (((n : ℤ) - m) * (B * a + 1)) ^ m := by
    calc z ^ n * (a ^ n + A * (B * a + 1) ^ m)
        = (z * a) ^ n + A * (z ^ n * (B * a + 1) ^ m) := by
          rw [mul_pow z a]; ring
      _ = (z * a) ^ n + A * (B ^ n * ((n : ℤ) - m) ^ n * (B * a + 1) ^ m) := by
          rw [hz, mul_pow B (((n : ℤ) - m))]
      _ = (z * a) ^ n + A * B ^ n * ((n : ℤ) - m) ^ (n - m) *
            (((n : ℤ) - m) * (B * a + 1)) ^ m := by
          rw [hsplit, mul_pow (((n : ℤ) - m)) (B * a + 1)]
          ring
  rw [hexp, ← neg_pow_identity]
  exact (h1.add ((h2n.mul_left _)))

/-- Transfer of divisibility through the fundamental congruence. -/
private theorem dvd_eval_iff_dvd_D (hmn : m ≤ n) {a N : ℤ}
    (hα : N ∣ B * ((n : ℤ) - m) * a + n)
    (hcop : IsCoprime N ((B * ((n : ℤ) - m)) ^ n)) :
    N ∣ a ^ n + A * (B * a + 1) ^ m ↔ N ∣ D n m A B := by
  have hkey := modEq_key (A := A) hmn hα
  have hd : N ∣ (-1) ^ n * D n m A B -
      (B * ((n : ℤ) - m)) ^ n * (a ^ n + A * (B * a + 1) ^ m) := hkey.dvd
  have hunit : N ∣ (-1 : ℤ) ^ n * D n m A B ↔ N ∣ D n m A B := by
    rcases Int.isUnit_iff.mp ((isUnit_one.neg).pow n) with h | h <;>
      rw [h] <;> simp [dvd_neg]
  constructor
  · intro h
    rw [← hunit]
    have h2 := dvd_add hd (h.mul_left ((B * ((n : ℤ) - m)) ^ n))
    simpa using h2
  · intro h
    have h2 : N ∣ (B * ((n : ℤ) - m)) ^ n * (a ^ n + A * (B * a + 1) ^ m) := by
      have h3 := dvd_sub (hunit.mpr h) hd
      simpa using h3
    exact hcop.dvd_of_dvd_mul_left h2

/-- If `p ∣ D` and `p ∤ A` (with `gcd (n, m B) = 1`), then `p` divides none of `n`, `B`, `m`
and `n - m`. -/
private theorem not_dvd_of_dvd_D (hp : p.Prime) (hm : 0 < m) (hmn : m < n)
    (hgcd : IsCoprime (n : ℤ) ((m : ℤ) * B)) (hA : ¬(p : ℤ) ∣ A)
    (hD : (p : ℤ) ∣ D n m A B) :
    (¬(p : ℤ) ∣ (n : ℤ)) ∧ (¬(p : ℤ) ∣ B) ∧ (¬(p : ℤ) ∣ (m : ℤ)) ∧
      ¬(p : ℤ) ∣ ((n : ℤ) - m) := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hn0 : 0 < n := hm.trans hmn
  set T : ℤ := (-1) ^ (n + m) * B ^ n * ((n : ℤ) - m) ^ (n - m) * (m : ℤ) ^ m * A with hT
  -- if `p` divides the second summand of `D`, it divides one of the listed factors
  have hfac : (p : ℤ) ∣ T →
      (p : ℤ) ∣ B ∨ (p : ℤ) ∣ ((n : ℤ) - m) ∨ (p : ℤ) ∣ (m : ℤ) ∨ (p : ℤ) ∣ A := by
    intro h
    rcases hpp.dvd_mul.mp h with h | h
    · rcases hpp.dvd_mul.mp h with h | h
      · rcases hpp.dvd_mul.mp h with h | h
        · rcases hpp.dvd_mul.mp h with h | h
          · exact absurd (dvd_neg.mp (hpp.dvd_of_dvd_pow h)) hpp.not_dvd_one
          · exact Or.inl (hpp.dvd_of_dvd_pow h)
        · exact Or.inr (Or.inl (hpp.dvd_of_dvd_pow h))
      · exact Or.inr (Or.inr (Or.inl (hpp.dvd_of_dvd_pow h)))
    · exact Or.inr (Or.inr (Or.inr h))
  have hDsum : D n m A B = (n : ℤ) ^ n + T := by rw [D, hT]
  -- `p ∤ n`
  have hnd : ¬(p : ℤ) ∣ (n : ℤ) := by
    intro hdvd
    have hTd : (p : ℤ) ∣ T := by
      have h1 : (p : ℤ) ∣ (n : ℤ) ^ n := hdvd.pow hn0.ne'
      have h2 := dvd_sub hD h1
      rw [hDsum] at h2
      simpa using h2
    have hmB : ¬(p : ℤ) ∣ ((m : ℤ) * B) := fun h => hpp.not_unit (hgcd.isUnit_of_dvd' hdvd h)
    rcases hfac hTd with h | h | h | h
    · exact hmB (h.mul_left _)
    · exact hmB ((by simpa using dvd_sub hdvd h : (p : ℤ) ∣ (m : ℤ)).mul_right _)
    · exact hmB (h.mul_right _)
    · exact hA h
  -- if `p` divides `T`'s inner factors it divides `n ^ n`, hence `n`
  have haux : (p : ℤ) ∣ T → False := by
    intro h
    have h1 : (p : ℤ) ∣ (n : ℤ) ^ n := by
      have h2 := dvd_sub hD h
      rw [hDsum] at h2
      simpa using h2
    exact hnd (hpp.dvd_of_dvd_pow h1)
  refine ⟨hnd, ?_, ?_, ?_⟩
  · intro hdvd
    exact haux ((((hdvd.pow hn0.ne').mul_left _).mul_right _).mul_right _ |>.mul_right _)
  · intro hdvd
    exact haux (((hdvd.pow hm.ne').mul_left _).mul_right _)
  · intro hdvd
    have hnm0 : n - m ≠ 0 := Nat.sub_ne_zero_of_lt hmn
    exact haux ((((hdvd.pow hnm0).mul_left _).mul_right _).mul_right _)

/-- If `p ∣ A` and `p ^ 2 ∣ D` (with `gcd (n, m B) = 1`), then `p ^ 2 ∣ A`: indeed `p` then
divides `n`, hence `p ^ 2` divides `n ^ n` and therefore the second summand of `D`, all of
whose factors except `A` are coprime to `p`. -/
private theorem sq_dvd_A_of_dvd_A_of_sq_dvd_D (hp : p.Prime) (hm : 0 < m) (hmn : m < n)
    (hgcd : IsCoprime (n : ℤ) ((m : ℤ) * B)) (hpA : (p : ℤ) ∣ A)
    (hD2 : (p : ℤ) ^ 2 ∣ D n m A B) : (p : ℤ) ^ 2 ∣ A := by
  have hn : 2 ≤ n := by omega
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hD1 : (p : ℤ) ∣ D n m A B := (dvd_pow_self _ two_ne_zero).trans hD2
  -- first, `p ∣ n`
  have hpn : (p : ℤ) ∣ (n : ℤ) := by
    have hT : (p : ℤ) ∣
        (-1) ^ (n + m) * B ^ n * ((n : ℤ) - m) ^ (n - m) * (m : ℤ) ^ m * A :=
      hpA.mul_left _
    have h1 : (p : ℤ) ∣ (n : ℤ) ^ n := by
      have h2 := dvd_sub hD1 hT
      rw [D] at h2
      simpa using h2
    exact hpp.dvd_of_dvd_pow h1
  have hmB : ¬(p : ℤ) ∣ ((m : ℤ) * B) := fun h => hpp.not_unit (hgcd.isUnit_of_dvd' hpn h)
  have hpB : ¬(p : ℤ) ∣ B := fun h => hmB (h.mul_left _)
  have hpm : ¬(p : ℤ) ∣ (m : ℤ) := fun h => hmB (h.mul_right _)
  have hpnm : ¬(p : ℤ) ∣ ((n : ℤ) - m) := fun h =>
    hpm (by simpa using dvd_sub hpn h)
  -- `p ^ 2` divides the second summand of `D`
  have h2 : (p : ℤ) ^ 2 ∣ (n : ℤ) ^ n :=
    (pow_dvd_pow_of_dvd hpn 2).trans (pow_dvd_pow _ hn)
  have h3 : (p : ℤ) ^ 2 ∣
      (-1) ^ (n + m) * B ^ n * ((n : ℤ) - m) ^ (n - m) * (m : ℤ) ^ m * A := by
    have h4 := dvd_sub hD2 h2
    rw [D] at h4
    simpa using h4
  -- and is coprime to everything but `A`
  have hu : IsCoprime ((p : ℤ)) ((-1 : ℤ) ^ (n + m)) := by
    rcases Int.isUnit_iff.mp (isUnit_one.neg.pow (n + m)) with h | h <;> rw [h]
    · exact isCoprime_one_right
    · exact isCoprime_one_right.neg_right
  have hbase : IsCoprime ((p : ℤ))
      ((-1) ^ (n + m) * B ^ n * ((n : ℤ) - m) ^ (n - m) * (m : ℤ) ^ m) :=
    ((hu.mul_right ((hpp.coprime_iff_not_dvd.mpr hpB).pow_right)).mul_right
      ((hpp.coprime_iff_not_dvd.mpr hpnm).pow_right)).mul_right
      ((hpp.coprime_iff_not_dvd.mpr hpm).pow_right)
  exact hbase.pow_left.dvd_of_dvd_mul_left h3

/-- A Bezout-style lift: if `p ∤ B (n - m)` there is an integer `a` with
`p ^ 2 ∣ B (n - m) a + n`. -/
private theorem exists_lift (hp : p.Prime) (hB : ¬(p : ℤ) ∣ B)
    (hnm : ¬(p : ℤ) ∣ ((n : ℤ) - m)) :
    ∃ a : ℤ, (p : ℤ) ^ 2 ∣ B * ((n : ℤ) - m) * a + n := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hz : ¬(p : ℤ) ∣ B * ((n : ℤ) - m) := fun h =>
    (hpp.dvd_mul.mp h).elim hB hnm
  have hcop : IsCoprime ((p : ℤ) ^ 2) (B * ((n : ℤ) - m)) :=
    (hpp.coprime_iff_not_dvd.mpr hz).pow_left
  obtain ⟨u, v, huv⟩ := hcop
  exact ⟨-(n : ℤ) * v, (n : ℤ) * u, by linear_combination (-(n : ℤ)) * huv⟩

end IntegerLemmas

/-! ### Residue analysis at a repeated root -/

section ResidueAnalysis

variable {F : Type*} [Field F] {p : ℕ} {n m : ℕ} {A B : ℤ}

/-- If `x` is a common root of `f` and `f'` in a field of characteristic `p ∤ A`, then
`(n - m) B x = -n`. -/
private theorem residue_analysis (hp : p.Prime)
    (hpF : ∀ t : ℤ, ((t : F) = 0) ↔ (p : ℤ) ∣ t)
    (hn : 2 ≤ n) (hm : 0 < m) (hgcd : IsCoprime (n : ℤ) ((m : ℤ) * B))
    (hA : ¬(p : ℤ) ∣ A) {x : F}
    (hf : x ^ n + (A : F) * ((B : F) * x + 1) ^ m = 0)
    (hf' : (n : F) * x ^ (n - 1) + (m : F) * (A : F) * (B : F) * ((B : F) * x + 1) ^ (m - 1)
      = 0) :
    ((n : F) - m) * B * x = -(n : F) := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hAF : (A : F) ≠ 0 := fun h => hA ((hpF A).mp h)
  have hcast : ∀ t : ℕ, ((t : F) = 0) ↔ (p : ℤ) ∣ (t : ℤ) := fun t => by
    rw [← hpF (t : ℤ)]
    norm_cast
  -- `x ≠ 0`
  have hxne : x ≠ 0 := by
    rintro rfl
    simp only [zero_pow (show n ≠ 0 by omega), mul_zero, zero_add, one_pow, mul_one] at hf
    exact hAF hf
  -- `B x + 1 ≠ 0`
  have hune : (B : F) * x + 1 ≠ 0 := by
    intro h
    rw [h, zero_pow hm.ne', mul_zero, add_zero, pow_eq_zero_iff (by omega)] at hf
    exact hxne hf
  -- `p ∤ n`
  have hnd : ¬(p : ℤ) ∣ (n : ℤ) := by
    intro hdvd
    have hmB : ¬(p : ℤ) ∣ ((m : ℤ) * B) := fun h => hpp.not_unit (hgcd.isUnit_of_dvd' hdvd h)
    have hmF : (m : F) ≠ 0 := fun h => hmB (((hcast m).mp h).mul_right B)
    have hBF : (B : F) ≠ 0 := fun h => hmB (((hpF B).mp h).mul_left (m : ℤ))
    have hnF : (n : F) = 0 := (hcast n).mpr hdvd
    rw [hnF, zero_mul, zero_add] at hf'
    rcases mul_eq_zero.mp hf' with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact hmF h
        · exact hAF h
      · exact hBF h
    · rcases Nat.lt_or_ge m 2 with h1 | h1
      · have hm1 : m = 1 := by omega
        rw [hm1, Nat.sub_self, pow_zero] at h
        exact one_ne_zero h
      · exact hune (pow_eq_zero_iff (by omega) |>.mp h)
  have hnF : (n : F) ≠ 0 := fun h => hnd ((hcast n).mp h)
  -- `p ∤ B`
  have hBd : ¬(p : ℤ) ∣ B := by
    intro hdvd
    have hBF : (B : F) = 0 := (hpF B).mpr hdvd
    rw [hBF, mul_zero, zero_mul, add_zero, mul_eq_zero] at hf'
    rcases hf' with h | h
    · exact hnF h
    · exact hxne (pow_eq_zero_iff (by omega) |>.mp h)
  have hBF : (B : F) ≠ 0 := fun h => hBd ((hpF B).mp h)
  -- the key relation `n (B x + 1) = m B x`
  have e1 : x ^ (n - 1) * x = x ^ n := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  have e2 : ((B : F) * x + 1) ^ (m - 1) * ((B : F) * x + 1) = ((B : F) * x + 1) ^ m := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  have hkey0 : (A : F) * ((B : F) * x + 1) ^ (m - 1) *
      ((n : F) * ((B : F) * x + 1) - (m : F) * B * x) = 0 := by
    rw [← e1] at hf
    linear_combination (n : F) * hf - x * hf' + (n : F) * (A : F) * e2
  have hkey : (n : F) * ((B : F) * x + 1) = (m : F) * B * x := by
    have hupow : ((B : F) * x + 1) ^ (m - 1) ≠ 0 := pow_ne_zero _ hune
    rcases mul_eq_zero.mp hkey0 with h | h
    · exact absurd h (mul_ne_zero hAF hupow)
    · exact sub_eq_zero.mp h
  -- `p ∤ m`
  have hmd : ¬(p : ℤ) ∣ (m : ℤ) := by
    intro hdvd
    have hmF : (m : F) = 0 := (hcast m).mpr hdvd
    rw [hmF, zero_mul, zero_mul] at hkey
    exact (mul_eq_zero.mp hkey).elim hnF hune
  -- `(n - m) B x = -n`
  linear_combination hkey

/-- At a common root of `f` and `f'`, the second derivative of `f` does not vanish. -/
private theorem residue_second_deriv (hn : 2 ≤ n)
    (hA : (A : F) ≠ 0) (hB : (B : F) ≠ 0) (hm' : (m : F) ≠ 0)
    {x : F} (hune : (B : F) * x + 1 ≠ 0)
    (hkey2 : ((n : F) - m) * B * x = -(n : F))
    (hf' : (n : F) * x ^ (n - 1) + (m : F) * (A : F) * (B : F) * ((B : F) * x + 1) ^ (m - 1)
      = 0) :
    (n : F) * ((n - 1 : ℕ) : F) * x ^ (n - 2) +
      (m : F) * ((m - 1 : ℕ) : F) * A * B ^ 2 * ((B : F) * x + 1) ^ (m - 2) ≠ 0 := by
  have hm : 0 < m := Nat.pos_of_ne_zero fun h => hm' (by simp [h])
  set u : F := (B : F) * x + 1 with hu
  intro hG2
  have hcast1 : (((n - 1 : ℕ) : F)) = (n : F) - 1 := by
    have h : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    exact_mod_cast congrArg (Int.cast (R := F)) h
  have hcast2 : (((m - 1 : ℕ) : F)) = (m : F) - 1 := by
    have h : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
    exact_mod_cast congrArg (Int.cast (R := F)) h
  have hbracket : -((n : F) - 1) * u + ((m : F) - 1) * B * x = 1 := by
    rw [hu]
    linear_combination -hkey2
  have e1 : x ^ (n - 2) * x = x ^ (n - 1) := by
    rw [← pow_succ]
    congr 1
    omega
  have hmain : ((n : F) * ((n - 1 : ℕ) : F) * x ^ (n - 2) +
      (m : F) * ((m - 1 : ℕ) : F) * A * B ^ 2 * u ^ (m - 2)) * (x * u) =
        (m : F) * A * B * u ^ (m - 1) := by
    rcases Nat.lt_or_ge m 2 with h1 | h1
    · -- `m = 1`
      have hm1 : m = 1 := by omega
      subst hm1
      simp only [Nat.sub_self, Nat.cast_zero, mul_zero, zero_mul, add_zero, Nat.cast_one,
        one_mul, pow_zero, mul_one] at hf' ⊢
      rw [hcast1]
      -- `hf' : n x^(n-1) + A B = 0`, `hbracket : -(n-1) u + 0 = 1`
      simp only [Nat.cast_one, sub_self, zero_mul, add_zero] at hbracket
      calc (n : F) * ((n : F) - 1) * x ^ (n - 2) * (x * u)
          = ((n : F) - 1) * u * ((n : F) * (x ^ (n - 2) * x)) := by ring
        _ = ((n : F) - 1) * u * ((n : F) * x ^ (n - 1)) := by rw [e1]
        _ = (A : F) * B := by
            linear_combination (((n : F) - 1) * u) * hf' + ((A : F) * B) * hbracket
    · -- `m ≥ 2`
      have e2 : u ^ (m - 2) * u = u ^ (m - 1) := by
        rw [← pow_succ]
        congr 1
        omega
      calc ((n : F) * ((n - 1 : ℕ) : F) * x ^ (n - 2) +
          (m : F) * ((m - 1 : ℕ) : F) * A * B ^ 2 * u ^ (m - 2)) * (x * u)
          = ((n - 1 : ℕ) : F) * u * ((n : F) * (x ^ (n - 2) * x)) +
            (m : F) * ((m - 1 : ℕ) : F) * A * B ^ 2 * x * (u ^ (m - 2) * u) := by ring
        _ = ((n - 1 : ℕ) : F) * u * ((n : F) * x ^ (n - 1)) +
            (m : F) * ((m - 1 : ℕ) : F) * A * B ^ 2 * x * u ^ (m - 1) := by rw [e1, e2]
        _ = (m : F) * A * B * u ^ (m - 1) := by
            rw [hcast1, hcast2]
            linear_combination (((n : F) - 1) * u) * hf' +
              ((m : F) * (A : F) * (B : F) * u ^ (m - 1)) * hbracket
  rw [hG2, zero_mul] at hmain
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hm' hA) hB) (pow_ne_zero _ hune)) hmain.symm

/-- At a common root of `f` and `f'` (in characteristic `p ∤ A`), `D` vanishes. -/
private theorem residue_D_eq_zero (hmn : m ≤ n)
    {x : F} (hkey2 : ((n : F) - m) * B * x = -(n : F))
    (hf : x ^ n + (A : F) * ((B : F) * x + 1) ^ m = 0) :
    ((D n m A B : ℤ) : F) = 0 := by
  set u : F := (B : F) * x + 1 with hu
  set ν : F := (n : F) with hν
  set μ : F := (m : F) with hμ
  have e3 : (ν - μ) * u = -μ := by rw [hu]; linear_combination hkey2
  have h1 : ((ν - μ) * (B : F) * x) ^ n = (-ν) ^ n := by rw [hkey2]
  have h2 : ((ν - μ) * u) ^ m = (-μ) ^ m := by rw [e3]
  have hsplit : (ν - μ) ^ n = (ν - μ) ^ (n - m) * (ν - μ) ^ m :=
    (pow_sub_mul_pow _ hmn).symm
  have hexp : (-ν) ^ n + (A : F) * (B : F) ^ n * (ν - μ) ^ (n - m) * (-μ) ^ m = 0 := by
    have hx : ((ν - μ) * (B : F)) ^ n * x ^ n = (-ν) ^ n := by
      rw [← h1, mul_pow ((ν - μ) * (B : F)) x]
    have hxu : ((ν - μ) * (B : F)) ^ n * ((A : F) * u ^ m) =
        (A : F) * (B : F) ^ n * (ν - μ) ^ (n - m) * (-μ) ^ m := by
      rw [← h2, mul_pow (ν - μ) u, mul_pow (ν - μ) (B : F), hsplit]
      ring
    linear_combination (((ν - μ) * (B : F)) ^ n) * hf - hx - hxu
  rw [neg_pow, neg_pow] at hexp
  have hone : (-1 : F) ^ n * (-1 : F) ^ n = 1 := by
    rw [← mul_pow]; norm_num
  rw [D]
  push_cast
  rw [pow_add]
  linear_combination ((-1 : F) ^ n) * hexp - ν ^ n * hone

/-- Conversely, if `(n - m) B x = -n` and `D = 0` in `F`, then `x` is a common root of `f`
and `f'`. -/
private theorem root_of_D (hmn : m ≤ n)
    (hn' : (n : F) ≠ 0) (hB : (B : F) ≠ 0) (hm' : (m : F) ≠ 0) (hnm' : (n : F) - m ≠ 0)
    {x : F} (hkey2 : ((n : F) - m) * B * x = -(n : F))
    (hD : ((D n m A B : ℤ) : F) = 0) :
    (x ^ n + (A : F) * ((B : F) * x + 1) ^ m = 0) ∧
      ((n : F) * x ^ (n - 1) + (m : F) * (A : F) * (B : F) * ((B : F) * x + 1) ^ (m - 1)
        = 0) := by
  have hn : 0 < n := Nat.pos_of_ne_zero fun h => hn' (by simp [h])
  have hm : 0 < m := Nat.pos_of_ne_zero fun h => hm' (by simp [h])
  set u : F := (B : F) * x + 1 with hu
  set ν : F := (n : F) with hν
  set μ : F := (m : F) with hμ
  have hxne : x ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hkey2
    exact hn' (neg_eq_zero.mp hkey2.symm)
  have e3 : (ν - μ) * u = -μ := by rw [hu]; linear_combination hkey2
  have hune : u ≠ 0 := by
    intro h
    rw [h, mul_zero, eq_comm, neg_eq_zero] at e3
    exact hm' e3
  have h1 : ((ν - μ) * (B : F) * x) ^ n = (-ν) ^ n := by rw [hkey2]
  have h2 : ((ν - μ) * u) ^ m = (-μ) ^ m := by rw [e3]
  have hsplit : (ν - μ) ^ n = (ν - μ) ^ (n - m) * (ν - μ) ^ m :=
    (pow_sub_mul_pow _ hmn).symm
  have hone : (-1 : F) ^ n * (-1 : F) ^ n = 1 := by
    rw [← mul_pow]; norm_num
  -- from `D = 0`, deduce the expanded relation
  have hDexp : (-ν) ^ n + (A : F) * (B : F) ^ n * (ν - μ) ^ (n - m) * (-μ) ^ m = 0 := by
    rw [D] at hD
    push_cast at hD
    rw [pow_add] at hD
    rw [neg_pow, neg_pow]
    linear_combination ((-1 : F) ^ n) * hD -
      ((A : F) * (B : F) ^ n * (ν - μ) ^ (n - m) * (-1 : F) ^ m * μ ^ m) * hone
  -- `f(x) = 0`
  have hf : x ^ n + (A : F) * u ^ m = 0 := by
    have hx : ((ν - μ) * (B : F)) ^ n * x ^ n = (-ν) ^ n := by
      rw [← h1, mul_pow ((ν - μ) * (B : F)) x]
    have hxu : ((ν - μ) * (B : F)) ^ n * ((A : F) * u ^ m) =
        (A : F) * (B : F) ^ n * (ν - μ) ^ (n - m) * (-μ) ^ m := by
      rw [← h2, mul_pow (ν - μ) u, mul_pow (ν - μ) (B : F), hsplit]
      ring
    have hmul : ((ν - μ) * (B : F)) ^ n * (x ^ n + (A : F) * u ^ m) = 0 := by
      linear_combination hx + hxu + hDexp
    exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero _ (mul_ne_zero hnm' hB))
  refine ⟨hf, ?_⟩
  -- `f'(x) = 0`
  have e1 : x ^ (n - 1) * x = x ^ n := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  have e2 : u ^ (m - 1) * u = u ^ m := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  have hbr : μ * B * x - ν * u = 0 := by
    rw [hu]
    linear_combination -hkey2
  have hmain : (ν * x ^ (n - 1) + μ * A * B * u ^ (m - 1)) * (x * u) = 0 := by
    calc (ν * x ^ (n - 1) + μ * A * B * u ^ (m - 1)) * (x * u)
        = ν * u * (x ^ (n - 1) * x) + μ * A * B * x * (u ^ (m - 1) * u) := by ring
      _ = ν * u * x ^ n + μ * A * B * x * u ^ m := by rw [e1, e2]
      _ = ν * u * (x ^ n + A * u ^ m) + A * u ^ m * (μ * B * x - ν * u) := by ring
      _ = 0 := by rw [hf, hbr, mul_zero, mul_zero, add_zero]
  exact (mul_eq_zero.mp hmain).resolve_right (mul_ne_zero hxne hune)

/-- If `p ∤ A` and `p ∣ D`, then `f = X ^ n + A (B X + 1) ^ m` has a double root modulo `p`
at any integer `a` with `p ^ 2 ∣ B (n - m) a + n`, and such an `a` exists. -/
private theorem exists_lift_double_root {p : ℕ} [Fact p.Prime] (hp : p.Prime) (hm : 0 < m)
    (hmn : m < n) (hgcd : IsCoprime (n : ℤ) ((m : ℤ) * B)) (hA : ¬(p : ℤ) ∣ A)
    (hD : (p : ℤ) ∣ D n m A B) :
    ∃ a : ℤ, (p : ℤ) ^ 2 ∣ B * ((n : ℤ) - m) * a + n ∧
      IsCoprime ((p : ℤ) ^ 2) ((B * ((n : ℤ) - m)) ^ n) ∧
      ((n : ZMod p) - m) * B * (a : ZMod p) = -(n : ZMod p) ∧
      ((a : ZMod p) ^ n + (A : ZMod p) * ((B : ZMod p) * (a : ZMod p) + 1) ^ m = 0) ∧
      ((n : ZMod p) * (a : ZMod p) ^ (n - 1) + (m : ZMod p) * (A : ZMod p) * (B : ZMod p) *
        ((B : ZMod p) * (a : ZMod p) + 1) ^ (m - 1) = 0) := by
  obtain ⟨hpn, hpB, hpm, hpnm⟩ := not_dvd_of_dvd_D hp hm hmn hgcd hA hD
  obtain ⟨a, ha⟩ := exists_lift hp hpB hpnm
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hcop2 : IsCoprime ((p : ℤ) ^ 2) ((B * ((n : ℤ) - m)) ^ n) :=
    (hpp.coprime_iff_not_dvd.mpr fun h => (hpp.dvd_mul.mp h).elim hpB hpnm).pow
  have hpF0 : ∀ t : ℤ, ((t : ZMod p) = 0) ↔ (p : ℤ) ∣ t := fun t =>
    ZMod.intCast_zmod_eq_zero_iff_dvd t p
  have hkey2a : ((n : ZMod p) - m) * B * (a : ZMod p) = -(n : ZMod p) := by
    have h0 : ((B * ((n : ℤ) - m) * a + n : ℤ) : ZMod p) = 0 :=
      (hpF0 _).mpr ((dvd_pow_self (p : ℤ) two_ne_zero).trans ha)
    push_cast at h0
    linear_combination h0
  have hnZ : ((n : ZMod p)) ≠ 0 := fun h => hpn (by rw [← hpF0]; exact_mod_cast h)
  have hBZ : ((B : ZMod p)) ≠ 0 := fun h => hpB ((hpF0 B).mp h)
  have hmZ : ((m : ZMod p)) ≠ 0 := fun h => hpm (by rw [← hpF0]; exact_mod_cast h)
  have hnmZ : ((n : ZMod p)) - m ≠ 0 := fun h => hpnm (by rw [← hpF0]; push_cast; exact h)
  obtain ⟨hfa, hf'a⟩ := root_of_D hmn.le hnZ hBZ hmZ hnmZ hkey2a ((hpF0 _).mpr hD)
  exact ⟨a, ha, hcop2, hkey2a, hfa, hf'a⟩

end ResidueAnalysis

/-! ### The main theorem -/

section Main

attribute [local instance] Ideal.Quotient.field

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {n m : ℕ} {A B : ℤ}

private theorem sq_dvd_natCast_iff {z : ℤ} {q : ℕ} : (q : ℤ) ^ 2 ∣ z ↔ q * q ∣ z.natAbs := by
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_pow, Int.natAbs_natCast, sq]

/-- An integer is squarefree if and only if no prime squared divides it. -/
private theorem squarefree_int_iff {z : ℤ} :
    Squarefree z ↔ ∀ q : ℕ, q.Prime → ¬(q : ℤ) ^ 2 ∣ z := by
  rw [← Int.squarefree_natAbs, Nat.squarefree_iff_prime_squarefree]
  exact forall₂_congr fun q hq => not_congr sq_dvd_natCast_iff.symm

omit [NumberField K] in
/-- The polynomial identity `f(θ) = 0` in `𝓞 K`. -/
private theorem aeval_root (hθ : minpoly ℤ θ = X ^ n + C A * (C B * X + 1) ^ m) :
    θ ^ n + (A : 𝓞 K) * ((B : 𝓞 K) * θ + 1) ^ m = 0 := by
  have h := minpoly.aeval ℤ θ
  rw [hθ] at h
  simpa [algebraMap_int_eq, eq_intCast] using h

omit [NumberField K] in
private theorem aeval_derivative_eq (hθ : minpoly ℤ θ = X ^ n + C A * (C B * X + 1) ^ m) :
    aeval θ (derivative (minpoly ℤ θ)) =
      (n : 𝓞 K) * θ ^ (n - 1) +
        (m : 𝓞 K) * (A : 𝓞 K) * (B : 𝓞 K) * ((B : 𝓞 K) * θ + 1) ^ (m - 1) := by
  rw [hθ, derivative_jones]
  simp only [map_add, map_mul, map_pow, aeval_X, map_one, eq_intCast, map_intCast]
  push_cast
  ring

omit [NumberField K] in
/-- The transfer of integer divisibility to the residue field `𝓞 K ⧸ 𝔪`. -/
private theorem quotient_intCast_iff {p : ℕ} [Fact p.Prime] {𝔪 : Ideal (𝓞 K)}
    (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : 𝓞 K) ∈ 𝔪) (t : ℤ) :
    ((t : 𝓞 K ⧸ 𝔪) = 0) ↔ (p : ℤ) ∣ t := by
  rw [show ((t : 𝓞 K ⧸ 𝔪)) = Ideal.Quotient.mk 𝔪 ((t : 𝓞 K)) from
    (map_intCast (Ideal.Quotient.mk 𝔪) t).symm, Ideal.Quotient.eq_zero_iff_mem]
  exact RingOfIntegers.intCast_mem_iff_dvd h𝔪 hp𝔪 t

/-- In a residue field above `p` containing the conductor, `θ` is a double root of `f`. -/
private theorem quotient_facts (hθ : minpoly ℤ θ = X ^ n + C A * (C B * X + 1) ^ m)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    {𝔪 : Ideal (𝓞 K)} (hcond : conductor ℤ θ ≤ 𝔪) :
    ((Ideal.Quotient.mk 𝔪 θ) ^ n +
        (A : 𝓞 K ⧸ 𝔪) * ((B : 𝓞 K ⧸ 𝔪) * (Ideal.Quotient.mk 𝔪 θ) + 1) ^ m = 0) ∧
      ((n : 𝓞 K ⧸ 𝔪) * (Ideal.Quotient.mk 𝔪 θ) ^ (n - 1) +
        (m : 𝓞 K ⧸ 𝔪) * (A : 𝓞 K ⧸ 𝔪) * (B : 𝓞 K ⧸ 𝔪) *
          ((B : 𝓞 K ⧸ 𝔪) * (Ideal.Quotient.mk 𝔪 θ) + 1) ^ (m - 1) = 0) := by
  constructor
  · have h := congrArg (Ideal.Quotient.mk 𝔪) (aeval_root hθ)
    simpa [map_add, map_mul, map_pow, map_one, map_intCast] using h
  · have h1 : aeval θ (derivative (minpoly ℤ θ)) ∈ 𝔪 :=
      hcond (RingOfIntegers.aeval_derivative_minpoly_mem_conductor hgen)
    have h2 := (Ideal.Quotient.eq_zero_iff_mem (I := 𝔪)).mpr h1
    rw [aeval_derivative_eq hθ] at h2
    simpa [map_add, map_mul, map_pow, map_one, map_intCast, map_natCast] using h2

/-- The converse direction, localized at `p`: if `p ^ 2` divides neither `A` nor `D`, then
`p` does not divide the exponent. -/
private theorem not_dvd_exponent_aux {p : ℕ} [hp : Fact p.Prime]
    (hm : 0 < m) (hmn : m < n) (hgcd : IsCoprime (n : ℤ) ((m : ℤ) * B))
    (hθ : minpoly ℤ θ = X ^ n + C A * (C B * X + 1) ^ m)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hA2 : ¬(p : ℤ) ^ 2 ∣ A) (hD2 : ¬(p : ℤ) ^ 2 ∣ D n m A B) :
    ¬p ∣ RingOfIntegers.exponent θ := by
  have hn : 2 ≤ n := by omega
  by_cases hpA : (p : ℤ) ∣ A
  · -- Case 1: `p ∣ A`, use the Eisenstein criterion
    exact RingOfIntegers.not_dvd_exponent_of_minpoly_isEisensteinAt hgen
      (hθ ▸ isEisensteinAt_jones (Nat.prime_iff_prime_int.mp hp.out) hmn hpA hA2)
  by_cases hpD : (p : ℤ) ∣ D n m A B
  · -- Case 2: `p ∤ A`, `p ∣ D`: tame double root at the lift `a`
    obtain ⟨hpn, hpB, hpm, hpnm⟩ := not_dvd_of_dvd_D hp.out hm hmn hgcd hpA hpD
    obtain ⟨a, ha, hcop2, hkey2a, hfa, hf'a⟩ :=
      exists_lift_double_root hp.out hm hmn hgcd hpA hpD
    have hpa : (p : ℤ) ∣ B * ((n : ℤ) - m) * a + n :=
      (dvd_pow_self (p : ℤ) two_ne_zero).trans ha
    -- facts about `x = a` in `ZMod p`
    have hpF0 : ∀ t : ℤ, ((t : ZMod p) = 0) ↔ (p : ℤ) ∣ t := fun t =>
      ZMod.intCast_zmod_eq_zero_iff_dvd t p
    have hnZ : ((n : ZMod p)) ≠ 0 := fun h => hpn (by
      rw [← hpF0]
      exact_mod_cast h)
    have hBZ : ((B : ZMod p)) ≠ 0 := fun h => hpB ((hpF0 B).mp h)
    have hmZ : ((m : ZMod p)) ≠ 0 := fun h => hpm (by
      rw [← hpF0]
      exact_mod_cast h)
    have hAZ : ((A : ZMod p)) ≠ 0 := fun h => hpA ((hpF0 A).mp h)
    -- apply the double-root criterion
    refine RingOfIntegers.not_dvd_exponent_of_sq_not_dvd_eval (r := a) hgen ?_ ?_ ?_
    · -- `p ^ 2 ∤ f(a)`
      rw [hθ, eval_jones]
      rw [dvd_eval_iff_dvd_D hmn.le ha hcop2]
      exact hD2
    · -- `p ∤ f''(a)`
      rw [hθ, eval_derivative_derivative_jones]
      intro hdvd
      have h0 := (hpF0 _).mpr hdvd
      push_cast at h0
      exact residue_second_deriv hn hAZ hBZ hmZ
        (by
          intro h
          rw [h, zero_pow hm.ne', mul_zero, add_zero,
            pow_eq_zero_iff (show n ≠ 0 by omega)] at hfa
          rw [hfa, mul_zero] at hkey2a
          exact hnZ (neg_eq_zero.mp hkey2a.symm))
        hkey2a hf'a h0
    · -- every maximal ideal above `p` containing the conductor contains `θ - a`
      intro 𝔪 h𝔪 hcond hp𝔪
      obtain ⟨hfθ, hf'θ⟩ := quotient_facts hθ hgen hcond
      have hpF𝔪 := quotient_intCast_iff h𝔪 hp𝔪
      have hkey2θ := residue_analysis hp.out hpF𝔪 hn hm hgcd hpA hfθ hf'θ
      -- `a` satisfies the same linear relation in the residue field
      have hkey2a' : ((n : 𝓞 K ⧸ 𝔪) - m) * B * ((a : ℤ) : 𝓞 K ⧸ 𝔪) = -(n : 𝓞 K ⧸ 𝔪) := by
        have h0 : ((B * ((n : ℤ) - m) * a + n : ℤ) : 𝓞 K ⧸ 𝔪) = 0 := (hpF𝔪 _).mpr hpa
        push_cast at h0
        linear_combination h0
      have hBm : ((B : 𝓞 K ⧸ 𝔪)) ≠ 0 := fun h => hpB ((hpF𝔪 B).mp h)
      have hnmm : ((n : 𝓞 K ⧸ 𝔪)) - m ≠ 0 := fun h => hpnm (by
        rw [← hpF𝔪]
        push_cast
        exact h)
      have heq : Ideal.Quotient.mk 𝔪 θ = ((a : ℤ) : 𝓞 K ⧸ 𝔪) := by
        have h1 : ((n : 𝓞 K ⧸ 𝔪) - m) * B *
            (Ideal.Quotient.mk 𝔪 θ - ((a : ℤ) : 𝓞 K ⧸ 𝔪)) = 0 := by
          linear_combination hkey2θ - hkey2a'
        have h2 := (mul_eq_zero.mp h1).resolve_left (mul_ne_zero hnmm hBm)
        exact sub_eq_zero.mp h2
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_intCast, heq, sub_self]
  · -- Case 3: `p ∤ A`, `p ∤ D`: `f` has no repeated root mod `p`
    rw [RingOfIntegers.not_dvd_exponent_iff_conductor_sup_span_eq_top]
    by_contra hsup
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hsup
    have hcond : conductor ℤ θ ≤ 𝔪 := le_trans le_sup_left hle
    have hp𝔪 : (p : 𝓞 K) ∈ 𝔪 := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    obtain ⟨hfθ, hf'θ⟩ := quotient_facts hθ hgen hcond
    have hpF𝔪 := quotient_intCast_iff h𝔪 hp𝔪
    have hkey2θ := residue_analysis hp.out hpF𝔪 hn hm hgcd hpA hfθ hf'θ
    exact hpD ((hpF𝔪 _).mp (residue_D_eq_zero hmn.le hkey2θ hfθ))

/-- Forward direction at a prime whose square divides `A`: `p` divides the exponent, by the
double-root criterion at `r = 0`. -/
private theorem dvd_exponent_of_sq_dvd_A {p : ℕ} [Fact p.Prime] (hn : 2 ≤ n) (hmn : m < n)
    (hθ : minpoly ℤ θ = X ^ n + C A * (C B * X + 1) ^ m)
    (hA2 : (p : ℤ) ^ 2 ∣ A) : p ∣ RingOfIntegers.exponent θ := by
  have hA1 : (p : ℤ) ∣ A := (dvd_pow_self _ two_ne_zero).trans hA2
  refine RingOfIntegers.dvd_exponent_of_sq_dvd_eval (r := 0) ?_ ?_ ?_
  · rw [hθ, natDegree_jones hmn]
    exact hn
  · rw [hθ, show (X ^ n + C A * (C B * X + 1) ^ m : ℤ[X]).eval 0 = A by
      rw [eval_jones]
      simp [zero_pow (show n ≠ 0 by omega)]]
    exact hA2
  · rw [hθ, show (derivative (X ^ n + C A * (C B * X + 1) ^ m) : ℤ[X]).eval 0
        = ↑m * A * B by
      rw [eval_derivative_jones]
      simp [zero_pow (show n - 1 ≠ 0 by omega)]]
    exact (hA1.mul_left _).mul_right _

/-- **Local refinement of the Kaur–Kumar theorem**: the per-prime index criterion.
Let `f = X ^ n + A (B X + 1) ^ m ∈ ℤ[X]` be the minimal polynomial of `θ : 𝓞 K`, where
`1 ≤ m < n` and `gcd (n, m B) = 1`, and suppose `θ` generates `K` over `ℚ`.  A rational
prime `p` divides the index `[𝓞 K : ℤ[θ]]` — the exponent of `θ`, in the sense of
`RingOfIntegers.exponent` — if and only if `p ^ 2 ∣ A` or `p ^ 2 ∣ D n m A B`.  The
Kaur–Kumar theorem `NumberField.KaurKumar.monogenic_iff` follows by localizing
squarefreeness at each prime. -/
theorem dvd_exponent_iff {p : ℕ} [hp : Fact p.Prime] (hm : 0 < m) (hmn : m < n)
    (hgcd : IsCoprime (n : ℤ) ((m : ℤ) * B))
    (hθ : minpoly ℤ θ = X ^ n + C A * (C B * X + 1) ^ m)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    p ∣ RingOfIntegers.exponent θ ↔ (p : ℤ) ^ 2 ∣ A ∨ (p : ℤ) ^ 2 ∣ D n m A B := by
  have hn : 2 ≤ n := by omega
  constructor
  · intro h
    by_contra hcon
    rw [not_or] at hcon
    exact not_dvd_exponent_aux hm hmn hgcd hθ hgen hcon.1 hcon.2 h
  · rintro (hA2 | hD2)
    · exact dvd_exponent_of_sq_dvd_A hn hmn hθ hA2
    · by_cases hpA : (p : ℤ) ∣ A
      · -- `p ∣ A` and `p ^ 2 ∣ D` force `p ^ 2 ∣ A`
        exact dvd_exponent_of_sq_dvd_A hn hmn hθ
          (sq_dvd_A_of_dvd_A_of_sq_dvd_D hp.out hm hmn hgcd hpA hD2)
      · -- `p ∤ A`, `p ^ 2 ∣ D`: double-root criterion at the lift `a`
        have hD1 : (p : ℤ) ∣ D n m A B := (dvd_pow_self _ two_ne_zero).trans hD2
        obtain ⟨a, ha, hcop2, -, -, hf'a⟩ :=
          exists_lift_double_root hp.out hm hmn hgcd hpA hD1
        have hpF0 : ∀ t : ℤ, ((t : ZMod p) = 0) ↔ (p : ℤ) ∣ t := fun t =>
          ZMod.intCast_zmod_eq_zero_iff_dvd t p
        refine RingOfIntegers.dvd_exponent_of_sq_dvd_eval (r := a) ?_ ?_ ?_
        · rw [hθ, natDegree_jones hmn]
          exact hn
        · rw [hθ, eval_jones, dvd_eval_iff_dvd_D hmn.le ha hcop2]
          exact hD2
        · rw [hθ, eval_derivative_jones]
          rw [← hpF0]
          push_cast
          exact hf'a

/-- **The Kaur–Kumar theorem** (conjectured by L. Jones).
Let `f = X ^ n + A (B X + 1) ^ m ∈ ℤ[X]` be the minimal polynomial of `θ : 𝓞 K`, where
`1 ≤ m < n` and `gcd (n, m B) = 1`, and suppose `θ` generates `K` over `ℚ`.  Then
`ℤ[θ] = 𝓞 K` if and only if both `A` and `D n m A B` are squarefree.

This is the globalization of the per-prime index criterion
`NumberField.KaurKumar.dvd_exponent_iff`: `ℤ[θ] = 𝓞 K` iff no prime divides the exponent of
`θ`, iff no prime squared divides `A` or `D n m A B`, iff `A` and `D n m A B` are
squarefree. -/
theorem monogenic_iff (hm : 0 < m) (hmn : m < n)
    (hgcd : IsCoprime (n : ℤ) ((m : ℤ) * B))
    (hθ : minpoly ℤ θ = X ^ n + C A * (C B * X + 1) ^ m)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    Algebra.adjoin ℤ {θ} = ⊤ ↔ Squarefree A ∧ Squarefree (D n m A B) := by
  rw [RingOfIntegers.adjoin_eq_top_iff_forall_prime_not_dvd_exponent]
  have key : ∀ p : ℕ, p.Prime → (¬p ∣ RingOfIntegers.exponent θ ↔
      ¬(p : ℤ) ^ 2 ∣ A ∧ ¬(p : ℤ) ^ 2 ∣ D n m A B) := fun p hp => by
    haveI : Fact p.Prime := ⟨hp⟩
    rw [dvd_exponent_iff hm hmn hgcd hθ hgen, not_or]
  constructor
  · intro h
    exact ⟨squarefree_int_iff.mpr fun p hp => ((key p hp).mp (h p hp)).1,
      squarefree_int_iff.mpr fun p hp => ((key p hp).mp (h p hp)).2⟩
  · rintro ⟨h1, h2⟩ p hp
    exact (key p hp).mpr ⟨squarefree_int_iff.mp h1 p hp, squarefree_int_iff.mp h2 p hp⟩

/-- **Jones' conjecture** (proved by Kaur and Kumar): for `A` prime, the polynomial
`X ^ n + A (B X + 1) ^ m` is monogenic if and only if `D n m A B` is squarefree. -/
theorem monogenic_iff_of_prime (hA : Prime A) (hm : 0 < m) (hmn : m < n)
    (hgcd : IsCoprime (n : ℤ) ((m : ℤ) * B))
    (hθ : minpoly ℤ θ = X ^ n + C A * (C B * X + 1) ^ m)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    Algebra.adjoin ℤ {θ} = ⊤ ↔ Squarefree (D n m A B) := by
  rw [monogenic_iff hm hmn hgcd hθ hgen]
  exact and_iff_right hA.irreducible.squarefree

end Main

/-! ### Remark 1.2 and Examples 1.4, 1.5 of [kaurkumar2023]

Remark 1.2 shows that the hypothesis `gcd (n, m B) = 1` in the Kaur–Kumar theorem cannot be
dropped.  Example 1.4 treats polynomials `X ^ n + a X ^ 2 + b X + p` with `b ^ 2 = 4 a p`,
and Example 1.5 the family `X ^ 3 + A (B X + 1) ^ 2` for squarefree `A`.

For the irreducibility claim in Example 1.5 the paper invokes Perron's criterion (under the
additional hypothesis `4 ≤ |B|`); here we observe that Eisenstein's criterion at any prime
factor of the squarefree integer `A ≠ ±1` applies instead, so that no hypothesis on the size
of `B` is needed.
-/

section Examples

attribute [local instance] Ideal.Quotient.field

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {n m : ℕ} {A B : ℤ}

private theorem squarefree_congr {z w : ℤ} (h : z = w) : Squarefree z ↔ Squarefree w :=
  h ▸ Iff.rfl

/-- `X ^ n + A (B X + 1) ^ m` is irreducible whenever `A` is squarefree and not `±1`, by
Eisenstein's criterion at any prime factor of `A`. -/
theorem irreducible_of_squarefree (hA : Squarefree A) (hA1 : A.natAbs ≠ 1)
    (hmn : m < n) : Irreducible (X ^ n + C A * (C B * X + 1) ^ m) := by
  obtain ⟨q, hq, hqA⟩ := Int.exists_prime_and_dvd hA1
  exact (isEisensteinAt_jones hq hmn hqA fun h =>
      hq.not_unit (hA q (by rwa [← sq]))).irreducible
    ((Ideal.span_singleton_prime hq.ne_zero).mpr hq) (monic_jones hmn).isPrimitive
    (by rw [natDegree_jones hmn]; omega)

/-- **Remark 1.2** of [kaurkumar2023]: the assumption `gcd (n, m B) = 1` in
`NumberField.KaurKumar.monogenic_iff` cannot be dropped.  The polynomial
`x ^ 3 - 6 (3 x + 1)` (that is, `n = 3`, `m = 1`, `A = -6`, `B = 3`, where
`gcd (n, m B) = 3`) is monogenic, although the quantity
`n ^ n + (-1) ^ (n + m) B ^ n (n - m) ^ (n - m) m ^ m A = -621 = -(3 ^ 3 * 23)` is not
squarefree. -/
theorem remark_1_2 (hθ : minpoly ℤ θ = X ^ 3 + C (-6) * (C 3 * X + 1) ^ 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    Algebra.adjoin ℤ {θ} = ⊤ ∧ ¬Squarefree (D 3 1 (-6) 3) := by
  constructor
  · rw [RingOfIntegers.adjoin_eq_top_iff_forall_prime_not_dvd_exponent]
    intro p hp
    haveI : Fact p.Prime := ⟨hp⟩
    -- at `p = 2` and `p = 3` the polynomial is Eisenstein
    rcases eq_or_ne p 2 with rfl | hp2
    · refine RingOfIntegers.not_dvd_exponent_of_minpoly_isEisensteinAt hgen ?_
      rw [hθ]
      exact isEisensteinAt_jones (Nat.prime_iff_prime_int.mp hp) (by norm_num)
        (by norm_num) (by norm_num)
    rcases eq_or_ne p 3 with rfl | hp3
    · refine RingOfIntegers.not_dvd_exponent_of_minpoly_isEisensteinAt hgen ?_
      rw [hθ]
      exact isEisensteinAt_jones (Nat.prime_iff_prime_int.mp hp) (by norm_num)
        (by norm_num) (by norm_num)
    rcases eq_or_ne p 23 with rfl | hp23
    · -- at `p = 23` there is a tame double root at `11`
      refine RingOfIntegers.not_dvd_exponent_of_sq_not_dvd_eval (r := 11) hgen ?_ ?_ ?_
      · rw [hθ, eval_jones]
        norm_num
      · rw [hθ, eval_derivative_derivative_jones]
        norm_num
      · intro 𝔪 h𝔪 hcond hp𝔪
        obtain ⟨hf, hf'⟩ := quotient_facts hθ hgen hcond
        have hpF := quotient_intCast_iff h𝔪 hp𝔪
        set x := Ideal.Quotient.mk 𝔪 θ with hx
        -- both `θ` and `11` satisfy `36 y + 18 = 0` in the residue field
        have e1 : (36 : 𝓞 K ⧸ 𝔪) * x + 18 = 0 := by
          linear_combination (norm := (push_cast; ring_nf)) x * hf' - 3 * hf
        have e2 : (36 : 𝓞 K ⧸ 𝔪) * ((11 : ℤ) : 𝓞 K ⧸ 𝔪) + 18 = 0 := by
          have h414 : ((414 : ℤ) : 𝓞 K ⧸ 𝔪) = 0 := (hpF 414).mpr (by norm_num)
          linear_combination (norm := (push_cast; ring_nf)) h414
        have h36 : ((36 : ℤ) : 𝓞 K ⧸ 𝔪) ≠ 0 := fun h => by
          have := (hpF 36).mp h
          norm_num at this
        have heq : x = ((11 : ℤ) : 𝓞 K ⧸ 𝔪) := by
          have h1 : ((36 : ℤ) : 𝓞 K ⧸ 𝔪) * (x - ((11 : ℤ) : 𝓞 K ⧸ 𝔪)) = 0 := by
            linear_combination (norm := (push_cast; ring_nf)) e1 - e2
          exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left h36)
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_intCast, ← hx, heq, sub_self]
    -- at all other primes `f` has no repeated root mod `p`
    rw [RingOfIntegers.not_dvd_exponent_iff_conductor_sup_span_eq_top]
    by_contra hsup
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hsup
    have hcond : conductor ℤ θ ≤ 𝔪 := le_trans le_sup_left hle
    have hp𝔪 : (p : 𝓞 K) ∈ 𝔪 := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    obtain ⟨hf, hf'⟩ := quotient_facts hθ hgen hcond
    have hpF := quotient_intCast_iff h𝔪 hp𝔪
    set x := Ideal.Quotient.mk 𝔪 θ with hx
    -- the Bezout identity `(18 - 36 x) f(x) + (12 x² - 6 x - 144) f'(x) = 2484`
    have h2484 : ((2484 : ℤ) : 𝓞 K ⧸ 𝔪) = 0 := by
      linear_combination (norm := (push_cast; ring_nf))
        (18 - 36 * x) * hf + (12 * x ^ 2 - 6 * x - 144) * hf'
    have hdvd : p ∣ 2484 := by exact_mod_cast (hpF 2484).mp h2484
    -- `2484 = 2 ^ 2 * 3 ^ 3 * 23`, so `p ∈ {2, 3, 23}`
    have h1 : p ∣ 2 ^ 2 * (3 ^ 3 * 23) := by
      rwa [show 2 ^ 2 * (3 ^ 3 * 23) = 2484 by norm_num]
    rcases (Nat.Prime.dvd_mul hp).mp h1 with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h))
    · exact hp23 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h)
  · -- `-621` is divisible by `3 ^ 2`
    intro h
    have h9 := h 3 (by rw [D]; norm_num)
    rw [Int.isUnit_iff] at h9
    norm_num at h9

/-- The decomposition underlying Example 1.4 of [kaurkumar2023]: if `p` is an odd prime and
`b ^ 2 = 4 a p`, then `a = p B ^ 2` and `b = 2 p B` for some integer `B`. -/
theorem exists_eq_mul_sq_of_sq_eq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a b : ℤ}
    (hab : b ^ 2 = 4 * a * p) : ∃ B : ℤ, a = p * B ^ 2 ∧ b = 2 * p * B := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpb : (p : ℤ) ∣ b := hpp.dvd_of_dvd_pow (n := 2) ⟨4 * a, by linarith⟩
  obtain ⟨c, rfl⟩ := hpb
  have hpc : (p : ℤ) * c ^ 2 = 4 * a := by
    have h1 : (p : ℤ) * ((p : ℤ) * c ^ 2) = (p : ℤ) * (4 * a) := by ring_nf; linarith [hab]
    exact mul_left_cancel₀ hp0 h1
  have h2c : (2 : ℤ) ∣ c := by
    have h4 : (4 : ℤ) ∣ (p : ℤ) * c ^ 2 := ⟨a, by linarith⟩
    have h2p : ¬(2 : ℤ) ∣ (p : ℤ) := by
      intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (by exact_mod_cast h)).symm
    have hcop : IsCoprime (4 : ℤ) ((p : ℤ)) := by
      have := (Int.prime_two.coprime_iff_not_dvd.mpr h2p).pow_left (m := 2)
      norm_num at this
      exact this
    have h4c : (4 : ℤ) ∣ c ^ 2 := hcop.dvd_of_dvd_mul_left h4
    rcases Int.even_or_odd c with h | h
    · exact h.two_dvd
    · exfalso
      obtain ⟨k, rfl⟩ := h
      obtain ⟨t, ht⟩ := h4c
      have h1 : 4 * (k ^ 2 + k) + 1 = 4 * t := by linear_combination ht
      omega
  obtain ⟨B, rfl⟩ := h2c
  exact ⟨B, by linarith, by ring⟩

/-- The polynomial of Example 1.4 in the form of the Kaur–Kumar theorem. -/
private theorem ex14_poly {p : ℕ} {B : ℤ} {n : ℕ} :
    (X ^ n + C ((p : ℤ) * B ^ 2) * X ^ 2 + C (2 * (p : ℤ) * B) * X + C (p : ℤ) : ℤ[X]) =
      X ^ n + C (p : ℤ) * (C B * X + 1) ^ 2 := by
  simp only [eq_intCast]
  push_cast
  ring

/-- The irreducibility claim of **Example 1.4** of [kaurkumar2023]:
`X ^ n + p B ^ 2 X ^ 2 + 2 p B X + p` is irreducible by Eisenstein's criterion. -/
theorem irreducible_example_1_4 {p : ℕ} (hp : p.Prime) {B : ℤ} {n : ℕ} (hn : 2 < n) :
    Irreducible
      (X ^ n + C ((p : ℤ) * B ^ 2) * X ^ 2 + C (2 * (p : ℤ) * B) * X + C (p : ℤ)) := by
  rw [ex14_poly]
  exact irreducible_of_prime (Nat.prime_iff_prime_int.mp hp) (by omega)

/-- **Example 1.4** of [kaurkumar2023]: let `p` be a prime and `f = X ^ n + a X ^ 2 + b X + p`
with `b ^ 2 = 4 a p`, so that `a = p B ^ 2` and `b = 2 p B` with `B = b / (2 p)` (see
`exists_eq_mul_sq_of_sq_eq`).  If `gcd (n, 2 B) = 1`, then `f` is monogenic if and only if
`n ^ n + (-1) ^ n 4 B ^ n (n - 2) ^ (n - 2) p` is squarefree. -/
theorem example_1_4 {p : ℕ} (hp : p.Prime) {B : ℤ} {n : ℕ} (hn : 2 < n)
    (hgcd : IsCoprime (n : ℤ) (2 * B))
    (hθ : minpoly ℤ θ =
      X ^ n + C ((p : ℤ) * B ^ 2) * X ^ 2 + C (2 * (p : ℤ) * B) * X + C (p : ℤ))
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    Algebra.adjoin ℤ {θ} = ⊤ ↔
      Squarefree ((n : ℤ) ^ n + (-1) ^ n * 4 * B ^ n * ((n : ℤ) - 2) ^ (n - 2) * p) := by
  rw [monogenic_iff (by norm_num) (by omega) (by push_cast; exact hgcd)
    (hθ.trans ex14_poly) hgen,
    and_iff_right (Nat.prime_iff_prime_int.mp hp).irreducible.squarefree]
  exact squarefree_congr (by rw [D]; push_cast [pow_add]; ring)

/-- The irreducibility claim of **Example 1.5** of [kaurkumar2023]: for squarefree
`A ≠ ±1`, the polynomial `X ^ 3 + A (B X + 1) ^ 2` is irreducible.  (The paper uses Perron's
criterion, assuming moreover `4 ≤ |B|`; Eisenstein's criterion at a prime factor of `A`
applies without any hypothesis on `B`.) -/
theorem irreducible_example_1_5 {A B : ℤ} (hA : Squarefree A) (hA1 : A.natAbs ≠ 1) :
    Irreducible (X ^ 3 + C A * (C B * X + 1) ^ 2) :=
  irreducible_of_squarefree hA hA1 (by norm_num)

/-- **Example 1.5** of [kaurkumar2023]: for `3 ∤ B` and squarefree `A`, the polynomial
`X ^ 3 + A (B X + 1) ^ 2` is monogenic if and only if `4 A B ^ 3 - 27` is squarefree. -/
theorem example_1_5 (hA : Squarefree A) (hB : ¬(3 : ℤ) ∣ B)
    (hθ : minpoly ℤ θ = X ^ 3 + C A * (C B * X + 1) ^ 2)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    Algebra.adjoin ℤ {θ} = ⊤ ↔ Squarefree (4 * A * B ^ 3 - 27) := by
  have h3 : IsCoprime ((3 : ℕ) : ℤ) (((2 : ℕ) : ℤ) * B) := by
    push_cast
    exact Int.prime_three.coprime_iff_not_dvd.mpr fun h =>
      ((Int.prime_three.dvd_mul.mp h).resolve_left (by norm_num) : (3 : ℤ) ∣ B) |> hB
  rw [monogenic_iff (by norm_num) (by norm_num) h3 hθ hgen,
    and_iff_right hA]
  calc Squarefree (D 3 2 A B)
      ↔ Squarefree (-(4 * A * B ^ 3 - 27)) := squarefree_congr (by rw [D]; push_cast; ring)
    _ ↔ Squarefree (4 * A * B ^ 3 - 27) := by
        rw [← Int.squarefree_natAbs, Int.natAbs_neg, Int.squarefree_natAbs]

end Examples

end NumberField.KaurKumar

