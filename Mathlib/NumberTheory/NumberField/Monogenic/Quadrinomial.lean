/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.Monogenic.Pure
public import Mathlib.NumberTheory.NumberField.Monogenic.Dedekind

/-!
# Monogenicity of `X ^ n + a X ^ 2 + 2 B X + c` with `B ^ 2 = a c`

Let `f = X ^ n + a X ^ 2 + b X + c ∈ ℤ[X]` be irreducible with `b ^ 2 = 4 a c` (so `b = 2 B`
is even and `B ^ 2 = a c`: the quadratic part is a degenerate square), and let `θ` be a root
of `f` generating the number field `K`.  This file works towards Theorem 1.1 of
Jakhar--Kaur--Kumar [jakharkaurkumar2023], the per-prime criterion for
`p ∣ [𝓞 K : ℤ[θ]]`, with the discriminant-free toolkit of this directory.  Currently
formalized:

* `NumberField.Quadrinomial.D`: the discriminant-like constant
  `D = n ^ n (-c) ^ (n - 1) - 4 (n - 2) ^ (n - 2) B ^ n` (equal to `± disc f` by
  [jakharkaurkumar2023, Lemma 2.2], which we do not need).
* `NumberField.Quadrinomial.modEq_key`: the fundamental congruence: if
  `N ∣ a (n - 2) d + n B` then
  `B ^ (n - 2) (a (n - 2)) ^ n f(d) ≡ - a ^ (n - 1) D  [ZMOD N]`,
  the analogue of the Kaur--Kumar congruence, again eliminating all discriminant
  computations; with the divisibility transfer `dvd_eval_iff_dvd_D`.
* `NumberField.Quadrinomial.dvd_exponent_iff_of_dvd_of_dvd` — **case (1) of Theorem 1.1**
  (`p ∣ a` and `p ∣ c`): `p ∣ [𝓞 K : ℤ[θ]]` iff `p ^ 2 ∣ c`.
* `NumberField.Quadrinomial.dvd_exponent_of_sq_dvd_of_sq_dvd` — the necessity half of
  **case (2)** in the totally wild subcase: if `p ^ 2` divides `a`, `2 * B` and
  `c + (-c) ^ p ^ r` (with `n = p ^ r * m`, `r ≥ 1`), then `p ∣ [𝓞 K : ℤ[θ]]`, by the
  generalized obstruction lemma at the repeated factor `X ^ m + c`.
* `NumberField.Quadrinomial.dvd_exponent_iff_of_not_dvd` — **case (5) of Theorem 1.1**, in
  full (`p ∤ b = 2 B`): `p ∣ [𝓞 K : ℤ[θ]]` iff `p ^ 2 ∣ D`.  The residue analysis shows
  that the resolvent `a (n - 2) x ^ 2 + 2 B (n - 1) x + n c` (with discriminant `4 B ^ 2`,
  by `B ^ 2 = a c`) factors as `(a (n - 2) x + n B) (a (n - 2) x + (n - 2) B)` up to a unit,
  that the root `- B / a` of the second factor is not a root of `f̄`, and that the double
  root `- n B / (a (n - 2))` is tame (`f̄'' (x) x = 2 B ≠ 0`); necessity and sufficiency
  then follow from the double-root criteria of `DoubleRoot.lean` exactly as in the
  Kaur--Kumar theorem.

* `NumberField.Quadrinomial.dvd_exponent_of_dvd_of_not_dvd` — **corrected case (3)**: if
  `p ∣ c` and `p ∤ a` then `p` *always* divides the index (since `B ^ 2 = a c` forces
  `p ^ 2 ∣ c`, making `0` an obstructing double root).  This **contradicts case (3) of
  Theorem 1.1 as printed** in [jakharkaurkumar2023]; see the docstring for a concrete
  counterexample to the printed criterion.
* `NumberField.Quadrinomial.dvd_exponent_of_dvd_of_dvd_eval` — necessity in case (2), the
  rational-common-root subcase, completing (with the totally wild subcase above) the
  necessity half of case (2).
* `NumberField.Quadrinomial.two_dvd_exponent_of_mod_four` — necessity in **case (4)**
  (`p = 2`, `n = 2 m`, `a ≡ c ≡ 3 mod 4`), via the exact identity
  `f = h ^ 2 - 2 (a X + c) h + ((a + a ^ 2) X ^ 2 + (2 a c + 2 B) X + (c + c ^ 2))` with
  `h = X ^ m + a X + c` and the generalized obstruction lemma.

What remains of Theorem 1.1 is exactly the *sufficiency* halves of the wild cases (2) and
(4): these are the genuinely open formalization problem (they would follow from a general
Dedekind criterion, or from a new descent argument — the pure-field subfield trick has no
analogue here; a single-prime valuation argument provably cannot decide them).

## References

* [A. Jakhar, S. Kaur, S. Kumar, *On power basis of a class of number fields*,
  arXiv:2303.03138 (2023)][jakharkaurkumar2023]
-/

set_option linter.style.longFile 1700

@[expose] public section

noncomputable section

open Polynomial NumberField Ideal

namespace NumberField.Quadrinomial

/-! ### Elementary facts about the polynomial -/

section PolynomialLemmas

variable {n : ℕ} {a B c : ℤ}

/-- The quadrinomial `X ^ n + a X ^ 2 + 2 B X + c`. -/
private def q (n : ℕ) (a B c : ℤ) : ℤ[X] :=
  X ^ n + (C a * X ^ 2 + C (2 * B) * X + C c)

private theorem degree_lower_lt (hn : 3 ≤ n) :
    (C a * X ^ 2 + C (2 * B) * X + C c : ℤ[X]).degree < (n : WithBot ℕ) :=
  lt_of_le_of_lt (Polynomial.degree_quadratic_le) (by exact_mod_cast hn)

private theorem monic_q (hn : 3 ≤ n) : (q n a B c).Monic :=
  Polynomial.monic_X_pow_add (degree_lower_lt hn)

private theorem natDegree_q (hn : 3 ≤ n) : (q n a B c).natDegree = n :=
  Polynomial.natDegree_eq_of_degree_eq_some (by
    rw [q, Polynomial.degree_add_eq_left_of_degree_lt
      (by rw [Polynomial.degree_X_pow]; exact degree_lower_lt hn), Polynomial.degree_X_pow])

private theorem eval_q (d : ℤ) :
    (q n a B c).eval d = d ^ n + a * d ^ 2 + 2 * B * d + c := by
  simp [q]
  ring

private theorem derivative_q :
    derivative (q n a B c) = C (n : ℤ) * X ^ (n - 1) + (C (2 * a) * X + C (2 * B)) := by
  rw [q, derivative_add, derivative_X_pow, derivative_add, derivative_add, derivative_mul,
    derivative_mul, derivative_C, derivative_C, derivative_C, derivative_X, derivative_X_pow]
  simp only [map_mul]
  ring

private theorem eval_derivative_q (d : ℤ) :
    (derivative (q n a B c)).eval d = n * d ^ (n - 1) + 2 * a * d + 2 * B := by
  rw [derivative_q]
  simp
  ring

private theorem eval_derivative_derivative_q (d : ℤ) :
    (derivative (derivative (q n a B c))).eval d
      = (n : ℤ) * ((n - 1 : ℕ) : ℤ) * d ^ (n - 2) + 2 * a := by
  rw [derivative_q, derivative_add, derivative_add, derivative_mul, derivative_mul,
    derivative_C, derivative_C, derivative_X, derivative_X_pow]
  have h2 : n - 1 - 1 = n - 2 := by omega
  simp [h2]
  ring

end PolynomialLemmas

/-! ### The constant `D` and the fundamental congruence -/

/-- The discriminant-like constant of the quadrinomial family:
`D = n ^ n (-c) ^ (n - 1) - 4 (n - 2) ^ (n - 2) B ^ n`.  By Lemma 2.2 of
[jakharkaurkumar2023] this equals `± disc f`; as with the Kaur--Kumar constant, no such
identification is needed here: all divisibility information flows through
`NumberField.Quadrinomial.modEq_key`. -/
def D (n : ℕ) (B c : ℤ) : ℤ :=
  (n : ℤ) ^ n * (-c) ^ (n - 1) - 4 * ((n : ℤ) - 2) ^ (n - 2) * B ^ n

section IntegerLemmas

variable {n : ℕ} {a B c : ℤ}

/-- **The fundamental congruence** for the quadrinomial family: if
`N ∣ a (n - 2) d + n B` and `B ^ 2 = a c`, then
`B ^ (n - 2) (a (n - 2)) ^ n f(d) ≡ - a ^ (n - 1) D  [ZMOD N]`. -/
theorem modEq_key (hn : 3 ≤ n) (hB : B ^ 2 = a * c) {d N : ℤ}
    (hα : N ∣ a * ((n : ℤ) - 2) * d + n * B) :
    B ^ (n - 2) * (a * ((n : ℤ) - 2)) ^ n * (d ^ n + a * d ^ 2 + 2 * B * d + c) ≡
      -a ^ (n - 1) * D n B c [ZMOD N] := by
  set z : ℤ := a * ((n : ℤ) - 2) with hz
  have hzd : z * d ≡ -((n : ℤ) * B) [ZMOD N] := by
    rw [Int.modEq_iff_dvd]
    have h1 : -((n : ℤ) * B) - z * d = -(z * d + n * B) := by ring
    rw [h1]
    exact dvd_neg.mpr hα
  -- the two power congruences
  have h1 : (z * d) ^ n ≡ (-((n : ℤ) * B)) ^ n [ZMOD N] := hzd.pow n
  have h2 : a * (z * d) ^ 2 + 2 * B * z * (z * d) + c * z ^ 2 ≡ 4 * a * B ^ 2 [ZMOD N] := by
    have hs1 : a * (z * d) ^ 2 ≡ a * (-((n : ℤ) * B)) ^ 2 [ZMOD N] := (hzd.pow 2).mul_left a
    have hs2 : 2 * B * z * (z * d) ≡ 2 * B * z * (-((n : ℤ) * B)) [ZMOD N] :=
      hzd.mul_left (2 * B * z)
    have hs3 := (hs1.add hs2).add_right (c * z ^ 2)
    have halg : a * (-((n : ℤ) * B)) ^ 2 + 2 * B * z * (-((n : ℤ) * B)) + c * z ^ 2
        = 4 * a * B ^ 2 := by
      rw [hz]
      linear_combination (a * ((n : ℤ) ^ 2 - 2 * ((n : ℤ) - 2) * (n : ℤ) - 4)) * hB
    rw [halg] at hs3
    exact hs3
  -- expand the left-hand side
  have hsplit : z ^ n = z ^ (n - 2) * z ^ 2 := (pow_sub_mul_pow z (by omega : 2 ≤ n)).symm
  have hexp : B ^ (n - 2) * z ^ n * (d ^ n + a * d ^ 2 + 2 * B * d + c)
      = B ^ (n - 2) * ((z * d) ^ n +
          z ^ (n - 2) * (a * (z * d) ^ 2 + 2 * B * z * (z * d) + c * z ^ 2)) := by
    calc B ^ (n - 2) * z ^ n * (d ^ n + a * d ^ 2 + 2 * B * d + c)
        = B ^ (n - 2) * (z ^ n * d ^ n + z ^ n * (a * d ^ 2) + z ^ n * (2 * B * d)
            + z ^ n * c) := by ring
      _ = B ^ (n - 2) * ((z * d) ^ n + z ^ (n - 2) * (a * (z * d) ^ 2)
            + z ^ (n - 2) * (2 * B * z * (z * d)) + z ^ (n - 2) * (c * z ^ 2)) := by
          rw [mul_pow z d, hsplit]
          ring
      _ = B ^ (n - 2) * ((z * d) ^ n +
            z ^ (n - 2) * (a * (z * d) ^ 2 + 2 * B * z * (z * d) + c * z ^ 2)) := by ring
  -- assemble, and identify the right-hand side with `- a ^ (n - 1) * D`
  have hcong : B ^ (n - 2) * z ^ n * (d ^ n + a * d ^ 2 + 2 * B * d + c) ≡
      B ^ (n - 2) * ((-((n : ℤ) * B)) ^ n + z ^ (n - 2) * (4 * a * B ^ 2)) [ZMOD N] := by
    rw [hexp]
    exact (h1.add (h2.mul_left (z ^ (n - 2)))).mul_left (B ^ (n - 2))
  have hfinal : B ^ (n - 2) * ((-((n : ℤ) * B)) ^ n + z ^ (n - 2) * (4 * a * B ^ 2))
      = -a ^ (n - 1) * D n B c := by
    rw [hz, D]
    have hBpow : B ^ (n - 2) * B ^ n = (B ^ 2) ^ (n - 1) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    have hBsq : B ^ (n - 2) * B ^ 2 = B ^ n := pow_sub_mul_pow B (by omega : 2 ≤ n)
    have hapow : a * a ^ (n - 2) = a ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hcpow : (B ^ 2) ^ (n - 1) = a ^ (n - 1) * c ^ (n - 1) := by
      rw [hB, mul_pow]
    have hneg : (-((n : ℤ) * B)) ^ n = (-1) ^ n * ((n : ℤ) ^ n * B ^ n) := by
      rw [neg_pow, mul_pow]
    have hnegc : (-c) ^ (n - 1) = (-1) ^ (n - 1) * c ^ (n - 1) := neg_pow c (n - 1)
    have hone2 : (-1 : ℤ) ^ n + (-1 : ℤ) ^ (n - 1) = 0 := by
      obtain ⟨j, hj⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
      subst hj
      rw [Nat.add_sub_cancel, pow_succ]
      ring
    have hmulpow : (a * ((n : ℤ) - 2)) ^ (n - 2) = a ^ (n - 2) * ((n : ℤ) - 2) ^ (n - 2) :=
      mul_pow a _ _
    calc B ^ (n - 2) * ((-((n : ℤ) * B)) ^ n
          + (a * ((n : ℤ) - 2)) ^ (n - 2) * (4 * a * B ^ 2))
        = (-1) ^ n * ((n : ℤ) ^ n * (B ^ (n - 2) * B ^ n))
          + 4 * (a * a ^ (n - 2)) * ((n : ℤ) - 2) ^ (n - 2) * (B ^ (n - 2) * B ^ 2) := by
          rw [hneg, hmulpow]
          ring
      _ = (-1) ^ n * ((n : ℤ) ^ n * (a ^ (n - 1) * c ^ (n - 1)))
          + 4 * a ^ (n - 1) * ((n : ℤ) - 2) ^ (n - 2) * B ^ n := by
          rw [hBpow, hcpow, hBsq, hapow]
      _ = -a ^ (n - 1) * ((n : ℤ) ^ n * ((-1) ^ (n - 1) * c ^ (n - 1))
            - 4 * ((n : ℤ) - 2) ^ (n - 2) * B ^ n) := by
          linear_combination ((n : ℤ) ^ n * a ^ (n - 1) * c ^ (n - 1)) * hone2
      _ = -a ^ (n - 1) * ((n : ℤ) ^ n * (-c) ^ (n - 1)
            - 4 * ((n : ℤ) - 2) ^ (n - 2) * B ^ n) := by
          rw [hnegc]
  calc B ^ (n - 2) * z ^ n * (d ^ n + a * d ^ 2 + 2 * B * d + c)
      ≡ B ^ (n - 2) * ((-((n : ℤ) * B)) ^ n + z ^ (n - 2) * (4 * a * B ^ 2)) [ZMOD N] := hcong
    _ = -a ^ (n - 1) * D n B c := hfinal

/-- Transfer of divisibility through the fundamental congruence: for `N` coprime to
`a`, `B` and `n - 2`, `N ∣ f(d) ↔ N ∣ D`. -/
theorem dvd_eval_iff_dvd_D (hn : 3 ≤ n) (hB : B ^ 2 = a * c) {d N : ℤ}
    (hα : N ∣ a * ((n : ℤ) - 2) * d + n * B)
    (hcopa : IsCoprime N a) (hcopB : IsCoprime N B) (hcopn : IsCoprime N ((n : ℤ) - 2)) :
    N ∣ d ^ n + a * d ^ 2 + 2 * B * d + c ↔ N ∣ D n B c := by
  have hkey := modEq_key hn hB hα
  have hd : N ∣ -a ^ (n - 1) * D n B c -
      B ^ (n - 2) * (a * ((n : ℤ) - 2)) ^ n * (d ^ n + a * d ^ 2 + 2 * B * d + c) :=
    hkey.dvd
  constructor
  · intro h
    have h2 : N ∣ -a ^ (n - 1) * D n B c := by
      have h3 := dvd_add hd (h.mul_left (B ^ (n - 2) * (a * ((n : ℤ) - 2)) ^ n))
      simpa using h3
    rw [neg_mul] at h2
    exact hcopa.pow_right.dvd_of_dvd_mul_left (dvd_neg.mp h2)
  · intro h
    have h2 : N ∣ B ^ (n - 2) * (a * ((n : ℤ) - 2)) ^ n *
        (d ^ n + a * d ^ 2 + 2 * B * d + c) := by
      have h3 := dvd_sub (h.mul_left (-a ^ (n - 1))) hd
      simpa using h3
    exact (hcopB.pow_right.mul_right
      ((hcopa.mul_right hcopn).pow_right)).dvd_of_dvd_mul_left h2

/-- For `p ∤ 2B` (with `B ^ 2 = a c`), `p` divides neither `a` nor `c`. -/
private theorem not_dvd_a_c {p : ℕ} (hp : p.Prime) (hB : B ^ 2 = a * c)
    (hp2B : ¬(p : ℤ) ∣ 2 * B) : ¬(p : ℤ) ∣ a ∧ ¬(p : ℤ) ∣ c := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpB : ¬(p : ℤ) ∣ B := fun h => hp2B (h.mul_left 2)
  constructor
  · intro h
    exact hpB (hpp.dvd_of_dvd_pow (n := 2) (by rw [hB]; exact h.mul_right c))
  · intro h
    exact hpB (hpp.dvd_of_dvd_pow (n := 2) (by rw [hB]; exact h.mul_left a))

/-- If `p ∤ 2B` and `p ∣ D`, then `p` divides neither `n` nor `n - 2`. -/
private theorem not_dvd_of_dvd_D {p : ℕ} (hp : p.Prime) (hn : 3 ≤ n) (hB : B ^ 2 = a * c)
    (hp2B : ¬(p : ℤ) ∣ 2 * B) (hD : (p : ℤ) ∣ D n B c) :
    ¬(p : ℤ) ∣ (n : ℤ) ∧ ¬(p : ℤ) ∣ ((n : ℤ) - 2) := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpB : ¬(p : ℤ) ∣ B := fun h => hp2B (h.mul_left 2)
  have hp2 : ¬(p : ℤ) ∣ 2 := fun h => hp2B (h.mul_right B)
  have hpc : ¬(p : ℤ) ∣ c := (not_dvd_a_c hp hB hp2B).2
  have h4 : ¬(p : ℤ) ∣ 4 := fun h => by
    rcases hpp.dvd_mul.mp (show (p : ℤ) ∣ 2 * 2 by norm_num at h ⊢; omega) with h1 | h1 <;>
      exact hp2 h1
  constructor
  · intro hdvd
    have h1 : (p : ℤ) ∣ (n : ℤ) ^ n * (-c) ^ (n - 1) :=
      (hdvd.pow (show n ≠ 0 by omega)).mul_right _
    have h2 : (p : ℤ) ∣ 4 * ((n : ℤ) - 2) ^ (n - 2) * B ^ n := by
      have h3 := dvd_sub h1 hD
      rw [D] at h3
      simpa using h3
    rcases hpp.dvd_mul.mp h2 with h3 | h3
    · rcases hpp.dvd_mul.mp h3 with h5 | h5
      · exact h4 h5
      · have h6 := hpp.dvd_of_dvd_pow h5
        have h7 : (p : ℤ) ∣ 2 := by
          have := dvd_sub hdvd h6
          simpa using this
        exact hp2 h7
    · exact hpB (hpp.dvd_of_dvd_pow h3)
  · intro hdvd
    have h1 : (p : ℤ) ∣ 4 * ((n : ℤ) - 2) ^ (n - 2) * B ^ n :=
      ((hdvd.pow (show n - 2 ≠ 0 by omega)).mul_left 4).mul_right _
    have h2 : (p : ℤ) ∣ (n : ℤ) ^ n * (-c) ^ (n - 1) := by
      have h3 := dvd_add hD h1
      rw [D] at h3
      simpa using h3
    rcases hpp.dvd_mul.mp h2 with h3 | h3
    · have h5 := hpp.dvd_of_dvd_pow h3
      have h6 : (p : ℤ) ∣ 2 := by
        have := dvd_sub h5 hdvd
        simpa using this
      exact hp2 h6
    · have h5 := hpp.dvd_of_dvd_pow h3
      rw [dvd_neg] at h5
      exact hpc h5

/-- A Bezout lift: if `p ∤ a (n - 2)` there is `d` with `p ^ 2 ∣ a (n - 2) d + n B`. -/
private theorem exists_lift {p : ℕ} (hp : p.Prime) (hpa : ¬(p : ℤ) ∣ a)
    (hpn2 : ¬(p : ℤ) ∣ ((n : ℤ) - 2)) :
    ∃ d : ℤ, (p : ℤ) ^ 2 ∣ a * ((n : ℤ) - 2) * d + n * B := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hz : ¬(p : ℤ) ∣ a * ((n : ℤ) - 2) := fun h =>
    (hpp.dvd_mul.mp h).elim hpa hpn2
  have hcop : IsCoprime ((p : ℤ) ^ 2) (a * ((n : ℤ) - 2)) :=
    (hpp.coprime_iff_not_dvd.mpr hz).pow_left
  obtain ⟨u, v, huv⟩ := hcop
  exact ⟨-((n : ℤ) * B) * v, (n : ℤ) * B * u, by linear_combination (-((n : ℤ) * B)) * huv⟩

end IntegerLemmas

/-! ### Case (5): residue analysis at the tame double root -/

section ResidueAnalysis

variable {F : Type*} [Field F] {p n : ℕ} {a B c : ℤ}

/-- The field-valued avatar of the fundamental congruence: under the linear relation
`a (n - 2) x = - n B`, one has `B^(n-2) (a(n-2))^n f(x) = - a^(n-1) D` in `F`. -/
private theorem val_identity (hn : 3 ≤ n) (hB : B ^ 2 = a * c) {x : F}
    (hkey : (a : F) * ((n : F) - 2) * x = -((n : F) * (B : F))) :
    (B : F) ^ (n - 2) * ((a : F) * ((n : F) - 2)) ^ n *
      (x ^ n + (a : F) * x ^ 2 + 2 * (B : F) * x + (c : F))
      = -(a : F) ^ (n - 1) * ((D n B c : ℤ) : F) := by
  have e2 : (B : F) ^ 2 = (a : F) * (c : F) := by
    exact_mod_cast congrArg (Int.cast (R := F)) hB
  set z : F := (a : F) * ((n : F) - 2) with hz
  have h1 : (z * x) ^ n = (-((n : F) * (B : F))) ^ n := by rw [hkey]
  have h2 : (a : F) * (z * x) ^ 2 + 2 * (B : F) * z * (z * x) + (c : F) * z ^ 2
      = 4 * (a : F) * (B : F) ^ 2 := by
    rw [hkey, hz]
    linear_combination ((a : F) * ((n : F) ^ 2 - 2 * ((n : F) - 2) * (n : F) - 4)) * e2
  have hsplit : z ^ n = z ^ (n - 2) * z ^ 2 := (pow_sub_mul_pow z (by omega : 2 ≤ n)).symm
  have hexp : (B : F) ^ (n - 2) * z ^ n *
      (x ^ n + (a : F) * x ^ 2 + 2 * (B : F) * x + (c : F))
      = (B : F) ^ (n - 2) * ((z * x) ^ n +
          z ^ (n - 2) * ((a : F) * (z * x) ^ 2 + 2 * (B : F) * z * (z * x)
            + (c : F) * z ^ 2)) := by
    calc (B : F) ^ (n - 2) * z ^ n * (x ^ n + (a : F) * x ^ 2 + 2 * (B : F) * x + (c : F))
        = (B : F) ^ (n - 2) * (z ^ n * x ^ n + z ^ n * ((a : F) * x ^ 2)
            + z ^ n * (2 * (B : F) * x) + z ^ n * (c : F)) := by ring
      _ = (B : F) ^ (n - 2) * ((z * x) ^ n + z ^ (n - 2) * ((a : F) * (z * x) ^ 2)
            + z ^ (n - 2) * (2 * (B : F) * z * (z * x))
            + z ^ (n - 2) * ((c : F) * z ^ 2)) := by
          rw [mul_pow z x, hsplit]
          ring
      _ = (B : F) ^ (n - 2) * ((z * x) ^ n +
            z ^ (n - 2) * ((a : F) * (z * x) ^ 2 + 2 * (B : F) * z * (z * x)
              + (c : F) * z ^ 2)) := by ring
  rw [hexp, h1, h2, hz, D]
  push_cast
  have hBpow : (B : F) ^ (n - 2) * (B : F) ^ n = ((B : F) ^ 2) ^ (n - 1) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hBsq : (B : F) ^ (n - 2) * (B : F) ^ 2 = (B : F) ^ n :=
    pow_sub_mul_pow (B : F) (by omega : 2 ≤ n)
  have hapow : (a : F) * (a : F) ^ (n - 2) = (a : F) ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hcpow : ((B : F) ^ 2) ^ (n - 1) = (a : F) ^ (n - 1) * (c : F) ^ (n - 1) := by
    rw [e2, mul_pow]
  have hneg : (-((n : F) * (B : F))) ^ n = (-1) ^ n * ((n : F) ^ n * (B : F) ^ n) := by
    rw [neg_pow, mul_pow]
  have hnegc : (-(c : F)) ^ (n - 1) = (-1) ^ (n - 1) * (c : F) ^ (n - 1) :=
    neg_pow (c : F) (n - 1)
  have hone2 : (-1 : F) ^ n + (-1 : F) ^ (n - 1) = 0 := by
    obtain ⟨j, hj⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    subst hj
    rw [Nat.add_sub_cancel, pow_succ]
    ring
  have hmulpow : ((a : F) * ((n : F) - 2)) ^ (n - 2)
      = (a : F) ^ (n - 2) * ((n : F) - 2) ^ (n - 2) := mul_pow _ _ _
  calc (B : F) ^ (n - 2) * ((-((n : F) * (B : F))) ^ n
        + ((a : F) * ((n : F) - 2)) ^ (n - 2) * (4 * (a : F) * (B : F) ^ 2))
      = (-1) ^ n * ((n : F) ^ n * ((B : F) ^ (n - 2) * (B : F) ^ n))
        + 4 * ((a : F) * (a : F) ^ (n - 2)) * ((n : F) - 2) ^ (n - 2) *
          ((B : F) ^ (n - 2) * (B : F) ^ 2) := by
        rw [hneg, hmulpow]
        ring
    _ = (-1) ^ n * ((n : F) ^ n * ((a : F) ^ (n - 1) * (c : F) ^ (n - 1)))
        + 4 * (a : F) ^ (n - 1) * ((n : F) - 2) ^ (n - 2) * (B : F) ^ n := by
        rw [hBpow, hcpow, hBsq, hapow]
    _ = -(a : F) ^ (n - 1) * ((n : F) ^ n * ((-1) ^ (n - 1) * (c : F) ^ (n - 1))
          - 4 * ((n : F) - 2) ^ (n - 2) * (B : F) ^ n) := by
        linear_combination ((n : F) ^ n * (a : F) ^ (n - 1) * (c : F) ^ (n - 1)) * hone2
    _ = -(a : F) ^ (n - 1) * ((n : F) ^ n * (-(c : F)) ^ (n - 1)
          - 4 * ((n : F) - 2) ^ (n - 2) * (B : F) ^ n) := by
        rw [hnegc]

/-- **Residue analysis for case (5)**: in a field where the integers reduce with kernel
`p ℤ` and `p ∤ 2B`, a common root `x` of `f̄` and `f̄'` satisfies the linear relation
`a (n - 2) x = - n B`; along the way, `(n : F) ≠ 0`, `(n : F) - 2 ≠ 0` and `x ≠ 0`. -/
private theorem residue_analysis (hpF : ∀ t : ℤ, ((t : F) = 0) ↔ (p : ℤ) ∣ t)
    (hn : 3 ≤ n) (hB : B ^ 2 = a * c) (hp2B : ¬(p : ℤ) ∣ 2 * B) {x : F}
    (hf : x ^ n + (a : F) * x ^ 2 + 2 * (B : F) * x + (c : F) = 0)
    (hf' : (n : F) * x ^ (n - 1) + 2 * (a : F) * x + 2 * (B : F) = 0) :
    (a : F) * ((n : F) - 2) * x = -((n : F) * (B : F)) ∧
      (n : F) ≠ 0 ∧ (n : F) - 2 ≠ 0 ∧ x ≠ 0 := by
  have hpB : ¬(p : ℤ) ∣ B := fun h => hp2B (h.mul_left 2)
  have hp2 : ¬(p : ℤ) ∣ 2 := fun h => hp2B (h.mul_right B)
  have hBF : (B : F) ≠ 0 := fun h => hpB ((hpF B).mp h)
  have h2F : (2 : F) ≠ 0 := fun h => hp2 ((hpF 2).mp (by exact_mod_cast h))
  have e2 : (B : F) ^ 2 = (a : F) * (c : F) := by
    exact_mod_cast congrArg (Int.cast (R := F)) hB
  have haF : (a : F) ≠ 0 := fun h => hBF (by
    have h1 : (B : F) ^ 2 = 0 := by rw [e2, h, zero_mul]
    exact pow_eq_zero_iff two_ne_zero |>.mp h1)
  have hcF : (c : F) ≠ 0 := fun h => hBF (by
    have h1 : (B : F) ^ 2 = 0 := by rw [e2, h, mul_zero]
    exact pow_eq_zero_iff two_ne_zero |>.mp h1)
  have hxne : x ≠ 0 := by
    rintro rfl
    norm_num [zero_pow (show n ≠ 0 by omega)] at hf
    exact hcF hf
  -- the recurring dead end: `a x + B = 0` is impossible
  have haux : (a : F) * x + (B : F) ≠ 0 := by
    intro e1
    have hquad : (a : F) ^ 2 * ((a : F) * x ^ 2 + 2 * (B : F) * x + (c : F)) = 0 := by
      linear_combination ((a : F) ^ 2 * x + (a : F) * (B : F)) * e1 - (a : F) * e2
    have hq0 : (a : F) * x ^ 2 + 2 * (B : F) * x + (c : F) = 0 :=
      (mul_eq_zero.mp hquad).resolve_left (pow_ne_zero 2 haF)
    have hxn : x ^ n = 0 := by linear_combination hf - hq0
    exact hxne (pow_eq_zero_iff (show n ≠ 0 by omega) |>.mp hxn)
  -- `p ∤ n`
  have hnF : (n : F) ≠ 0 := by
    intro h
    apply haux
    have h1 : 2 * ((a : F) * x + (B : F)) = 0 := by
      linear_combination hf' + (-(x ^ (n - 1))) * h
    exact (mul_eq_zero.mp h1).resolve_left h2F
  -- the resolvent identity
  have epow : x ^ (n - 1) * x = x ^ n := by
    rw [← pow_succ]
    congr 1
    omega
  have key0 : (a : F) * ((n : F) - 2) * x ^ 2 + 2 * (B : F) * ((n : F) - 1) * x
      + (n : F) * (c : F) = 0 := by
    linear_combination (n : F) * hf - x * hf' + (n : F) * epow
  -- `p ∤ n - 2`
  have hn2F : (n : F) - 2 ≠ 0 := by
    intro h
    have hn2 : (n : F) = 2 := by linear_combination h
    have eBx : (B : F) * x + (c : F) = 0 := by
      have h1 : 2 * ((B : F) * x + (c : F)) = 0 := by
        linear_combination key0 + (-(a : F) * x ^ 2 - 2 * (B : F) * x - (c : F)) * h
      exact (mul_eq_zero.mp h1).resolve_left h2F
    have eX : x ^ (n - 1) + (a : F) * x + (B : F) = 0 := by
      have h1 : 2 * (x ^ (n - 1) + (a : F) * x + (B : F)) = 0 := by
        linear_combination hf' + (-(x ^ (n - 1))) * hn2
      exact (mul_eq_zero.mp h1).resolve_left h2F
    have hBx : (B : F) ^ 2 * x ^ (n - 1) = 0 := by
      linear_combination (B : F) ^ 2 * eX + (-(a : F) * (B : F)) * eBx + (-(B : F)) * e2
    have hxn1 : x ^ (n - 1) = 0 :=
      (mul_eq_zero.mp hBx).resolve_left (pow_ne_zero 2 hBF)
    have hx0 : x = 0 := pow_eq_zero_iff (show n - 1 ≠ 0 by omega) |>.mp hxn1
    rw [hx0, mul_zero, zero_add] at eBx
    exact hcF eBx
  -- the factored resolvent: two candidate linear relations
  have hfact : ((a : F) * ((n : F) - 2) * x + (n : F) * (B : F)) *
      ((a : F) * ((n : F) - 2) * x + ((n : F) - 2) * (B : F)) = 0 := by
    have hid : ((a : F) * ((n : F) - 2) * x + (n : F) * (B : F)) *
        ((a : F) * ((n : F) - 2) * x + ((n : F) - 2) * (B : F))
        = (a : F) * ((n : F) - 2) *
          ((a : F) * ((n : F) - 2) * x ^ 2 + 2 * (B : F) * ((n : F) - 1) * x
            + (n : F) * (c : F))
          + (n : F) * ((n : F) - 2) * ((B : F) ^ 2 - (a : F) * (c : F)) := by
      ring
    rw [hid, key0, mul_zero, zero_add, e2, sub_self, mul_zero]
  rcases mul_eq_zero.mp hfact with h1 | h1
  · exact ⟨by linear_combination h1, hnF, hn2F, hxne⟩
  · exfalso
    apply haux
    have h2 : ((n : F) - 2) * ((a : F) * x + (B : F)) = 0 := by linear_combination h1
    exact (mul_eq_zero.mp h2).resolve_left hn2F

/-- At a common root (in the linear-relation form), `D` vanishes. -/
private theorem residue_D_eq_zero (hn : 3 ≤ n) (hB : B ^ 2 = a * c)
    (haF : (a : F) ≠ 0) {x : F}
    (hkey : (a : F) * ((n : F) - 2) * x = -((n : F) * (B : F)))
    (hf : x ^ n + (a : F) * x ^ 2 + 2 * (B : F) * x + (c : F) = 0) :
    ((D n B c : ℤ) : F) = 0 := by
  have hval := val_identity (F := F) hn hB hkey
  rw [hf, mul_zero] at hval
  have h0 : (a : F) ^ (n - 1) * ((D n B c : ℤ) : F) = 0 := by linear_combination hval
  exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ haF)

/-- Conversely: the linear relation together with `D̄ = 0` makes `x` a common root of `f̄`
and `f̄'`. -/
private theorem root_of_D (hn : 3 ≤ n) (hB : B ^ 2 = a * c)
    (haF : (a : F) ≠ 0) (hBF : (B : F) ≠ 0) (hnF : (n : F) ≠ 0) (hn2F : (n : F) - 2 ≠ 0)
    {x : F} (hkey : (a : F) * ((n : F) - 2) * x = -((n : F) * (B : F)))
    (hD : ((D n B c : ℤ) : F) = 0) :
    (x ^ n + (a : F) * x ^ 2 + 2 * (B : F) * x + (c : F) = 0) ∧
      ((n : F) * x ^ (n - 1) + 2 * (a : F) * x + 2 * (B : F) = 0) := by
  have e2 : (B : F) ^ 2 = (a : F) * (c : F) := by
    exact_mod_cast congrArg (Int.cast (R := F)) hB
  have hz0 : (a : F) * ((n : F) - 2) ≠ 0 := mul_ne_zero haF hn2F
  have hxne : x ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hkey
    have h0 : (n : F) * (B : F) = 0 := by linear_combination hkey
    exact (mul_eq_zero.mp h0).elim hnF hBF
  -- `f(x) = 0` from the identity
  have hval := val_identity (F := F) hn hB hkey
  rw [hD, mul_zero] at hval
  have hfac : (B : F) ^ (n - 2) * ((a : F) * ((n : F) - 2)) ^ n ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hBF) (pow_ne_zero _ hz0)
  have hf : x ^ n + (a : F) * x ^ 2 + 2 * (B : F) * x + (c : F) = 0 := by
    rcases mul_eq_zero.mp hval with h | h
    · exact absurd h hfac
    · exact h
  refine ⟨hf, ?_⟩
  -- `f'(x) = 0` from the factored resolvent
  have epow : x ^ (n - 1) * x = x ^ n := by
    rw [← pow_succ]
    congr 1
    omega
  have keyid : (n : F) * (x ^ n + (a : F) * x ^ 2 + 2 * (B : F) * x + (c : F))
      - x * ((n : F) * x ^ (n - 1) + 2 * (a : F) * x + 2 * (B : F))
      = (a : F) * ((n : F) - 2) * x ^ 2 + 2 * (B : F) * ((n : F) - 1) * x
        + (n : F) * (c : F) := by
    linear_combination (-(n : F)) * epow
  have hfact : ((a : F) * ((n : F) - 2) * x + (n : F) * (B : F)) *
      ((a : F) * ((n : F) - 2) * x + ((n : F) - 2) * (B : F))
      = (a : F) * ((n : F) - 2) *
        ((a : F) * ((n : F) - 2) * x ^ 2 + 2 * (B : F) * ((n : F) - 1) * x
          + (n : F) * (c : F)) := by
    linear_combination ((n : F) * ((n : F) - 2)) * e2
  have hzero : (a : F) * ((n : F) - 2) * x + (n : F) * (B : F) = 0 := by
    linear_combination hkey
  have hg2 : (a : F) * ((n : F) - 2) *
      ((a : F) * ((n : F) - 2) * x ^ 2 + 2 * (B : F) * ((n : F) - 1) * x
        + (n : F) * (c : F)) = 0 := by
    rw [← hfact, hzero, zero_mul]
  have hg2' : (a : F) * ((n : F) - 2) * x ^ 2 + 2 * (B : F) * ((n : F) - 1) * x
      + (n : F) * (c : F) = 0 :=
    (mul_eq_zero.mp hg2).resolve_left hz0
  have hxf' : x * ((n : F) * x ^ (n - 1) + 2 * (a : F) * x + 2 * (B : F)) = 0 := by
    linear_combination (n : F) * hf - keyid - hg2'
  exact (mul_eq_zero.mp hxf').resolve_left hxne

/-- **Tameness**: at the double root, `f''(x) · x = 2 B ≠ 0`. -/
private theorem residue_second_deriv (hn : 3 ≤ n) {x : F}
    (hcast : ((n - 1 : ℕ) : F) = (n : F) - 1)
    (hkey : (a : F) * ((n : F) - 2) * x = -((n : F) * (B : F)))
    (hf' : (n : F) * x ^ (n - 1) + 2 * (a : F) * x + 2 * (B : F) = 0) :
    ((n : F) * ((n - 1 : ℕ) : F) * x ^ (n - 2) + 2 * (a : F)) * x = 2 * (B : F) := by
  have epow : x ^ (n - 2) * x = x ^ (n - 1) := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hcast]
  linear_combination ((n : F) - 1) * (n : F) * epow + ((n : F) - 1) * hf' +
    (-2 : F) * hkey

end ResidueAnalysis

/-! ### Case (1) of Theorem 1.1: `p ∣ a` and `p ∣ c` -/

section Main

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {p : ℕ} [hp : Fact p.Prime]
  {n : ℕ} {a B c : ℤ}

/-- **Case (1) of Theorem 1.1 of [jakharkaurkumar2023]**: at a prime `p` dividing both `a`
and `c` (hence `b = 2B`, since `B ^ 2 = a c`), `p` divides the index `[𝓞 K : ℤ[θ]]` if and
only if `p ^ 2 ∣ c`.  Sufficiency is Eisenstein's criterion; necessity is the double-root
criterion at `0`. -/
theorem dvd_exponent_iff_of_dvd_of_dvd (hn : 3 ≤ n) (hB : B ^ 2 = a * c)
    (hpa : (p : ℤ) ∣ a) (hpc : (p : ℤ) ∣ c)
    (hθ : minpoly ℤ θ = X ^ n + (C a * X ^ 2 + C (2 * B) * X + C c))
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    p ∣ RingOfIntegers.exponent θ ↔ (p : ℤ) ^ 2 ∣ c := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  -- `p ∣ B` since `B ^ 2 = a c` and `p ∣ a`
  have hpB : (p : ℤ) ∣ B := hpp.dvd_of_dvd_pow (n := 2) (by rw [hB]; exact hpa.mul_right c)
  constructor
  · intro hdvd
    by_contra hc2
    -- `f` is Eisenstein at `p`
    refine (RingOfIntegers.not_dvd_exponent_of_minpoly_isEisensteinAt hgen ?_) hdvd
    rw [hθ]
    refine (monic_q hn).isEisensteinAt_of_mem_of_notMem
      (fun h => hpp.not_unit (isUnit_of_dvd_one
        (Ideal.mem_span_singleton.mp ((Ideal.eq_top_iff_one _).mp h))))
      (fun {i} hi => ?_) ?_
    · rw [natDegree_q hn] at hi
      rw [show (q n a B c).coeff i = (C a * X ^ 2 + C (2 * B) * X + C c).coeff i by
        rw [q, Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega), zero_add]]
      rw [Ideal.mem_span_singleton]
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_C, Polynomial.coeff_X]
      rcases show i = 0 ∨ i = 1 ∨ i = 2 ∨ 3 ≤ i by omega with rfl | rfl | rfl | h3
      · simpa using hpc
      · simpa using (hpB.mul_left 2)
      · simpa using hpa
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        simp
    · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      rw [show (q n a B c).coeff 0 = c by
        rw [q]
        simp [Polynomial.coeff_X_pow, if_neg (show ¬(0 = n) by omega)]]
      exact hc2
  · intro hc2
    refine RingOfIntegers.dvd_exponent_of_sq_dvd_eval (r := 0) ?_ ?_ ?_
    · rw [hθ]
      rw [show (X ^ n + (C a * X ^ 2 + C (2 * B) * X + C c) : ℤ[X]) = q n a B c from rfl,
        natDegree_q hn]
      omega
    · rw [hθ]
      rw [show (X ^ n + (C a * X ^ 2 + C (2 * B) * X + C c) : ℤ[X]) = q n a B c from rfl]
      rw [eval_q]
      simpa [zero_pow (show n ≠ 0 by omega)] using hc2
    · rw [hθ]
      rw [show (X ^ n + (C a * X ^ 2 + C (2 * B) * X + C c) : ℤ[X]) = q n a B c from rfl]
      rw [eval_derivative_q]
      simpa [zero_pow (show n - 1 ≠ 0 by omega)] using (hpB.mul_left 2)

/-- **Necessity in the totally wild subcase of case (2) of Theorem 1.1**: suppose `p ∣ a`,
`n = p ^ r * m` with `r ≥ 1`, and `p ^ 2` divides `a`, `2 B` and `c + (-c) ^ p ^ r`
(the last is `p ∣ c₁` in the notation of [jakharkaurkumar2023]).  Then `p` divides the
index, by the generalized obstruction lemma at the repeated factor `X ^ m + C c` of
`f mod p`. -/
theorem dvd_exponent_of_sq_dvd_of_sq_dvd {r m : ℕ} (hn : 3 ≤ p ^ r * m)
    (hr : 1 ≤ r) (hm : m ≠ 0)
    (ha2 : (p : ℤ) ^ 2 ∣ a) (hB2 : (p : ℤ) ^ 2 ∣ 2 * B)
    (hc1 : (p : ℤ) ^ 2 ∣ c + (-c) ^ p ^ r)
    (hθ : minpoly ℤ θ = X ^ (p ^ r * m) + (C a * X ^ 2 + C (2 * B) * X + C c)) :
    p ∣ RingOfIntegers.exponent θ := by
  -- the key identity for `X ^ n - (-c)`, i.e. `X ^ n + c`
  obtain ⟨T, hT⟩ := Pure.key_identity p r hm (-c)
  obtain ⟨a₂, ha₂⟩ := ha2
  obtain ⟨B₂, hB₂⟩ := hB2
  obtain ⟨c₂, hc₂⟩ := hc1
  have h2 : 2 ≤ p ^ r := by
    calc 2 ≤ p := hp.out.two_le
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ r := Nat.pow_le_pow_right hp.out.one_lt.le hr
  have hhm : (X ^ m + C c : ℤ[X]).Monic := by
    have h := monic_X_pow_sub_C (-c) hm
    rwa [map_neg, sub_neg_eq_add] at h
  have hsplit : (X ^ m + C c : ℤ[X]) ^ p ^ r
      = (X ^ m + C c) ^ 2 * (X ^ m + C c) ^ (p ^ r - 2) := by
    rw [← pow_add]
    congr 1
    omega
  refine RingOfIntegers.dvd_exponent_of_sq_factor
    (h := X ^ m + C c) (g := (X ^ m + C c) ^ (p ^ r - 2)) (k := T)
    (t := C a₂ * X ^ 2 + C B₂ * X + C c₂) ?_ ?_ ?_
  · exact hhm.mul (hhm.pow _)
  · rw [hθ]
    rw [show (X ^ (p ^ r * m) + (C a * X ^ 2 + C (2 * B) * X + C c) : ℤ[X])
        = q (p ^ r * m) a B c from rfl]
    rw [natDegree_q hn, hhm.natDegree_mul (hhm.pow _), natDegree_pow]
    have hdeg_h : (X ^ m + C c : ℤ[X]).natDegree = m := by
      have h := natDegree_X_pow_sub_C (n := m) (r := -c) (R := ℤ)
      rwa [map_neg, sub_neg_eq_add] at h
    rw [hdeg_h]
    obtain ⟨s, hs⟩ : ∃ s, p ^ r = s + 2 := ⟨p ^ r - 2, by omega⟩
    rw [hs]
    have hm1 : 0 < m := Nat.pos_of_ne_zero hm
    simp only [Nat.add_sub_cancel]
    nlinarith [hm1]
  · rw [hθ]
    -- the key identity for `X ^ n + C c`, obtained from the pure one at `-c`
    have hkey : (X ^ (p ^ r * m) + C c : ℤ[X])
        = (X ^ m + C c) ^ p ^ r + C (p : ℤ) * ((X ^ m + C c) * T)
          + C (c + (-c) ^ p ^ r) := by
      have h := hT
      rw [show (X ^ (p ^ r * m) - C (-c) : ℤ[X]) = X ^ (p ^ r * m) + C c by
          rw [map_neg, sub_neg_eq_add],
        show (X ^ m - C (-c) : ℤ[X]) = X ^ m + C c by rw [map_neg, sub_neg_eq_add],
        show ((-c : ℤ) ^ p ^ r - -c) = c + (-c) ^ p ^ r by ring] at h
      exact h
    have hca : C a = C ((p : ℤ)) ^ 2 * C a₂ := by
      rw [← map_pow, ← map_mul, ← ha₂]
    have hcB : C (2 * B) = C ((p : ℤ)) ^ 2 * C B₂ := by
      rw [← map_pow, ← map_mul, ← hB₂]
    have hcc : C (c + (-c) ^ p ^ r) = C ((p : ℤ)) ^ 2 * C c₂ := by
      rw [← map_pow, ← map_mul, ← hc₂]
    rw [← hsplit]
    linear_combination hkey + X ^ 2 * hca + X * hcB + hcc

/-- **Corrected case (3) of Theorem 1.1**: if `p ∣ c` and `p ∤ a` then `p` *always* divides
the index `[𝓞 K : ℤ[θ]]`.  Indeed `B ^ 2 = a c` forces `p ∣ B`, hence
`p ^ 2 ∣ B ^ 2 = a c` and, as `p ∤ a`, `p ^ 2 ∣ c`; the double-root criterion at `0`
applies since `f(0) = c` and `f'(0) = 2 B`.

Note that this **contradicts case (3) of Theorem 1.1 as printed** in
[jakharkaurkumar2023], which asserts a nontrivial criterion for `p ∤ [𝓞 K : ℤ[θ]]` in
this situation.  Concretely, for `f = X ^ 5 + X ^ 2 + 6 X + 9` at `p = 3` the printed
condition of case (3) is satisfied (`a₁ = 0`, `b₁ = 2`, so `p ∣ a₁` and `p ∤ b₁`), but
`f ≡ x ^ 2 (x + 1) ^ 3 mod 3` with Dedekind remainder
`M̄ = x (x ^ 3 + x ^ 2 + 1)`, divisible by the repeated factor `x`, so `3` divides the
index; the proof of case (3) in [jakharkaurkumar2023] appears to drop the repeated
factor `x` when applying Dedekind's criterion. -/
theorem dvd_exponent_of_dvd_of_not_dvd (hn : 3 ≤ n) (hB : B ^ 2 = a * c)
    (hpa : ¬(p : ℤ) ∣ a) (hpc : (p : ℤ) ∣ c)
    (hθ : minpoly ℤ θ = X ^ n + (C a * X ^ 2 + C (2 * B) * X + C c)) :
    p ∣ RingOfIntegers.exponent θ := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hpB : (p : ℤ) ∣ B := hpp.dvd_of_dvd_pow (n := 2) (by rw [hB]; exact hpc.mul_left a)
  have hpc2 : (p : ℤ) ^ 2 ∣ c := by
    have h1 : (p : ℤ) ^ 2 ∣ a * c := by
      rw [← hB]
      exact pow_dvd_pow_of_dvd hpB 2
    exact ((hpp.coprime_iff_not_dvd.mpr hpa).pow_left).dvd_of_dvd_mul_left h1
  refine RingOfIntegers.dvd_exponent_of_sq_dvd_eval (r := 0) ?_ ?_ ?_
  · rw [hθ, show (X ^ n + (C a * X ^ 2 + C (2 * B) * X + C c) : ℤ[X])
        = q n a B c from rfl, natDegree_q hn]
    omega
  · rw [hθ, show (X ^ n + (C a * X ^ 2 + C (2 * B) * X + C c) : ℤ[X])
        = q n a B c from rfl, eval_q]
    simpa [zero_pow (show n ≠ 0 by omega)] using hpc2
  · rw [hθ, show (X ^ n + (C a * X ^ 2 + C (2 * B) * X + C c) : ℤ[X])
        = q n a B c from rfl, eval_derivative_q]
    simpa [zero_pow (show n - 1 ≠ 0 by omega)] using hpB.mul_left 2

/-- **Necessity in case (2), rational-common-root subcase**: suppose `p ∣ a`, `n = p ^ r m`
with `r ≥ 1`, and there is an integer `d` with `p ∣ d ^ m + c` (i.e. `d̄` is a root of the
repeated factor mod `p`) and `p ^ 2 ∣ (-c) ^ p ^ r + c + a d ^ 2 + 2 B d` (equivalently
`p ^ 2 ∣ f(d)`).  Then `p` divides the index, by the double-root criterion at `d`.
Together with `dvd_exponent_of_sq_dvd_of_sq_dvd` this covers the necessity half of case
(2) of Theorem 1.1 of [jakharkaurkumar2023]. -/
theorem dvd_exponent_of_dvd_of_dvd_eval {r m : ℕ} (hn : 3 ≤ p ^ r * m) (hr : 1 ≤ r)
    (hm : m ≠ 0) (hB : B ^ 2 = a * c) (hpa : (p : ℤ) ∣ a) {d : ℤ}
    (hd : (p : ℤ) ∣ d ^ m + c)
    (hlin : (p : ℤ) ^ 2 ∣ (-c) ^ p ^ r + c + a * d ^ 2 + 2 * B * d)
    (hθ : minpoly ℤ θ = X ^ (p ^ r * m) + (C a * X ^ 2 + C (2 * B) * X + C c)) :
    p ∣ RingOfIntegers.exponent θ := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hpB : (p : ℤ) ∣ B := hpp.dvd_of_dvd_pow (n := 2) (by rw [hB]; exact hpa.mul_right c)
  have h2 : 2 ≤ p ^ r := by
    calc 2 ≤ p := hp.out.two_le
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ r := Nat.pow_le_pow_right hp.out.one_lt.le hr
  -- `p ^ 2 ∣ f(d)` via the key identity evaluated at `d`
  obtain ⟨T, hT⟩ := Pure.key_identity p r hm (-c)
  have heval := congrArg (Polynomial.eval d) hT
  simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C] at heval
  obtain ⟨k, hk⟩ := hd
  have hsq : (p : ℤ) ^ 2 ∣ (d ^ m - -c) ^ p ^ r + (p : ℤ) * ((d ^ m - -c) * T.eval d) := by
    have hdm : d ^ m - -c = (p : ℤ) * k := by linear_combination hk
    refine dvd_add ?_ ?_
    · rw [hdm, mul_pow]
      exact ((pow_dvd_pow (p : ℤ) h2).mul_right _)
    · rw [hdm]
      exact ⟨k * T.eval d, by ring⟩
  have hfd : (p : ℤ) ^ 2 ∣ d ^ (p ^ r * m) + a * d ^ 2 + 2 * B * d + c := by
    have hre : d ^ (p ^ r * m) + a * d ^ 2 + 2 * B * d + c
        = ((d ^ m - -c) ^ p ^ r + (p : ℤ) * ((d ^ m - -c) * T.eval d))
          + ((-c) ^ p ^ r + c + a * d ^ 2 + 2 * B * d) := by
      linear_combination heval
    rw [hre]
    exact dvd_add hsq hlin
  refine RingOfIntegers.dvd_exponent_of_sq_dvd_eval (r := d) ?_ ?_ ?_
  · rw [hθ, show (X ^ (p ^ r * m) + (C a * X ^ 2 + C (2 * B) * X + C c) : ℤ[X])
        = q (p ^ r * m) a B c from rfl, natDegree_q hn]
    omega
  · rw [hθ, show (X ^ (p ^ r * m) + (C a * X ^ 2 + C (2 * B) * X + C c) : ℤ[X])
        = q (p ^ r * m) a B c from rfl, eval_q]
    exact hfd
  · rw [hθ, show (X ^ (p ^ r * m) + (C a * X ^ 2 + C (2 * B) * X + C c) : ℤ[X])
        = q (p ^ r * m) a B c from rfl, eval_derivative_q]
    have hpn : (p : ℤ) ∣ ((p ^ r * m : ℕ) : ℤ) := by
      push_cast
      exact (dvd_pow_self (p : ℤ) (by omega : r ≠ 0)).mul_right _
    exact dvd_add (dvd_add (hpn.mul_right _) ((hpa.mul_left 2).mul_right d))
      (hpB.mul_left 2)

/-- **Necessity in case (4) of Theorem 1.1** (`p = 2`): if `n = 2 m` and
`a ≡ c ≡ 3 mod 4`, then `2` divides the index.  This rests on the exact identity
`f = h ^ 2 - 2 (a X + c) h + ((a + a²) X ^ 2 + (2 a c + 2 B) X + (c + c²))` with
`h = X ^ m + a X + c`, whose tail is divisible by `4` precisely when
`a ≡ c ≡ 3 mod 4` (note `B` is odd since `B ^ 2 = a c` is odd), so the generalized
obstruction lemma applies at the repeated factor `h`. -/
theorem two_dvd_exponent_of_mod_four {m : ℕ} (hm : 2 ≤ m) (hB : B ^ 2 = a * c)
    (ha4 : (4 : ℤ) ∣ a + 1) (hc4 : (4 : ℤ) ∣ c + 1)
    (hθ : minpoly ℤ θ = X ^ (2 * m) + (C a * X ^ 2 + C (2 * B) * X + C c)) :
    2 ∣ RingOfIntegers.exponent θ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a₄, ha₄⟩ := ha4
  obtain ⟨c₄, hc₄⟩ := hc4
  -- `B` is odd
  have hBodd : ∃ B₅ : ℤ, B = 2 * B₅ + 1 := by
    rcases Int.even_or_odd B with hev | hod
    · exfalso
      have h2 : Even (a * c) := by
        obtain ⟨t, ht⟩ := hev
        rw [← hB, ht]
        exact ⟨2 * t * t, by ring⟩
      rcases Int.even_mul.mp h2 with h3 | h3 <;> obtain ⟨u, hu⟩ := h3 <;> omega
    · obtain ⟨B₅, hB₅⟩ := hod
      exact ⟨B₅, by omega⟩
  obtain ⟨B₅, hB₅⟩ := hBodd
  have haeq : a = 4 * a₄ - 1 := by omega
  have hceq : c = 4 * c₄ - 1 := by omega
  subst haeq hceq hB₅
  refine RingOfIntegers.dvd_exponent_of_sq_factor (p := 2)
    (h := X ^ m + (C (4 * a₄ - 1) * X + C (4 * c₄ - 1))) (g := 1)
    (k := -(C (4 * a₄ - 1) * X + C (4 * c₄ - 1)))
    (t := C ((4 * a₄ - 1) * a₄) * X ^ 2
      + C (8 * a₄ * c₄ - 2 * a₄ - 2 * c₄ + B₅ + 1) * X + C ((4 * c₄ - 1) * c₄))
    ?_ ?_ ?_
  · rw [mul_one]
    exact Polynomial.monic_X_pow_add (lt_of_le_of_lt Polynomial.degree_linear_le
      (by exact_mod_cast (by omega : 1 < m)))
  · rw [mul_one, hθ, show (X ^ (2 * m) + (C (4 * a₄ - 1) * X ^ 2
        + C (2 * (2 * B₅ + 1)) * X + C (4 * c₄ - 1)) : ℤ[X])
        = q (2 * m) (4 * a₄ - 1) (2 * B₅ + 1) (4 * c₄ - 1) from rfl,
      natDegree_q (by omega)]
    have hdegh : (X ^ m + (C (4 * a₄ - 1) * X + C (4 * c₄ - 1)) : ℤ[X]).natDegree = m :=
      Polynomial.natDegree_eq_of_degree_eq_some (by
        rw [Polynomial.degree_add_eq_left_of_degree_lt (by
          rw [Polynomial.degree_X_pow]
          exact lt_of_le_of_lt Polynomial.degree_linear_le
            (by exact_mod_cast (by omega : 1 < m))), Polynomial.degree_X_pow])
    rw [hdegh]
    omega
  · rw [hθ]
    have hxx : (X : ℤ[X]) ^ (2 * m) = (X ^ m) ^ 2 := by
      rw [← pow_mul, mul_comm m 2]
    rw [hxx]
    push_cast
    simp only [map_sub, map_add, map_mul, map_ofNat, map_one]
    ring

end Main

/-! ### Case (5) of Theorem 1.1: `p ∤ b` -/

section Case5

attribute [local instance] Ideal.Quotient.field

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {p : ℕ} [hp : Fact p.Prime]
  {n : ℕ} {a B c : ℤ}

omit [NumberField K] in
/-- The root relation in `𝓞 K`. -/
private theorem aeval_root_q (hθ : minpoly ℤ θ = X ^ n + (C a * X ^ 2 + C (2 * B) * X + C c)) :
    θ ^ n + (a : 𝓞 K) * θ ^ 2 + 2 * (B : 𝓞 K) * θ + (c : 𝓞 K) = 0 := by
  have h := minpoly.aeval ℤ θ
  rw [hθ] at h
  simp only [map_add, map_mul, map_pow, aeval_X, eq_intCast, map_intCast] at h
  push_cast at h
  linear_combination h

omit [NumberField K] in
private theorem aeval_derivative_eq_q
    (hθ : minpoly ℤ θ = X ^ n + (C a * X ^ 2 + C (2 * B) * X + C c)) :
    aeval θ (derivative (minpoly ℤ θ))
      = (n : 𝓞 K) * θ ^ (n - 1) + 2 * (a : 𝓞 K) * θ + 2 * (B : 𝓞 K) := by
  rw [hθ, show (X ^ n + (C a * X ^ 2 + C (2 * B) * X + C c) : ℤ[X]) = q n a B c from rfl,
    derivative_q]
  simp only [map_add, map_mul, map_pow, aeval_X, eq_intCast, map_intCast, map_natCast]
  push_cast
  ring

omit [NumberField K] in
/-- Transfer of integer divisibility to the residue field. -/
private theorem quotient_intCast_iff {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪.IsMaximal)
    (hp𝔪 : (p : 𝓞 K) ∈ 𝔪) (t : ℤ) :
    ((t : 𝓞 K ⧸ 𝔪) = 0) ↔ (p : ℤ) ∣ t := by
  rw [show ((t : 𝓞 K ⧸ 𝔪)) = Ideal.Quotient.mk 𝔪 ((t : 𝓞 K)) from
    (map_intCast (Ideal.Quotient.mk 𝔪) t).symm, Ideal.Quotient.eq_zero_iff_mem]
  exact RingOfIntegers.intCast_mem_iff_dvd h𝔪 hp𝔪 t

/-- In a residue field above `p` containing the conductor, `θ` is a common root of `f̄` and
`f̄'`. -/
private theorem quotient_facts
    (hθ : minpoly ℤ θ = X ^ n + (C a * X ^ 2 + C (2 * B) * X + C c))
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    {𝔪 : Ideal (𝓞 K)} (hcond : conductor ℤ θ ≤ 𝔪) :
    ((Ideal.Quotient.mk 𝔪 θ) ^ n + (a : 𝓞 K ⧸ 𝔪) * (Ideal.Quotient.mk 𝔪 θ) ^ 2
        + 2 * (B : 𝓞 K ⧸ 𝔪) * (Ideal.Quotient.mk 𝔪 θ) + (c : 𝓞 K ⧸ 𝔪) = 0) ∧
      ((n : 𝓞 K ⧸ 𝔪) * (Ideal.Quotient.mk 𝔪 θ) ^ (n - 1)
        + 2 * (a : 𝓞 K ⧸ 𝔪) * (Ideal.Quotient.mk 𝔪 θ) + 2 * (B : 𝓞 K ⧸ 𝔪) = 0) := by
  constructor
  · have h := congrArg (Ideal.Quotient.mk 𝔪) (aeval_root_q hθ)
    simpa [map_add, map_mul, map_pow, map_intCast, map_ofNat] using h
  · have h1 : aeval θ (derivative (minpoly ℤ θ)) ∈ 𝔪 :=
      hcond (RingOfIntegers.aeval_derivative_minpoly_mem_conductor hgen)
    have h2 := (Ideal.Quotient.eq_zero_iff_mem (I := 𝔪)).mpr h1
    rw [aeval_derivative_eq_q hθ] at h2
    simpa [map_add, map_mul, map_pow, map_intCast, map_natCast, map_ofNat] using h2

/-- **Case (5) of Theorem 1.1 of [jakharkaurkumar2023]**: at a prime `p` not dividing
`b = 2B`, `p` divides the index `[𝓞 K : ℤ[θ]]` if and only if `p ^ 2 ∣ D`. -/
theorem dvd_exponent_iff_of_not_dvd (hn : 3 ≤ n) (hB : B ^ 2 = a * c)
    (hp2B : ¬(p : ℤ) ∣ 2 * B)
    (hθ : minpoly ℤ θ = X ^ n + (C a * X ^ 2 + C (2 * B) * X + C c))
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    p ∣ RingOfIntegers.exponent θ ↔ (p : ℤ) ^ 2 ∣ D n B c := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  obtain ⟨hpa, hpc⟩ := not_dvd_a_c hp.out hB hp2B
  have hpB : ¬(p : ℤ) ∣ B := fun h => hp2B (h.mul_left 2)
  have hpF0 : ∀ t : ℤ, ((t : ZMod p) = 0) ↔ (p : ℤ) ∣ t := fun t =>
    ZMod.intCast_zmod_eq_zero_iff_dvd t p
  have hcastZ : ((n - 1 : ℕ) : ZMod p) = (n : ZMod p) - 1 := by
    exact_mod_cast congrArg (Int.cast (R := ZMod p))
      (show ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 by omega)
  constructor
  · -- contrapositive: if `p ^ 2 ∤ D` then `p ∤ exponent`
    intro h
    by_contra hD2
    refine absurd h ?_
    by_cases hpD : (p : ℤ) ∣ D n B c
    · -- tame double root at the lift `d`
      obtain ⟨hpn, hpn2⟩ := not_dvd_of_dvd_D hp.out hn hB hp2B hpD
      obtain ⟨d, hd⟩ := exists_lift hp.out hpa hpn2
      have hpd : (p : ℤ) ∣ a * ((n : ℤ) - 2) * d + n * B :=
        (dvd_pow_self (p : ℤ) two_ne_zero).trans hd
      have hcop2 : IsCoprime ((p : ℤ) ^ 2) a := (hpp.coprime_iff_not_dvd.mpr hpa).pow_left
      have hcopB2 : IsCoprime ((p : ℤ) ^ 2) B := (hpp.coprime_iff_not_dvd.mpr hpB).pow_left
      have hcopn2 : IsCoprime ((p : ℤ) ^ 2) ((n : ℤ) - 2) :=
        (hpp.coprime_iff_not_dvd.mpr hpn2).pow_left
      -- facts about `d` in `ZMod p`
      have haZ : ((a : ZMod p)) ≠ 0 := fun h0 => hpa ((hpF0 a).mp h0)
      have hBZ : ((B : ZMod p)) ≠ 0 := fun h0 => hpB ((hpF0 B).mp h0)
      have hnZ : ((n : ZMod p)) ≠ 0 := fun h0 => hpn (by
        rw [← hpF0]
        exact_mod_cast h0)
      have hn2Z : ((n : ZMod p)) - 2 ≠ 0 := fun h0 => hpn2 (by
        rw [← hpF0]
        push_cast
        exact h0)
      have hkeyd : (a : ZMod p) * ((n : ZMod p) - 2) * (d : ZMod p)
          = -((n : ZMod p) * (B : ZMod p)) := by
        have h0 : ((a * ((n : ℤ) - 2) * d + n * B : ℤ) : ZMod p) = 0 := (hpF0 _).mpr hpd
        push_cast at h0
        linear_combination h0
      obtain ⟨hfd, hf'd⟩ := root_of_D hn hB haZ hBZ hnZ hn2Z hkeyd ((hpF0 _).mpr hpD)
      -- apply the tame sufficiency criterion at `d`
      refine RingOfIntegers.not_dvd_exponent_of_sq_not_dvd_eval (r := d) hgen ?_ ?_ ?_
      · rw [hθ, show (X ^ n + (C a * X ^ 2 + C (2 * B) * X + C c) : ℤ[X])
            = q n a B c from rfl, eval_q]
        rw [dvd_eval_iff_dvd_D hn hB hd hcop2 hcopB2 hcopn2]
        exact hD2
      · rw [hθ, show (X ^ n + (C a * X ^ 2 + C (2 * B) * X + C c) : ℤ[X])
            = q n a B c from rfl, eval_derivative_derivative_q]
        intro hdvd
        have h0 := (hpF0 _).mpr hdvd
        push_cast at h0
        have hsd := residue_second_deriv (a := a) (B := B) hn hcastZ hkeyd hf'd
        rw [h0, zero_mul] at hsd
        have h2B : ((2 * B : ℤ) : ZMod p) = 0 := by
          push_cast
          linear_combination -hsd
        exact hp2B ((hpF0 _).mp h2B)
      · -- uniqueness of the double root in every residue field
        intro 𝔪 h𝔪 hcond hp𝔪
        obtain ⟨hfθ, hf'θ⟩ := quotient_facts hθ hgen hcond
        have hpF𝔪 := quotient_intCast_iff h𝔪 hp𝔪
        obtain ⟨hkeyθ, -, hn2𝔪, -⟩ :=
          residue_analysis hpF𝔪 hn hB hp2B hfθ hf'θ
        have ha𝔪 : ((a : 𝓞 K ⧸ 𝔪)) ≠ 0 := fun h0 => hpa ((hpF𝔪 a).mp h0)
        have hkeyd' : (a : 𝓞 K ⧸ 𝔪) * ((n : 𝓞 K ⧸ 𝔪) - 2) * ((d : ℤ) : 𝓞 K ⧸ 𝔪)
            = -((n : 𝓞 K ⧸ 𝔪) * (B : 𝓞 K ⧸ 𝔪)) := by
          have h0 : ((a * ((n : ℤ) - 2) * d + n * B : ℤ) : 𝓞 K ⧸ 𝔪) = 0 := (hpF𝔪 _).mpr hpd
          push_cast at h0
          linear_combination h0
        have heq : Ideal.Quotient.mk 𝔪 θ = ((d : ℤ) : 𝓞 K ⧸ 𝔪) := by
          have h1 : (a : 𝓞 K ⧸ 𝔪) * ((n : 𝓞 K ⧸ 𝔪) - 2) *
              (Ideal.Quotient.mk 𝔪 θ - ((d : ℤ) : 𝓞 K ⧸ 𝔪)) = 0 := by
            linear_combination hkeyθ - hkeyd'
          have h2 := (mul_eq_zero.mp h1).resolve_left (mul_ne_zero ha𝔪 hn2𝔪)
          exact sub_eq_zero.mp h2
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_intCast, heq, sub_self]
    · -- no repeated root modulo `p`
      rw [RingOfIntegers.not_dvd_exponent_iff_conductor_sup_span_eq_top]
      by_contra hsup
      obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hsup
      have hcond : conductor ℤ θ ≤ 𝔪 := le_trans le_sup_left hle
      have hp𝔪 : (p : 𝓞 K) ∈ 𝔪 := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
      obtain ⟨hfθ, hf'θ⟩ := quotient_facts hθ hgen hcond
      have hpF𝔪 := quotient_intCast_iff h𝔪 hp𝔪
      obtain ⟨hkeyθ, -, -, -⟩ := residue_analysis hpF𝔪 hn hB hp2B hfθ hf'θ
      have ha𝔪 : ((a : 𝓞 K ⧸ 𝔪)) ≠ 0 := fun h0 => hpa ((hpF𝔪 a).mp h0)
      exact hpD ((hpF𝔪 _).mp (residue_D_eq_zero hn hB ha𝔪 hkeyθ hfθ))
  · -- necessity: `p ^ 2 ∣ D` forces `p ∣ exponent`
    intro hD2
    have hpD : (p : ℤ) ∣ D n B c := (dvd_pow_self _ two_ne_zero).trans hD2
    obtain ⟨hpn, hpn2⟩ := not_dvd_of_dvd_D hp.out hn hB hp2B hpD
    obtain ⟨d, hd⟩ := exists_lift hp.out hpa hpn2
    have hpd : (p : ℤ) ∣ a * ((n : ℤ) - 2) * d + n * B :=
      (dvd_pow_self (p : ℤ) two_ne_zero).trans hd
    have hcop2 : IsCoprime ((p : ℤ) ^ 2) a := (hpp.coprime_iff_not_dvd.mpr hpa).pow_left
    have hcopB2 : IsCoprime ((p : ℤ) ^ 2) B := (hpp.coprime_iff_not_dvd.mpr hpB).pow_left
    have hcopn2 : IsCoprime ((p : ℤ) ^ 2) ((n : ℤ) - 2) :=
      (hpp.coprime_iff_not_dvd.mpr hpn2).pow_left
    have haZ : ((a : ZMod p)) ≠ 0 := fun h0 => hpa ((hpF0 a).mp h0)
    have hBZ : ((B : ZMod p)) ≠ 0 := fun h0 => hpB ((hpF0 B).mp h0)
    have hnZ : ((n : ZMod p)) ≠ 0 := fun h0 => hpn (by
      rw [← hpF0]
      exact_mod_cast h0)
    have hn2Z : ((n : ZMod p)) - 2 ≠ 0 := fun h0 => hpn2 (by
      rw [← hpF0]
      push_cast
      exact h0)
    have hkeyd : (a : ZMod p) * ((n : ZMod p) - 2) * (d : ZMod p)
        = -((n : ZMod p) * (B : ZMod p)) := by
      have h0 : ((a * ((n : ℤ) - 2) * d + n * B : ℤ) : ZMod p) = 0 := (hpF0 _).mpr hpd
      push_cast at h0
      linear_combination h0
    obtain ⟨-, hf'd⟩ := root_of_D hn hB haZ hBZ hnZ hn2Z hkeyd ((hpF0 _).mpr hpD)
    refine RingOfIntegers.dvd_exponent_of_sq_dvd_eval (r := d) ?_ ?_ ?_
    · rw [hθ, show (X ^ n + (C a * X ^ 2 + C (2 * B) * X + C c) : ℤ[X])
          = q n a B c from rfl, natDegree_q hn]
      omega
    · rw [hθ, show (X ^ n + (C a * X ^ 2 + C (2 * B) * X + C c) : ℤ[X])
          = q n a B c from rfl, eval_q,
        dvd_eval_iff_dvd_D hn hB hd hcop2 hcopB2 hcopn2]
      exact hD2
    · rw [hθ, show (X ^ n + (C a * X ^ 2 + C (2 * B) * X + C c) : ℤ[X])
          = q n a B c from rfl, eval_derivative_q]
      rw [← hpF0]
      push_cast
      exact hf'd

end Case5

/-! ### Sufficiency in the wild cases (2) and (4) of Theorem 1.1

These use the sufficiency half of Dedekind's index criterion
(`RingOfIntegers.not_dvd_exponent_of_bezout`), which cannot be replaced by
single-prime valuation arguments at wild multiplicities. -/

section Sufficiency

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {p : ℕ} [hp : Fact p.Prime]
variable {n : ℕ} {a B c : ℤ}

/-- A polynomial over a field is coprime to `X - C d` as soon as it does not vanish
at `d`. -/
private theorem isCoprime_X_sub_C_of_eval_ne_zero {F : Type*} [Field F] {f : F[X]} {d : F}
    (h : f.eval d ≠ 0) : IsCoprime f (X - C d) := by
  refine ⟨C (f.eval d)⁻¹, -(C (f.eval d)⁻¹ * (f /ₘ (X - C d))), ?_⟩
  have hmd := modByMonic_add_div f (X - C d)
  rw [modByMonic_X_sub_C_eq_C_eval] at hmd
  have hinv : C (f.eval d)⁻¹ * C (f.eval d) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ h, map_one]
  linear_combination hinv - C (f.eval d)⁻¹ * hmd

private theorem zmod_intCast_eq {x y : ℤ} {p : ℕ} [NeZero p] (h : (p : ℤ) ∣ x - y) :
    ((x : ZMod p)) = ((y : ZMod p)) := by
  rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact h

/-- In case (4) of Theorem 1.1 (`p = 2`, `a` and `c` odd), if the degree `n` is odd
then `2` never divides the index: `f` is separable mod `2`. -/
theorem not_two_dvd_exponent_of_odd_degree (hn : 3 ≤ n) (hodd : ¬2 ∣ n)
    (ha : ¬(2 : ℤ) ∣ a) (hc : ¬(2 : ℤ) ∣ c)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hθ : minpoly ℤ θ = X ^ n + (C a * X ^ 2 + C (2 * B) * X + C c)) :
    ¬2 ∣ RingOfIntegers.exponent θ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2N : (((2 : ℕ) : ZMod 2)) = 0 := ZMod.natCast_self 2
  have e1 : (((a : ℤ) : ZMod 2)) = ((1 : ℤ) : ZMod 2) := zmod_intCast_eq (by omega)
  have e2 : (((2 * B : ℤ) : ZMod 2)) = ((0 : ℤ) : ZMod 2) := zmod_intCast_eq ⟨B, by ring⟩
  have e3 : (((c : ℤ) : ZMod 2)) = ((1 : ℤ) : ZMod 2) := zmod_intCast_eq (by omega)
  rw [Int.cast_one] at e1 e3
  rw [Int.cast_zero] at e2
  refine RingOfIntegers.not_dvd_exponent_of_bezout (p := 2) hgen
    (g := X ^ n + (C a * X ^ 2 + C (2 * B) * X + C c))
    (h := 1) (M := 0) ?_ ?_ ?_ ?_
  · rw [hθ]
    ring
  · have hmap : (X ^ n + (C a * X ^ 2 + C (2 * B) * X
        + C c) : ℤ[X]).map (Int.castRingHom (ZMod 2))
        = X ^ n + X ^ 2 + 1 := by
      simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul, map_C, map_X,
        Int.coe_castRingHom, e1, e2, e3, map_one, map_zero]
      ring
    rw [hmap]
    apply Polynomial.Separable.squarefree
    have hn1 : ((n : ZMod 2)) = 1 := by
      rw [← Int.cast_natCast (R := ZMod 2), ← Int.cast_one (R := ZMod 2)]
      exact zmod_intCast_eq (by omega)
    have hder : derivative (X ^ n + X ^ 2 + 1 : (ZMod 2)[X]) = X ^ (n - 1) := by
      rw [derivative_add, derivative_add, derivative_one, add_zero, derivative_X_pow,
        derivative_X_pow, hn1, map_one, one_mul, h2N, map_zero, zero_mul, add_zero]
    rw [Polynomial.Separable, hder]
    refine IsCoprime.pow_right ?_
    refine ⟨1, -(X ^ (n - 1) + X), ?_⟩
    have hpow : (X : (ZMod 2)[X]) ^ (n - 1) * X = X ^ n := by
      rw [← pow_succ]
      congr 1
      omega
    linear_combination -hpow
  · intro q₀ hq₀ hdvd
    rw [Polynomial.map_one] at hdvd
    exact absurd (isUnit_of_dvd_one hdvd) hq₀.not_isUnit
  · exact ⟨0, 1, 0, by simp⟩

/-- **Sufficiency in case (4) of Theorem 1.1** (`p = 2`, `n = 2 m`, `a` and `c` odd):
if `a` and `c` are not both `≡ 3 mod 4`, then `2` does not divide the index.
Together with `two_dvd_exponent_of_mod_four` this determines case (4) completely. -/
theorem not_two_dvd_exponent_of_not_mod_four {m : ℕ} (hm : 2 ≤ m) (hB : B ^ 2 = a * c)
    (ha : ¬(2 : ℤ) ∣ a) (hc : ¬(2 : ℤ) ∣ c)
    (h4 : ¬((4 : ℤ) ∣ a + 1 ∧ (4 : ℤ) ∣ c + 1))
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hθ : minpoly ℤ θ = X ^ (2 * m) + (C a * X ^ 2 + C (2 * B) * X + C c)) :
    ¬2 ∣ RingOfIntegers.exponent θ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2P : ((2 : (ZMod 2)[X])) = 0 := by exact_mod_cast CharP.cast_eq_zero ((ZMod 2)[X]) 2
  obtain ⟨a₃, ha₃⟩ : ∃ a₃, a = 2 * a₃ + 1 := ⟨(a - 1) / 2, by omega⟩
  obtain ⟨c₃, hc₃⟩ : ∃ c₃, c = 2 * c₃ + 1 := ⟨(c - 1) / 2, by omega⟩
  -- `B` is odd since `B ^ 2 = a c` is odd
  have hBodd : ∃ B₁ : ℤ, B = 2 * B₁ + 1 := by
    rcases Int.even_or_odd B with hev | hod
    · exfalso
      have h2 : Even (a * c) := by
        obtain ⟨t, ht⟩ := hev
        rw [← hB, ht]
        exact ⟨2 * t * t, by ring⟩
      rcases Int.even_mul.mp h2 with h3 | h3 <;> obtain ⟨u, hu⟩ := h3 <;> omega
    · obtain ⟨B₁, hB₁⟩ := hod
      exact ⟨B₁, by omega⟩
  obtain ⟨B₁, hB₁⟩ := hBodd
  subst ha₃ hc₃ hB₁
  -- cast facts for the reductions mod 2
  have e1 : (((2 * a₃ + 1 : ℤ) : ZMod 2)) = ((1 : ℤ) : ZMod 2) :=
    zmod_intCast_eq ⟨a₃, by ring⟩
  have e2 : (((2 * c₃ + 1 : ℤ) : ZMod 2)) = ((1 : ℤ) : ZMod 2) :=
    zmod_intCast_eq ⟨c₃, by ring⟩
  have e3 : (((a₃ * (2 * a₃ + 1) : ℤ) : ZMod 2)) = ((a₃ : ZMod 2)) :=
    zmod_intCast_eq ⟨a₃ ^ 2, by ring⟩
  have e4 : ((((2 * B₁ + 1) - (2 * a₃ + 1) * (2 * c₃ + 1) : ℤ) : ZMod 2)) = ((0 : ℤ) : ZMod 2) :=
    zmod_intCast_eq ⟨B₁ - 2 * a₃ * c₃ - a₃ - c₃, by ring⟩
  have e5 : (((c₃ * (2 * c₃ + 1) : ℤ) : ZMod 2)) = ((c₃ : ZMod 2)) :=
    zmod_intCast_eq ⟨c₃ ^ 2, by ring⟩
  rw [Int.cast_one] at e1 e2
  rw [Int.cast_zero] at e4
  have hgmap : (X ^ m + C (2 * a₃ + 1) * X + C (2 * c₃ + 1) : ℤ[X]).map
      (Int.castRingHom (ZMod 2)) = X ^ m + X + 1 := by
    simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul, map_C, map_X,
      Int.coe_castRingHom, e1, e2, map_one]
    ring
  refine RingOfIntegers.not_dvd_exponent_of_bezout (p := 2) hgen
    (g := X ^ m + C (2 * a₃ + 1) * X + C (2 * c₃ + 1))
    (h := X ^ m + C (2 * a₃ + 1) * X + C (2 * c₃ + 1))
    (M := -(X ^ m * (C (2 * a₃ + 1) * X + C (2 * c₃ + 1)))
      - C (a₃ * (2 * a₃ + 1)) * X ^ 2
      + C ((2 * B₁ + 1) - (2 * a₃ + 1) * (2 * c₃ + 1)) * X
      - C (c₃ * (2 * c₃ + 1))) ?_ ?_ ?_ ?_
  · rw [hθ]
    have hxx : (X : ℤ[X]) ^ (2 * m) = (X ^ m) ^ 2 := by
      rw [← pow_mul, mul_comm m 2]
    rw [hxx]
    push_cast
    simp only [map_sub, map_add, map_mul, map_ofNat, map_one]
    ring
  · -- `ḡ = X ^ m + X + 1` is separable mod 2
    rw [hgmap]
    apply Polynomial.Separable.squarefree
    rw [Polynomial.Separable]
    have hder : derivative (X ^ m + X + 1 : (ZMod 2)[X])
        = C ((m : ZMod 2)) * X ^ (m - 1) + 1 := by
      rw [derivative_add, derivative_add, derivative_one, add_zero, derivative_X_pow,
        derivative_X]
    rw [hder]
    rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hm0 : ((m : ZMod 2)) = 0 := by
        rw [← Int.cast_natCast (R := ZMod 2), ← Int.cast_zero (R := ZMod 2)]
        exact zmod_intCast_eq (by omega)
      rw [hm0, map_zero, zero_mul, zero_add]
      exact isCoprime_one_right
    · have hm1 : ((m : ZMod 2)) = 1 := by
        rw [← Int.cast_natCast (R := ZMod 2), ← Int.cast_one (R := ZMod 2)]
        exact zmod_intCast_eq (by omega)
      rw [hm1, map_one, one_mul]
      refine ⟨1, -X, ?_⟩
      have hpow : (X : (ZMod 2)[X]) ^ (m - 1) * X = X ^ m := by
        rw [← pow_succ]
        congr 1
        omega
      linear_combination -hpow
  · exact fun q₀ _ hdvd => hdvd
  · -- the Bézout certificate, by cases on `a, c mod 4`
    have hMmap : ((-(X ^ m * (C (2 * a₃ + 1) * X + C (2 * c₃ + 1)))
        - C (a₃ * (2 * a₃ + 1)) * X ^ 2
        + C ((2 * B₁ + 1) - (2 * a₃ + 1) * (2 * c₃ + 1)) * X
        - C (c₃ * (2 * c₃ + 1))) : ℤ[X]).map (Int.castRingHom (ZMod 2))
        = X ^ (m + 1) + X ^ m + C ((a₃ : ZMod 2)) * X ^ 2 + C ((c₃ : ZMod 2)) := by
      simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_neg,
        Polynomial.map_pow, Polynomial.map_mul, map_C, map_X, Int.coe_castRingHom,
        e1, e2, e3, e4, e5, map_one, map_zero]
      linear_combination (-(X ^ (m + 1) : (ZMod 2)[X]) - X ^ m
        - C ((a₃ : ZMod 2)) * X ^ 2 - C ((c₃ : ZMod 2))) * h2P
    -- eval facts for the coprimality certificates
    have hg0 : (X ^ m + X + 1 : (ZMod 2)[X]).eval 0 ≠ 0 := by
      simp [zero_pow (by omega : m ≠ 0)]
    have hg1 : (X ^ m + X + 1 : (ZMod 2)[X]).eval 1 ≠ 0 := by
      have h3 : ((1 : ZMod 2)) + 1 + 1 = 1 := by
        have h2M : ((2 : ZMod 2)) = 0 := by exact_mod_cast ZMod.natCast_self 2
        linear_combination h2M
      simp only [eval_add, eval_pow, eval_X, eval_one, one_pow]
      rw [h3]
      exact one_ne_zero
    have hcopX : IsCoprime (X ^ m + X + 1 : (ZMod 2)[X]) X := by
      have h := isCoprime_X_sub_C_of_eval_ne_zero hg0
      rwa [map_zero, sub_zero] at h
    have hcopX1 : IsCoprime (X ^ m + X + 1 : (ZMod 2)[X]) (X + 1) := by
      have h := isCoprime_X_sub_C_of_eval_ne_zero hg1
      have hrw : (X - C (1 : ZMod 2) : (ZMod 2)[X]) = X + 1 := by
        rw [map_one]
        linear_combination -h2P
      rwa [hrw] at h
    suffices hcop : IsCoprime
        ((X ^ m + C (2 * a₃ + 1) * X + C (2 * c₃ + 1) : ℤ[X]).map (Int.castRingHom (ZMod 2)))
        (((-(X ^ m * (C (2 * a₃ + 1) * X + C (2 * c₃ + 1)))
          - C (a₃ * (2 * a₃ + 1)) * X ^ 2
          + C ((2 * B₁ + 1) - (2 * a₃ + 1) * (2 * c₃ + 1)) * X
          - C (c₃ * (2 * c₃ + 1))) : ℤ[X]).map (Int.castRingHom (ZMod 2))) by
      obtain ⟨u, w, huw⟩ := hcop
      exact ⟨u, 0, w, by rw [zero_mul]; linear_combination huw⟩
    rw [hgmap, hMmap]
    rcases Int.even_or_odd a₃ with ⟨s, hs⟩ | ⟨s, hs⟩ <;>
      rcases Int.even_or_odd c₃ with ⟨t, ht⟩ | ⟨t, ht⟩
    · -- a ≡ 1, c ≡ 1 mod 4 : M̄ = (X+1)² + ḡ (X+1)
      have hsZ : ((a₃ : ZMod 2)) = 0 := by
        rw [← Int.cast_zero (R := ZMod 2)]; exact zmod_intCast_eq (by omega)
      have htZ : ((c₃ : ZMod 2)) = 0 := by
        rw [← Int.cast_zero (R := ZMod 2)]; exact zmod_intCast_eq (by omega)
      rw [hsZ, htZ, map_zero, zero_mul, add_zero, add_zero]
      have hMrw : (X ^ (m + 1) + X ^ m : (ZMod 2)[X])
          = (X + 1) ^ 2 + (X ^ m + X + 1) * (X + 1) := by
        linear_combination (-(X ^ 2 : (ZMod 2)[X]) - 2 * X - 1) * h2P
      rw [hMrw]
      exact (hcopX1.pow_right).add_mul_left_right (X + 1)
    · -- a ≡ 1, c ≡ 3 mod 4 : M̄ = X² + ḡ (X+1)
      have hsZ : ((a₃ : ZMod 2)) = 0 := by
        rw [← Int.cast_zero (R := ZMod 2)]; exact zmod_intCast_eq (by omega)
      have htZ : ((c₃ : ZMod 2)) = 1 := by
        rw [← Int.cast_one (R := ZMod 2)]; exact zmod_intCast_eq (by omega)
      rw [hsZ, htZ, map_zero, map_one, zero_mul, add_zero]
      have hMrw : (X ^ (m + 1) + X ^ m + 1 : (ZMod 2)[X])
          = X ^ 2 + (X ^ m + X + 1) * (X + 1) := by
        linear_combination (-(X ^ 2 : (ZMod 2)[X]) - X) * h2P
      rw [hMrw]
      exact (hcopX.pow_right).add_mul_left_right (X + 1)
    · -- a ≡ 3, c ≡ 1 mod 4 : M̄ = 1 + ḡ (X+1)
      have hsZ : ((a₃ : ZMod 2)) = 1 := by
        rw [← Int.cast_one (R := ZMod 2)]; exact zmod_intCast_eq (by omega)
      have htZ : ((c₃ : ZMod 2)) = 0 := by
        rw [← Int.cast_zero (R := ZMod 2)]; exact zmod_intCast_eq (by omega)
      rw [hsZ, htZ, map_one, map_zero, one_mul, add_zero]
      have hMrw : (X ^ (m + 1) + X ^ m + X ^ 2 : (ZMod 2)[X])
          = 1 + (X ^ m + X + 1) * (X + 1) := by
        linear_combination (-X - 1 : (ZMod 2)[X]) * h2P
      rw [hMrw]
      exact isCoprime_one_right.add_mul_left_right (X + 1)
    · -- a ≡ c ≡ 3 mod 4 : excluded
      exact absurd ⟨⟨s + 1, by omega⟩, ⟨t + 1, by omega⟩⟩ h4

/-- `X ^ m + C s` is squarefree over `ZMod p` when `p ∤ m` and `s ≠ 0`. -/
private theorem squarefree_X_pow_add_C {m : ℕ} (hm : ¬p ∣ m) {s : ZMod p} (hs : s ≠ 0) :
    Squarefree (X ^ m + C s : (ZMod p)[X]) := by
  apply Polynomial.Separable.squarefree
  rw [Polynomial.Separable]
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero p)
  have hder : derivative (X ^ m + C s : (ZMod p)[X]) = C ((m : ZMod p)) * X ^ (m - 1) := by
    rw [derivative_add, derivative_C, add_zero, derivative_X_pow]
  rw [hder]
  have hmne : ((m : ZMod p)) ≠ 0 := by
    intro h0
    apply hm
    have h1 : (((m : ℤ)) : ZMod p) = 0 := by rw [Int.cast_natCast]; exact h0
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h1
  refine IsCoprime.mul_right ⟨0, C ((m : ZMod p))⁻¹, by
    rw [zero_mul, zero_add, ← map_mul, inv_mul_cancel₀ hmne, map_one]⟩ ?_
  refine IsCoprime.pow_right ?_
  have heval : (X ^ m + C s : (ZMod p)[X]).eval 0 ≠ 0 := by
    simp [zero_pow hm0, hs]
  have h := isCoprime_X_sub_C_of_eval_ne_zero heval
  rwa [map_zero, sub_zero] at h

/-- In case (2) of Theorem 1.1 (`p ∣ a`, `p ∤ c`), if moreover `p ∤ n` then `p` never
divides the index: `f ≡ X ^ n + c mod p` is separable. -/
theorem not_dvd_exponent_of_not_dvd_degree (_hn : 3 ≤ n) (hpn : ¬p ∣ n)
    (hB : B ^ 2 = a * c) (hpa : (p : ℤ) ∣ a) (hpc : ¬(p : ℤ) ∣ c)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hθ : minpoly ℤ θ = X ^ n + (C a * X ^ 2 + C (2 * B) * X + C c)) :
    ¬p ∣ RingOfIntegers.exponent θ := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hpB : (p : ℤ) ∣ B := hpp.dvd_of_dvd_pow (n := 2) (by rw [hB]; exact hpa.mul_right c)
  obtain ⟨a₁, ha₁⟩ := hpa
  obtain ⟨B₁, hB₁⟩ := hpB
  refine RingOfIntegers.not_dvd_exponent_of_bezout hgen
    (g := X ^ n + C c) (h := 1)
    (M := C a₁ * X ^ 2 + C (2 * B₁) * X) ?_ ?_ ?_ ?_
  · rw [hθ, ha₁, hB₁]
    simp only [map_mul, map_ofNat]
    ring
  · have hgmap : (X ^ n + C c : ℤ[X]).map (Int.castRingHom (ZMod p))
        = X ^ n + C ((c : ZMod p)) := by
      simp only [Polynomial.map_add, Polynomial.map_pow, map_C, map_X, Int.coe_castRingHom]
    rw [hgmap]
    have hcne : ((c : ZMod p)) ≠ 0 := fun h0 =>
      hpc ((ZMod.intCast_zmod_eq_zero_iff_dvd c p).mp h0)
    exact squarefree_X_pow_add_C hpn hcne
  · intro q₀ hq₀ hdvd
    rw [Polynomial.map_one] at hdvd
    exact absurd (isUnit_of_dvd_one hdvd) hq₀.not_isUnit
  · exact ⟨0, 1, 0, by simp⟩

/-- **Sufficiency in case (2) of Theorem 1.1**: `p ∣ a`, `p ∤ c`, `n = p ^ r * m` with
`r ≥ 1` and `p ∤ m`.  If the totally wild obstruction does not occur
(`¬(p² ∣ 2B ∧ p² ∣ c + (-c) ^ p ^ r)`) and no integer `d` with `p ∣ d ^ m + c`
satisfies `p² ∣ (-c) ^ p ^ r + c + a d² + 2 B d`, then `p` does not divide the index.
Together with `dvd_exponent_of_sq_dvd_of_sq_dvd` and `dvd_exponent_of_dvd_of_dvd_eval`
this determines case (2) completely. -/
theorem not_dvd_exponent_of_forall_not_dvd_eval {r m : ℕ} (_hn : 3 ≤ p ^ r * m)
    (_hr : 1 ≤ r) (hm : ¬p ∣ m) (hB : B ^ 2 = a * c) (hpa : (p : ℤ) ∣ a) (hpc : ¬(p : ℤ) ∣ c)
    (hw : ¬((p : ℤ) ^ 2 ∣ 2 * B ∧ (p : ℤ) ^ 2 ∣ c + (-c) ^ p ^ r))
    (hlin : ∀ d : ℤ, (p : ℤ) ∣ d ^ m + c →
      ¬(p : ℤ) ^ 2 ∣ (-c) ^ p ^ r + c + a * d ^ 2 + 2 * B * d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hθ : minpoly ℤ θ = X ^ (p ^ r * m) + (C a * X ^ 2 + C (2 * B) * X + C c)) :
    ¬p ∣ RingOfIntegers.exponent θ := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero p)
  -- `p ∣ B` and, since `p ∤ c`, in fact `p ^ 2 ∣ a`
  have hpB : (p : ℤ) ∣ B := hpp.dvd_of_dvd_pow (n := 2) (by rw [hB]; exact hpa.mul_right c)
  have hpa2 : (p : ℤ) ^ 2 ∣ a := by
    have h1 : (p : ℤ) ^ 2 ∣ a * c := by
      rw [← hB]
      exact pow_dvd_pow_of_dvd hpB 2
    exact ((hpp.coprime_iff_not_dvd.mpr hpc).pow_left).dvd_of_dvd_mul_right h1
  obtain ⟨a₂, ha₂⟩ := hpa2
  obtain ⟨B₁, hB₁⟩ := hpB
  -- `p ∣ c + (-c) ^ p ^ r` by Fermat
  have hpc1 : (p : ℤ) ∣ c + (-c) ^ p ^ r := by
    have h1 : (((c + (-c) ^ p ^ r : ℤ)) : ZMod p) = 0 := by
      push_cast
      rw [ZMod.pow_card_pow]
      ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h1
  obtain ⟨c₁, hc₁⟩ := hpc1
  -- the key identity for `X ^ n + C c`, from the pure one at `-c`
  obtain ⟨T, hT⟩ := Pure.key_identity p r hm0 (-c)
  have hkey : (X ^ (p ^ r * m) + C c : ℤ[X])
      = (X ^ m + C c) ^ p ^ r + C (p : ℤ) * ((X ^ m + C c) * T) + C (c + (-c) ^ p ^ r) := by
    have h := hT
    rw [show (X ^ (p ^ r * m) - C (-c) : ℤ[X]) = X ^ (p ^ r * m) + C c by
        rw [map_neg, sub_neg_eq_add],
      show (X ^ m - C (-c) : ℤ[X]) = X ^ m + C c by rw [map_neg, sub_neg_eq_add],
      show ((-c : ℤ) ^ p ^ r - -c) = c + (-c) ^ p ^ r by ring] at h
    exact h
  have hcne : ((c : ZMod p)) ≠ 0 := fun h0 =>
    hpc ((ZMod.intCast_zmod_eq_zero_iff_dvd c p).mp h0)
  have hgmap : (X ^ m + C c : ℤ[X]).map (Int.castRingHom (ZMod p))
      = X ^ m + C ((c : ZMod p)) := by
    simp only [Polynomial.map_add, Polynomial.map_pow, map_C, map_X, Int.coe_castRingHom]
  refine RingOfIntegers.not_dvd_exponent_of_bezout hgen
    (g := X ^ m + C c) (h := (X ^ m + C c) ^ (p ^ r - 1))
    (M := (X ^ m + C c) * T + C ((p : ℤ) * a₂) * X ^ 2 + C (2 * B₁) * X + C c₁)
    ?_ ?_ ?_ ?_
  · -- the splitting `f = g h + p M`
    rw [hθ]
    have hgh : (X ^ m + C c : ℤ[X]) * (X ^ m + C c) ^ (p ^ r - 1)
        = (X ^ m + C c) ^ p ^ r := by
      rw [← pow_succ']
      congr 1
      have h1 : 1 ≤ p ^ r := Nat.one_le_pow r p hp.out.pos
      omega
    have hca : C a = C ((p : ℤ)) * C ((p : ℤ) * a₂) := by
      rw [← map_mul]
      congr 1
      rw [ha₂]
      ring
    have hcB : C (2 * B) = C ((p : ℤ)) * C (2 * B₁) := by
      rw [← map_mul]
      congr 1
      rw [hB₁]
      ring
    have hcc : C (c + (-c) ^ p ^ r) = C ((p : ℤ)) * C c₁ := by
      rw [hc₁, map_mul]
    linear_combination hkey + X ^ 2 * hca + X * hcB + hcc - hgh
  · -- `ḡ = X ^ m + c̄` is separable
    rw [hgmap]
    exact squarefree_X_pow_add_C hm hcne
  · -- every irreducible factor of `h̄ = ḡ ^ (p ^ r - 1)` divides `ḡ`
    intro q₀ hq₀ hdvd
    rw [Polynomial.map_pow] at hdvd
    exact hq₀.prime.dvd_of_dvd_pow hdvd
  · -- the Bézout certificate
    have eB : (((2 * B₁ : ℤ)) : ZMod p) = 2 * ((B₁ : ℤ) : ZMod p) := by
      push_cast
      ring
    have ePa : ((((p : ℤ) * a₂ : ℤ)) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr ⟨a₂, rfl⟩
    have hMmap : (((X ^ m + C c) * T + C ((p : ℤ) * a₂) * X ^ 2 + C (2 * B₁) * X
        + C c₁ : ℤ[X])).map (Int.castRingHom (ZMod p))
        = C (2 * ((B₁ : ℤ) : ZMod p)) * X + C (((c₁ : ℤ)) : ZMod p)
          + (X ^ m + C ((c : ZMod p))) * T.map (Int.castRingHom (ZMod p)) := by
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_C, map_X,
        Int.coe_castRingHom, eB, ePa, map_zero]
      ring
    suffices hcop : IsCoprime (X ^ m + C ((c : ZMod p)) : (ZMod p)[X])
        (C (2 * ((B₁ : ℤ) : ZMod p)) * X + C (((c₁ : ℤ)) : ZMod p)) by
      have hcopM : IsCoprime
          ((X ^ m + C c : ℤ[X]).map (Int.castRingHom (ZMod p)))
          ((((X ^ m + C c) * T + C ((p : ℤ) * a₂) * X ^ 2 + C (2 * B₁) * X
            + C c₁ : ℤ[X])).map (Int.castRingHom (ZMod p))) := by
        rw [hgmap, hMmap]
        exact hcop.add_mul_left_right (T.map (Int.castRingHom (ZMod p)))
      obtain ⟨u, w, huw⟩ := hcopM
      exact ⟨u, 0, w, by rw [zero_mul]; linear_combination huw⟩
    by_cases hβ : (2 * ((B₁ : ℤ) : ZMod p)) = 0
    · -- constant case: `c₁` must be a unit mod `p` by the wildness hypothesis
      have hγ : (((c₁ : ℤ)) : ZMod p) ≠ 0 := by
        intro hγ0
        apply hw
        constructor
        · have h1 : (p : ℤ) ∣ 2 * B₁ := by
            have h2 : (((2 * B₁ : ℤ)) : ZMod p) = 0 := by rw [eB]; exact hβ
            exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h2
          obtain ⟨t, ht⟩ := h1
          exact ⟨t, by linear_combination 2 * hB₁ + (p : ℤ) * ht⟩
        · have h1 : (p : ℤ) ∣ c₁ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hγ0
          obtain ⟨t, ht⟩ := h1
          exact ⟨t, by rw [hc₁, ht]; ring⟩
      rw [hβ, map_zero, zero_mul, zero_add]
      exact ⟨0, C (((c₁ : ℤ)) : ZMod p)⁻¹, by
        rw [zero_mul, zero_add, ← map_mul, inv_mul_cancel₀ hγ, map_one]⟩
    · -- linear case: the root `d₀ = -c₁ / (2 B₁)` is not a root of `ḡ` by `hlin`
      have heval : (X ^ m + C ((c : ZMod p)) : (ZMod p)[X]).eval
          (-(((c₁ : ℤ)) : ZMod p) * (2 * ((B₁ : ℤ) : ZMod p))⁻¹) ≠ 0 := by
        intro h0
        simp only [eval_add, eval_pow, eval_X, eval_C] at h0
        obtain ⟨d, hd⟩ := ZMod.intCast_surjective
          (-(((c₁ : ℤ)) : ZMod p) * (2 * ((B₁ : ℤ) : ZMod p))⁻¹)
        have hdc : (p : ℤ) ∣ d ^ m + c := by
          have h1 : (((d ^ m + c : ℤ)) : ZMod p) = 0 := by
            push_cast
            rw [hd]
            exact h0
          exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h1
        refine hlin d hdc ?_
        have hlincast : (((c₁ + 2 * B₁ * d : ℤ)) : ZMod p) = 0 := by
          push_cast
          rw [hd]
          have hinv := mul_inv_cancel₀ hβ
          linear_combination -(((c₁ : ℤ) : ZMod p)) * hinv
        have h1 : (p : ℤ) ∣ c₁ + 2 * B₁ * d :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hlincast
        obtain ⟨t, ht⟩ := h1
        refine ⟨a₂ * d ^ 2 + t, ?_⟩
        linear_combination hc₁ + d ^ 2 * ha₂ + 2 * d * hB₁ + (p : ℤ) * ht
      have hcoplin := isCoprime_X_sub_C_of_eval_ne_zero heval
      have hd₀mul : (2 * ((B₁ : ℤ) : ZMod p))
          * (-(((c₁ : ℤ)) : ZMod p) * (2 * ((B₁ : ℤ) : ZMod p))⁻¹)
          = -(((c₁ : ℤ)) : ZMod p) := by
        have hinv := mul_inv_cancel₀ hβ
        linear_combination -(((c₁ : ℤ) : ZMod p)) * hinv
      have hlineq : C (2 * ((B₁ : ℤ) : ZMod p)) * X + C (((c₁ : ℤ)) : ZMod p)
          = C (2 * ((B₁ : ℤ) : ZMod p))
            * (X - C (-(((c₁ : ℤ)) : ZMod p) * (2 * ((B₁ : ℤ) : ZMod p))⁻¹)) := by
        rw [mul_sub, ← map_mul, hd₀mul, map_neg, sub_neg_eq_add]
      rw [hlineq]
      refine IsCoprime.mul_right ⟨0, C (2 * ((B₁ : ℤ) : ZMod p))⁻¹, by
        rw [zero_mul, zero_add, ← map_mul, inv_mul_cancel₀ hβ, map_one]⟩ hcoplin

/-- **Case (4) of Theorem 1.1 of [jakharkaurkumar2023], complete** (`p = 2`, `a` and `c`
odd, `n = 2 m`): `2` divides the index `[𝓞 K : ℤ[θ]]` if and only if
`a ≡ c ≡ 3 mod 4`. -/
theorem two_dvd_exponent_iff {m : ℕ} (hm : 2 ≤ m) (hB : B ^ 2 = a * c)
    (ha : ¬(2 : ℤ) ∣ a) (hc : ¬(2 : ℤ) ∣ c)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hθ : minpoly ℤ θ = X ^ (2 * m) + (C a * X ^ 2 + C (2 * B) * X + C c)) :
    2 ∣ RingOfIntegers.exponent θ ↔ (4 : ℤ) ∣ a + 1 ∧ (4 : ℤ) ∣ c + 1 := by
  constructor
  · intro h
    by_contra h4
    exact not_two_dvd_exponent_of_not_mod_four hm hB ha hc h4 hgen hθ h
  · rintro ⟨ha4, hc4⟩
    exact two_dvd_exponent_of_mod_four hm hB ha4 hc4 hθ

/-- **Case (2) of Theorem 1.1 of [jakharkaurkumar2023], complete**: for `p ∣ a`,
`p ∤ c` and `n = p ^ r * m` with `r ≥ 1`, `p ∤ m`, the prime `p` divides the index
`[𝓞 K : ℤ[θ]]` if and only if either the totally wild obstruction occurs
(`p² ∣ 2B` and `p² ∣ c + (-c) ^ p ^ r`) or some integer `d` with `p ∣ d ^ m + c`
satisfies `p² ∣ (-c) ^ p ^ r + c + a d² + 2 B d`. -/
theorem dvd_exponent_iff_of_dvd_of_not_dvd {r m : ℕ} (hn : 3 ≤ p ^ r * m) (hr : 1 ≤ r)
    (hm : ¬p ∣ m) (hB : B ^ 2 = a * c) (hpa : (p : ℤ) ∣ a) (hpc : ¬(p : ℤ) ∣ c)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hθ : minpoly ℤ θ = X ^ (p ^ r * m) + (C a * X ^ 2 + C (2 * B) * X + C c)) :
    p ∣ RingOfIntegers.exponent θ ↔
      ((p : ℤ) ^ 2 ∣ 2 * B ∧ (p : ℤ) ^ 2 ∣ c + (-c) ^ p ^ r) ∨
        ∃ d : ℤ, (p : ℤ) ∣ d ^ m + c ∧
          (p : ℤ) ^ 2 ∣ (-c) ^ p ^ r + c + a * d ^ 2 + 2 * B * d := by
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero p)
  constructor
  · intro h
    by_contra hcon
    refine absurd h (not_dvd_exponent_of_forall_not_dvd_eval hn hr hm hB hpa hpc ?_ ?_
      hgen hθ)
    · exact fun hwand => hcon (Or.inl hwand)
    · exact fun d hd hsq => hcon (Or.inr ⟨d, hd, hsq⟩)
  · rintro (⟨hw1, hw2⟩ | ⟨d, hd, hsq⟩)
    · -- totally wild necessity; `p ^ 2 ∣ a` is automatic
      have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
      have hpB : (p : ℤ) ∣ B :=
        hpp.dvd_of_dvd_pow (n := 2) (by rw [hB]; exact hpa.mul_right c)
      have hpa2 : (p : ℤ) ^ 2 ∣ a := by
        have h1 : (p : ℤ) ^ 2 ∣ a * c := by
          rw [← hB]
          exact pow_dvd_pow_of_dvd hpB 2
        exact ((hpp.coprime_iff_not_dvd.mpr hpc).pow_left).dvd_of_dvd_mul_right h1
      exact dvd_exponent_of_sq_dvd_of_sq_dvd hn hr hm0 hpa2 hw1 hw2 hθ
    · exact dvd_exponent_of_dvd_of_dvd_eval hn hr hm0 hB hpa hd hsq hθ

/-- **Corrected Corollary 1.2 of [jakharkaurkumar2023]** (global monogenicity).  For
irreducible `f = X ^ n + a X ^ 2 + 2 B X + c` with `B ^ 2 = a c` and root `θ`
generating `K`, `ℤ[θ] = 𝓞 K` if and only if

1. every prime divisor of `c` divides `a` (the *correction* to the printed
   Corollary 1.2, forced by the corrected case (3) of Theorem 1.1);
2. for `p ∣ a`, `p ∣ c`: `p ^ 2 ∤ c`;
3. for `p ∣ a`, `p ∤ c` and `n = p ^ r * m` with `r ≥ 1`, `p ∤ m`: neither the totally
   wild obstruction nor a linear-congruence witness occurs;
4. for `p ∤ 2 B`: `p ^ 2 ∤ D`;
5. for `p = 2` with `a c` odd and `n` even: not both `a ≡ 3` and `c ≡ 3 mod 4`.

Primes with `p ∣ a`, `p ∤ c`, `p ∤ n`, and the prime `2` when `a c` is odd and `n` is
odd, never divide the index, so no condition is imposed there. -/
theorem monogenic_iff (hn : 3 ≤ n) (hB : B ^ 2 = a * c)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hθ : minpoly ℤ θ = X ^ n + (C a * X ^ 2 + C (2 * B) * X + C c)) :
    Algebra.adjoin ℤ {θ} = ⊤ ↔
      (∀ p : ℕ, p.Prime → (p : ℤ) ∣ c → (p : ℤ) ∣ a) ∧
      (∀ p : ℕ, p.Prime → (p : ℤ) ∣ a → (p : ℤ) ∣ c → ¬(p : ℤ) ^ 2 ∣ c) ∧
      (∀ p r m : ℕ, p.Prime → n = p ^ r * m → 1 ≤ r → ¬p ∣ m → (p : ℤ) ∣ a →
        ¬(p : ℤ) ∣ c →
        ¬(((p : ℤ) ^ 2 ∣ 2 * B ∧ (p : ℤ) ^ 2 ∣ c + (-c) ^ p ^ r) ∨
          ∃ d : ℤ, (p : ℤ) ∣ d ^ m + c ∧
            (p : ℤ) ^ 2 ∣ (-c) ^ p ^ r + c + a * d ^ 2 + 2 * B * d)) ∧
      (∀ p : ℕ, p.Prime → ¬(p : ℤ) ∣ 2 * B → ¬(p : ℤ) ^ 2 ∣ D n B c) ∧
      (∀ m : ℕ, n = 2 * m → ¬(2 : ℤ) ∣ a * c →
        ¬((4 : ℤ) ∣ a + 1 ∧ (4 : ℤ) ∣ c + 1)) := by
  rw [RingOfIntegers.adjoin_eq_top_iff_forall_prime_not_dvd_exponent]
  constructor
  · intro hall
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro p hpprime hpc
      by_contra hpa
      haveI : Fact p.Prime := ⟨hpprime⟩
      exact hall p hpprime (dvd_exponent_of_dvd_of_not_dvd hn hB hpa hpc hθ)
    · intro p hpprime hpa hpc hc2
      haveI : Fact p.Prime := ⟨hpprime⟩
      exact hall p hpprime ((dvd_exponent_iff_of_dvd_of_dvd hn hB hpa hpc hθ hgen).mpr hc2)
    · intro p r m hpprime hnm hr hm hpa hpc hcon
      haveI : Fact p.Prime := ⟨hpprime⟩
      have hθ' : minpoly ℤ θ = X ^ (p ^ r * m) + (C a * X ^ 2 + C (2 * B) * X + C c) := by
        rw [← hnm]
        exact hθ
      exact hall p hpprime ((dvd_exponent_iff_of_dvd_of_not_dvd (hnm ▸ hn) hr hm hB hpa
        hpc hgen hθ').mpr hcon)
    · intro p hpprime hp2B hD2
      haveI : Fact p.Prime := ⟨hpprime⟩
      exact hall p hpprime ((dvd_exponent_iff_of_not_dvd hn hB hp2B hθ hgen).mpr hD2)
    · intro m hnm h2ac hmod
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have h2a : ¬(2 : ℤ) ∣ a := fun h => h2ac (h.mul_right c)
      have h2c : ¬(2 : ℤ) ∣ c := fun h => h2ac (Dvd.dvd.mul_left h a)
      have hm2 : 2 ≤ m := by omega
      have hθ' : minpoly ℤ θ = X ^ (2 * m) + (C a * X ^ 2 + C (2 * B) * X + C c) := by
        rw [← hnm]
        exact hθ
      exact hall 2 Nat.prime_two ((two_dvd_exponent_iff hm2 hB h2a h2c hgen hθ').mpr hmod)
  · rintro ⟨h3, h1, h2, h5, h4⟩ p hpprime
    haveI : Fact p.Prime := ⟨hpprime⟩
    by_cases hp2B : (p : ℤ) ∣ 2 * B
    · by_cases hpa : (p : ℤ) ∣ a
      · by_cases hpc : (p : ℤ) ∣ c
        · rw [dvd_exponent_iff_of_dvd_of_dvd hn hB hpa hpc hθ hgen]
          exact h1 p hpprime hpa hpc
        · by_cases hpn : p ∣ n
          · obtain ⟨r, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd
              (by omega : n ≠ 0) p hpprime.ne_one
            have hr : 1 ≤ r := by
              rcases Nat.eq_zero_or_pos r with h0 | h0
              · exfalso
                rw [h0, pow_zero, one_mul] at hnm
                exact hm (hnm ▸ hpn)
              · exact h0
            have hθ' : minpoly ℤ θ
                = X ^ (p ^ r * m) + (C a * X ^ 2 + C (2 * B) * X + C c) := by
              rw [← hnm]
              exact hθ
            rw [dvd_exponent_iff_of_dvd_of_not_dvd (hnm ▸ hn) hr hm hB hpa hpc hgen hθ']
            exact h2 p r m hpprime hnm hr hm hpa hpc
          · exact not_dvd_exponent_of_not_dvd_degree hn hpn hB hpa hpc hgen hθ
      · -- `p ∤ a`, hence `p ∤ c` by the corrected case (3), hence `p = 2` with `a c` odd
        have hpc : ¬(p : ℤ) ∣ c := fun hpc => hpa (h3 p hpprime hpc)
        have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpprime
        have hpB : ¬(p : ℤ) ∣ B := by
          intro h
          have hac : (p : ℤ) ∣ a * c := by
            rw [← hB, sq]
            exact h.mul_left B
          rcases hpp.dvd_mul.mp hac with h' | h'
          exacts [hpa h', hpc h']
        have hp2 : p = 2 := by
          rcases hpp.dvd_mul.mp hp2B with h' | h'
          · have hdvd2 : p ∣ 2 := by exact_mod_cast h'
            exact (Nat.prime_dvd_prime_iff_eq hpprime Nat.prime_two).mp hdvd2
          · exact absurd h' hpB
        subst hp2
        have h2ac : ¬(2 : ℤ) ∣ a * c := by
          intro h
          rcases hpp.dvd_mul.mp h with h' | h'
          exacts [hpa h', hpc h']
        rcases Nat.even_or_odd n with ⟨m, hm'⟩ | hodd
        · have hnm : n = 2 * m := by omega
          have hm2 : 2 ≤ m := by omega
          have hθ' : minpoly ℤ θ
              = X ^ (2 * m) + (C a * X ^ 2 + C (2 * B) * X + C c) := by
            rw [← hnm]
            exact hθ
          rw [two_dvd_exponent_iff hm2 hB hpa hpc hgen hθ']
          exact h4 m hnm h2ac
        · obtain ⟨k, hk⟩ := hodd
          exact not_two_dvd_exponent_of_odd_degree hn (by omega) hpa hpc hgen hθ
    · rw [dvd_exponent_iff_of_not_dvd hn hB hp2B hθ hgen]
      exact h5 p hpprime hp2B

/-- **Corollary 1.4 of [jakharkaurkumar2023]**.  Let `f = X ^ n + a X ^ 2 + 2 B X + c` be
irreducible with `B ^ 2 = a c`, `c` a squarefree non-unit, the sets of primes dividing
`a`, `b = 2 B` and `c` all equal, and `2 ∣ c` or `a ≡ 1` or `c ≡ 1 mod 4`.  Then
`ℤ[θ] = 𝓞 K` if and only if for every prime `p` dividing `D` and not dividing `a` one has
`p ^ 2 ∤ D`.

Here `D = NumberField.Quadrinomial.D n B c` differs from the paper's discriminant `D_f`
only by the sign unit `(-1) ^ (n (n-1) / 2)`, so the divisibility conditions coincide.
Under the hypotheses the same-primes assumption makes cases (2) and (3) of Theorem 1.1
vacuous, squarefreeness of `c` discharges case (1), and the `mod 4` assumption discharges
case (4), leaving only case (5). -/
theorem monogenic_iff_of_squarefree (hn : 3 ≤ n) (hB : B ^ 2 = a * c)
    (hsf : Squarefree c) (_hcnu : ¬ IsUnit c)
    (hac : ∀ p : ℕ, p.Prime → ((p : ℤ) ∣ a ↔ (p : ℤ) ∣ c))
    (hab : ∀ p : ℕ, p.Prime → ((p : ℤ) ∣ a ↔ (p : ℤ) ∣ 2 * B))
    (hmod : (2 : ℤ) ∣ c ∨ (4 : ℤ) ∣ a - 1 ∨ (4 : ℤ) ∣ c - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hθ : minpoly ℤ θ = X ^ n + (C a * X ^ 2 + C (2 * B) * X + C c)) :
    Algebra.adjoin ℤ {θ} = ⊤ ↔
      ∀ p : ℕ, p.Prime → (p : ℤ) ∣ D n B c → ¬(p : ℤ) ∣ a → ¬(p : ℤ) ^ 2 ∣ D n B c := by
  rw [monogenic_iff hn hB hgen hθ]
  constructor
  · rintro ⟨_, _, _, hc5, _⟩ p hpprime _ hpa
    exact hc5 p hpprime (fun h2B => hpa ((hab p hpprime).mpr h2B))
  · intro hT
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro p hpprime hpc
      exact (hac p hpprime).mpr hpc
    · intro p hpprime _ _ hp2c
      have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpprime
      exact hpp.not_unit (hsf (p : ℤ) (by rw [← sq]; exact hp2c))
    · intro p r m hpprime _ _ _ hpa hpc _
      exact hpc ((hac p hpprime).mp hpa)
    · intro p hpprime hp2B
      have hpa : ¬(p : ℤ) ∣ a := fun h => hp2B ((hab p hpprime).mp h)
      by_cases hpD : (p : ℤ) ∣ D n B c
      · exact hT p hpprime hpD hpa
      · exact fun h => hpD (dvd_trans (dvd_pow_self _ two_ne_zero) h)
    · intro m _ h2ac
      have h2c : ¬(2 : ℤ) ∣ c := fun h => h2ac (Dvd.dvd.mul_left h a)
      rcases hmod with h | h | h
      · exact absurd h h2c
      · rintro ⟨ha1, _⟩; omega
      · rintro ⟨_, hc1⟩; omega

end Sufficiency

end NumberField.Quadrinomial
