/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.Monogenic.Pure

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
* `NumberField.Quadrinomial.dvd_exponent_of_dvd_of_sq_dvd` — the necessity half of
  **case (2)** in the totally wild subcase: if `p` is odd, `p ∣ a`, `p ∤ c`, `n = p ^ r * m`
  with `r ≥ 1`, and `p ^ 2` divides both `b / 2 = B` and `(c + (-c) ^ p ^ r) / p ⋯` — more
  precisely if `p ^ 2 ∣ 2 * B` and `p ^ 2 ∣ c + (-c) ^ p ^ r` — then `p ∣ [𝓞 K : ℤ[θ]]`,
  by the generalized obstruction lemma at the repeated factor `X ^ m + c`.

The remaining cases of Theorem 1.1 are future work: case (5) (`p ∤ b`, the tame double
root at `- n b / (2 a (n - 2))`) is a direct port of the Kaur--Kumar tame analysis using
`modEq_key`; the sufficiency halves of the wild cases (2)--(4) are the genuinely open
formalization problem (they would follow from a general Dedekind criterion, or from a new
descent argument — the pure-field subfield trick has no analogue here).

## References

* [A. Jakhar, S. Kaur, S. Kumar, *On power basis of a class of number fields*,
  arXiv:2303.03138 (2023)][jakharkaurkumar2023]
-/

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

end IntegerLemmas

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

end Main

end NumberField.Quadrinomial
