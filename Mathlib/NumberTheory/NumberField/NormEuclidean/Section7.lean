/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.NormEuclidean.Character
public import Mathlib.NumberTheory.DirichletCharacter.PolyaVinogradov
public import Mathlib.Data.Int.CardIntervalMod

/-!
# The candidate set of Section 7

The character-sum argument of `Mathlib.NumberTheory.NumberField.NormEuclidean.Character` needs a
lower bound for the number of candidates
`S = {u < p / q₁ : q₁ ∤ u, u ≡ r₀ (mod q₂ ^ 2)}`,
and needs to know that every candidate `u` has `q₁ u` invertible modulo `p`.  Both are proved
here, giving Section 7 with a completely explicit sufficient condition.

The count is elementary: the residue class of `r₀` modulo `q₂ ^ 2` contributes at least
`M / q₂ ^ 2 - 1` integers below `M`, and the multiples of `q₁` inside it form a single class
modulo `q₁ q₂ ^ 2` (the moduli are coprime) and so contribute at most `M / (q₁ q₂ ^ 2) + 1`.
With `M = p / q₁` this gives `#S ≥ p (q₁ - 1) / (q₁ ^ 2 q₂ ^ 2) - 3`.

Taking instead for `S` a *single* arithmetic progression `u ≡ ρ (mod q₁ q₂ ^ 2)`, with `ρ ≡ 1`
modulo `q₁`, makes the condition `q₁ ∤ u` automatic and lets the Pólya–Vinogradov inequality be
applied directly, giving Section 7 with no analytic hypothesis at all:
`NumberField.not_normEuclidean_of_eisensteinDumas_of_gcd_lt`.

## Main results

* `Nat.le_card_range_filter_modEq_not_dvd`: the elementary count.
* `NumberField.le_card_candidates`: the lower bound `p (q₁ - 1) / (q₁ ^ 2 q₂ ^ 2) - 3`.
* `NumberField.not_normEuclidean_of_charSum_of_lt`: Section 7, with the size condition on the
  character-sum bound `B` made explicit.
* `Nat.filter_range_modEq_eq_image`, `Nat.sum_filter_range_modEq`: a residue class below `M`,
  parametrised by an initial segment.
* `NumberField.not_normEuclidean_of_eisensteinDumas_of_gcd_lt`: Section 7 unconditionally, with
  the Pólya–Vinogradov inequality supplied.
-/

public section

open Finset

namespace Nat

theorem card_range_filter_modEq {M Q : ℕ} (hQ : 0 < Q) (v : ℕ) :
    (#{u ∈ Finset.range M | u ≡ v [MOD Q]} : ℚ)
      = ((⌈((M : ℚ) - (v % Q : ℕ)) / (Q : ℚ)⌉ : ℤ) : ℚ) := by
  have h : ((#{u ∈ Finset.range M | u ≡ v [MOD Q]} : ℕ) : ℤ)
      = ⌈((M : ℚ) - (v % Q : ℕ)) / (Q : ℚ)⌉ := by
    rw [← Nat.count_eq_card_filter_range]
    exact Nat.count_modEq_card_eq_ceil _ hQ v
  exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) h

theorem le_card_range_filter_modEq {M Q : ℕ} (hQ : 0 < Q) (v : ℕ) :
    (M : ℚ) / Q - 1 ≤ #{u ∈ Finset.range M | u ≡ v [MOD Q]} := by
  have hQQ : (0 : ℚ) < Q := by exact_mod_cast hQ
  rw [card_range_filter_modEq hQ v]
  have h1 := Int.le_ceil (((M : ℚ) - (v % Q : ℕ)) / (Q : ℚ))
  have h2 : ((v % Q : ℕ) : ℚ) < Q := by exact_mod_cast Nat.mod_lt _ hQ
  have h3 : ((M : ℚ) - (v % Q : ℕ)) / Q = (M : ℚ) / Q - ((v % Q : ℕ) : ℚ) / Q := by ring
  have h4 : ((v % Q : ℕ) : ℚ) / Q ≤ 1 := by rw [div_le_one hQQ]; linarith
  linarith

theorem card_range_filter_modEq_le {M Q : ℕ} (hQ : 0 < Q) (v : ℕ) :
    (#{u ∈ Finset.range M | u ≡ v [MOD Q]} : ℚ) ≤ (M : ℚ) / Q + 1 := by
  have hQQ : (0 : ℚ) < Q := by exact_mod_cast hQ
  rw [card_range_filter_modEq hQ v]
  have h1 := Int.ceil_lt_add_one (((M : ℚ) - (v % Q : ℕ)) / (Q : ℚ))
  have h2 : (0 : ℚ) ≤ ((v % Q : ℕ) : ℚ) := by positivity
  have h3 : ((M : ℚ) - (v % Q : ℕ)) / Q ≤ (M : ℚ) / Q := by
    rw [div_le_div_iff_of_pos_right hQQ]; linarith
  linarith

theorem le_card_range_filter_modEq_not_dvd {M Q q : ℕ} (hQ : 0 < Q) (hq : 0 < q)
    (hcop : Nat.Coprime Q q) (v : ℕ) :
    (M : ℚ) / Q - (M : ℚ) / (q * Q) - 2 ≤
      #{u ∈ Finset.range M | ¬ q ∣ u ∧ u ≡ v [MOD Q]} := by
  classical
  obtain ⟨c, hcQ, hcq⟩ := Nat.chineseRemainder hcop v 0
  have hsub : {u ∈ Finset.range M | u ≡ v [MOD Q]} ⊆
      {u ∈ Finset.range M | ¬ q ∣ u ∧ u ≡ v [MOD Q]} ∪
      {u ∈ Finset.range M | u ≡ c [MOD Q * q]} := by
    intro u hu
    rw [Finset.mem_filter] at hu
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases hdvd : q ∣ u
    · refine Or.inr ⟨hu.1, ?_⟩
      refine (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨hu.2.trans hcQ.symm, ?_⟩
      exact ((Nat.modEq_zero_iff_dvd).2 hdvd).trans hcq.symm
    · exact Or.inl ⟨hu.1, hdvd, hu.2⟩
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_le
    {u ∈ Finset.range M | ¬ q ∣ u ∧ u ≡ v [MOD Q]}
    {u ∈ Finset.range M | u ≡ c [MOD Q * q]}
  have hA := le_card_range_filter_modEq (M := M) hQ v
  have hC := card_range_filter_modEq_le (M := M) (Nat.mul_pos hQ hq) c
  have hcast : (#{u ∈ Finset.range M | u ≡ v [MOD Q]} : ℚ) ≤
      (#{u ∈ Finset.range M | ¬ q ∣ u ∧ u ≡ v [MOD Q]} : ℚ) +
      (#{u ∈ Finset.range M | u ≡ c [MOD Q * q]} : ℚ) := by
    exact_mod_cast le_trans hcard hunion
  have hqQ : ((Q * q : ℕ) : ℚ) = (q : ℚ) * (Q : ℚ) := by push_cast; ring
  rw [hqQ] at hC
  linarith

theorem filter_range_modEq_eq_image {M Q r : ℕ} (hQ : 0 < Q) (hr : r < Q) :
    {u ∈ Finset.range M | u ≡ r [MOD Q]}
      = (Finset.range ((M - r + Q - 1) / Q)).image (fun t => r + Q * t) := by
  classical
  ext u
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨huM, hucong⟩
    have hmod : u % Q = r := by
      have h : u % Q = r % Q := hucong
      rwa [Nat.mod_eq_of_lt hr] at h
    have hu : r + Q * (u / Q) = u := by rw [← hmod]; exact Nat.mod_add_div u Q
    refine ⟨u / Q, ?_, hu⟩
    rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hQ]
    have hru : r ≤ u := Nat.le.intro hu
    calc (u / Q + 1) * Q = Q * (u / Q) + Q := by ring
      _ = (u - r) + Q := by rw [Nat.eq_sub_of_add_eq' hu]
      _ ≤ M - r + Q - 1 := by omega
  · rintro ⟨t, htT, rfl⟩
    have hle : Q * t + Q ≤ M - r + Q - 1 := by
      have h1 : (t + 1) * Q ≤ M - r + Q - 1 := by
        rw [← Nat.le_div_iff_mul_le hQ]
        omega
      calc Q * t + Q = (t + 1) * Q := by ring
        _ ≤ M - r + Q - 1 := h1
    refine ⟨?_, ?_⟩
    · obtain ⟨s, hs⟩ : ∃ s, Q * t = s := ⟨_, rfl⟩
      rw [hs] at hle ⊢
      omega
    · change (r + Q * t) % Q = r % Q
      exact Nat.add_mul_mod_self_left r Q t

theorem sum_filter_range_modEq {M Q r : ℕ} (hQ : 0 < Q) (hr : r < Q) {A : Type*}
    [AddCommMonoid A] (f : ℕ → A) :
    ∑ u ∈ {u ∈ Finset.range M | u ≡ r [MOD Q]}, f u
      = ∑ t ∈ Finset.range ((M - r + Q - 1) / Q), f (r + Q * t) := by
  classical
  rw [filter_range_modEq_eq_image hQ hr,
    Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hQ (add_left_cancel h))]

end Nat

namespace NumberField

/-- The set of candidates in Section 7, rewritten with `Nat.ModEq`. -/
theorem filter_natCast_zmod_eq {M Q : ℕ} [NeZero Q] (q v : ℕ) :
    {u ∈ Finset.range M | ¬ q ∣ u ∧ ((u : ℕ) : ZMod Q) = ((v : ℕ) : ZMod Q)}
      = {u ∈ Finset.range M | ¬ q ∣ u ∧ u ≡ v [MOD Q]} := by
  refine Finset.filter_congr fun u _ => ?_
  simp only [ZMod.natCast_eq_natCast_iff]

/-- **Lower bound for the number of candidates.** -/
theorem le_card_candidates {p q₁ q₂ : ℕ} (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (hne : q₁ ≠ q₂)
    (v : ℕ) :
    (p : ℝ) * ((q₁ : ℝ) - 1) / ((q₁ : ℝ) ^ 2 * (q₂ : ℝ) ^ 2) - 3 ≤
      #{u ∈ Finset.range (p / q₁) |
        ¬ q₁ ∣ u ∧ ((u : ℕ) : ZMod (q₂ ^ 2)) = ((v : ℕ) : ZMod (q₂ ^ 2))} := by
  have : NeZero (q₂ ^ 2) := ⟨pow_ne_zero 2 hq₂.pos.ne'⟩
  rw [filter_natCast_zmod_eq]
  set M := p / q₁ with hM
  have hq₁pos : (0 : ℝ) < q₁ := by exact_mod_cast hq₁.pos
  have hq₂pos : (0 : ℝ) < q₂ := by exact_mod_cast hq₂.pos
  have hcop : Nat.Coprime (q₂ ^ 2) q₁ :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes hq₂ hq₁).2 (Ne.symm hne))
  have hQ : 0 < q₂ ^ 2 := pow_pos hq₂.pos 2
  have hbase := Nat.le_card_range_filter_modEq_not_dvd (M := M) hQ hq₁.pos hcop v
  have hreal : (M : ℝ) / ((q₂ : ℝ) ^ 2) - (M : ℝ) / ((q₁ : ℝ) * (q₂ : ℝ) ^ 2) - 2 ≤
      #{u ∈ Finset.range M | ¬ q₁ ∣ u ∧ u ≡ v [MOD q₂ ^ 2]} := by
    have := (Rat.cast_le (K := ℝ)).2 hbase
    push_cast at this
    convert this using 2
  -- `M = p / q₁` is between `p / q₁ - 1` and `p / q₁`
  have hq₁ge : (1 : ℝ) ≤ (q₁ : ℝ) := by exact_mod_cast hq₁.one_lt.le
  have hq₂one : (1 : ℝ) ≤ (q₂ : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ (q₂ : ℝ) := by exact_mod_cast hq₂.one_lt.le
    nlinarith
  have hdm : q₁ * M + p % q₁ = p := by rw [hM]; exact Nat.div_add_mod p q₁
  have h2 : (q₁ : ℝ) * (M : ℝ) + ((p % q₁ : ℕ) : ℝ) = (p : ℝ) := by exact_mod_cast hdm
  have h3 : ((p % q₁ : ℕ) : ℝ) < (q₁ : ℝ) := by exact_mod_cast Nat.mod_lt _ hq₁.pos
  have hMge : (p : ℝ) / q₁ - 1 ≤ (M : ℝ) := by
    rw [sub_le_iff_le_add, div_le_iff₀ hq₁pos]
    nlinarith
  have hden : (0 : ℝ) < (q₁ : ℝ) * (q₂ : ℝ) ^ 2 := by positivity
  have e1 : (M : ℝ) / ((q₂ : ℝ) ^ 2) - (M : ℝ) / ((q₁ : ℝ) * (q₂ : ℝ) ^ 2)
      = (M : ℝ) * ((q₁ : ℝ) - 1) / ((q₁ : ℝ) * (q₂ : ℝ) ^ 2) := by field_simp
  have e2 : (p : ℝ) * ((q₁ : ℝ) - 1) / ((q₁ : ℝ) ^ 2 * (q₂ : ℝ) ^ 2)
      = ((p : ℝ) / q₁) * ((q₁ : ℝ) - 1) / ((q₁ : ℝ) * (q₂ : ℝ) ^ 2) := by field_simp
  have hstep : ((p : ℝ) / q₁) * ((q₁ : ℝ) - 1) / ((q₁ : ℝ) * (q₂ : ℝ) ^ 2)
      - (M : ℝ) * ((q₁ : ℝ) - 1) / ((q₁ : ℝ) * (q₂ : ℝ) ^ 2) ≤ 1 := by
    rw [div_sub_div_same, div_le_one hden]
    nlinarith [mul_le_mul_of_nonneg_right (show (p : ℝ) / q₁ - (M : ℝ) ≤ 1 by linarith)
      (show (0 : ℝ) ≤ (q₁ : ℝ) - 1 by linarith), hq₂one, hq₁ge, hq₁pos]
  rw [e2]
  rw [e1] at hreal
  linarith

open scoped Classical in
/-- **Section 7 with an explicit sufficient condition.**  If the Pólya–Vinogradov bound `B` for
the character sums over the candidate set satisfies
`(g - 1) B < p (q₁ - 1) / (q₁² q₂²) - 3`, where `g = gcd (p - 1, n)`,
then the field generated by a root of `f` is not norm-Euclidean.  No hypothesis on the character
and none on the size of the candidate set is left. -/
theorem not_normEuclidean_of_charSum_of_lt {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}
    {n m p q₁ q₂ r₀ : ℕ} {a : ℕ → ℤ} {cc : ℕ → ℕ} [NeZero p] [NeZero (q₂ ^ 2)]
    (hp : p.Prime) (hn : 0 < n) (hm : 0 < m) (hmn : Nat.Coprime m n)
    (hdeg : Module.finrank ℚ K = n)
    (hroot : θ ^ n + ∑ i ∈ Finset.range n, ((a i : ℤ) : 𝓞 K) * θ ^ i = 0)
    (hc : ∀ i < n, m * (n - i) ≤ n * cc i) (hdvd : ∀ i < n, (p : ℤ) ^ cc i ∣ a i)
    (hnd : ¬ (p : ℤ) ^ (m + 1) ∣ a 0)
    (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (hne : q₁ ≠ q₂) (hq₁p : q₁ ≠ p)
    (hr₁ : ∀ r : ZMod q₁, Polynomial.eval₂ (Int.castRingHom (ZMod q₁)) r
      (Polynomial.X ^ n + ∑ i ∈ Finset.range n, Polynomial.C (a i) * Polynomial.X ^ i) ≠ 0)
    (hr₂ : ∀ r : ZMod q₂, Polynomial.eval₂ (Int.castRingHom (ZMod q₂)) r
      (Polynomial.X ^ n + ∑ i ∈ Finset.range n, Polynomial.C (a i) * Polynomial.X ^ i) ≠ 0)
    (hr₀ : ((r₀ * q₁ : ℕ) : ZMod (q₂ ^ 2)) = ((p + q₁ * q₂ : ℕ) : ZMod (q₂ ^ 2)))
    {B : ℝ} (hB : 0 ≤ B)
    (hPV : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      ‖∑ u ∈ {u ∈ Finset.range (p / q₁) |
          ¬ q₁ ∣ u ∧ ((u : ℕ) : ZMod (q₂ ^ 2)) = ((r₀ : ℕ) : ZMod (q₂ ^ 2))},
        χ ((q₁ : ZMod p) * ((u : ℕ) : ZMod p))‖ ≤ B)
    (hcond : ((Nat.gcd (p - 1) n : ℝ) - 1) * B <
      (p : ℝ) * ((q₁ : ℝ) - 1) / ((q₁ : ℝ) ^ 2 * (q₂ : ℝ) ^ 2) - 3) :
    ¬ ∀ α β : 𝓞 K, β ≠ 0 → ∃ γ ρ : 𝓞 K, α = γ * β + ρ ∧
      (Algebra.norm ℤ ρ).natAbs < (Algebra.norm ℤ β).natAbs := by
  classical
  refine not_normEuclidean_of_charSum' hp hn hm hmn hdeg hroot hc hdvd hnd hq₁ hq₂
    (fun h => hne (((Nat.prime_dvd_prime_iff_eq hq₂ hq₁).1 (by exact_mod_cast h)).symm)) hq₁p
    hr₁ hr₂ hr₀ _ (fun u hu => Finset.mem_range.1 (Finset.mem_filter.1 hu).1)
    (fun u hu => (Finset.mem_filter.1 hu).2.1)
    (fun u hu => (Finset.mem_filter.1 hu).2.2) hB hPV ?_
  exact lt_of_lt_of_le hcond (le_card_candidates hq₁ hq₂ hne r₀)

open scoped Classical in
/-- **Section 7, unconditionally.**  Let `f` satisfy the Eisenstein–Dumas condition at the prime
`p` with slope `m / n`, and suppose `f` has no root modulo two primes `q₁ ≠ q₂`, both different
from `p`.  If
`(gcd (p - 1, n) - 1) √p (1 + log p) < p / (q₁ ^ 2 q₂ ^ 2) - 2`
then the field generated by a root of `f` is not norm-Euclidean.

Every hypothesis is arithmetic: the detecting character is produced by
`exists_dirichletCharacter_pow_residues` and its character sums are bounded by the
Pólya–Vinogradov inequality
`DirichletCharacter.norm_sum_le_sqrt_mul_one_add_log`, applied to the single arithmetic
progression `u ≡ ρ (mod q₁ q₂ ^ 2)` with `ρ ≡ 1 (mod q₁)` and `ρ q₁ ≡ p + q₁ q₂ (mod q₂ ^ 2)`. -/
theorem not_normEuclidean_of_eisensteinDumas_of_gcd_lt {K : Type*} [Field K] [NumberField K]
    {θ : 𝓞 K} {n m p q₁ q₂ : ℕ} {a : ℕ → ℤ} {cc : ℕ → ℕ}
    (hp : p.Prime) (hn : 0 < n) (hm : 0 < m) (hmn : Nat.Coprime m n)
    (hdeg : Module.finrank ℚ K = n)
    (hroot : θ ^ n + ∑ i ∈ Finset.range n, ((a i : ℤ) : 𝓞 K) * θ ^ i = 0)
    (hc : ∀ i < n, m * (n - i) ≤ n * cc i) (hdvd : ∀ i < n, (p : ℤ) ^ cc i ∣ a i)
    (hnd : ¬ (p : ℤ) ^ (m + 1) ∣ a 0)
    (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (hne : q₁ ≠ q₂) (hq₁p : q₁ ≠ p) (hq₂p : q₂ ≠ p)
    (hr₁ : ∀ r : ZMod q₁, Polynomial.eval₂ (Int.castRingHom (ZMod q₁)) r
      (Polynomial.X ^ n + ∑ i ∈ Finset.range n, Polynomial.C (a i) * Polynomial.X ^ i) ≠ 0)
    (hr₂ : ∀ r : ZMod q₂, Polynomial.eval₂ (Int.castRingHom (ZMod q₂)) r
      (Polynomial.X ^ n + ∑ i ∈ Finset.range n, Polynomial.C (a i) * Polynomial.X ^ i) ≠ 0)
    (hcond : ((Nat.gcd (p - 1) n : ℝ) - 1) * (Real.sqrt p * (1 + Real.log p)) <
      (p : ℝ) / ((q₁ : ℝ) ^ 2 * (q₂ : ℝ) ^ 2) - 2) :
    ¬ ∀ α β : 𝓞 K, β ≠ 0 → ∃ γ ρ : 𝓞 K, α = γ * β + ρ ∧
      (Algebra.norm ℤ ρ).natAbs < (Algebra.norm ℤ β).natAbs := by
  classical
  have : NeZero p := ⟨hp.pos.ne'⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  have : NeZero (q₂ ^ 2) := ⟨pow_ne_zero 2 hq₂.pos.ne'⟩
  set Q : ℕ := q₂ ^ 2 with hQdef
  set Q' : ℕ := q₁ * Q with hQ'def
  have hQpos : 0 < Q := pow_pos hq₂.pos 2
  have hQ'pos : 0 < Q' := Nat.mul_pos hq₁.pos hQpos
  have hcopQ : Nat.Coprime q₁ Q :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hq₁ hq₂).2 hne)
  -- the residue `r₀` of Section 7
  obtain ⟨r₀, hr₀⟩ := exists_residue_mul_eq (p := p) hq₁ hq₂ hne
  -- combine it with `1 mod q₁`
  obtain ⟨ρ₀, hρ₁, hρ₂⟩ := Nat.chineseRemainder hcopQ 1 r₀
  set ρ : ℕ := ρ₀ % Q' with hρdef
  have hρlt : ρ < Q' := Nat.mod_lt _ hQ'pos
  have hρmod : ρ ≡ ρ₀ [MOD Q'] := Nat.mod_modEq ρ₀ Q'
  have hρq₁ : ρ ≡ 1 [MOD q₁] :=
    (hρmod.of_dvd (Dvd.intro Q rfl)).trans hρ₁
  have hρQ : ρ ≡ r₀ [MOD Q] :=
    (hρmod.of_dvd (Dvd.intro_left q₁ rfl)).trans hρ₂
  -- the candidate set
  set M : ℕ := p / q₁ with hMdef
  set S : Finset ℕ := {u ∈ Finset.range M | u ≡ ρ [MOD Q']} with hSdef
  have hSlt : ∀ u ∈ S, u < p / q₁ := fun u hu => Finset.mem_range.1 (Finset.mem_filter.1 hu).1
  have hSnd : ∀ u ∈ S, ¬ q₁ ∣ u := by
    intro u hu hdvd'
    have h1 : u ≡ ρ [MOD Q'] := (Finset.mem_filter.1 hu).2
    have h2 : u ≡ 1 [MOD q₁] := ((h1.of_dvd (Dvd.intro Q rfl)).trans hρq₁)
    have h3 : (0 : ℕ) ≡ 1 [MOD q₁] := ((Nat.modEq_zero_iff_dvd.2 hdvd').symm.trans h2)
    exact hq₁.one_lt.ne' (Nat.eq_one_of_dvd_one ((Nat.modEq_zero_iff_dvd).1 h3.symm))
  have hScong : ∀ u ∈ S, ((u : ℕ) : ZMod Q) = ((r₀ : ℕ) : ZMod Q) := by
    intro u hu
    have h1 : u ≡ ρ [MOD Q'] := (Finset.mem_filter.1 hu).2
    exact (ZMod.natCast_eq_natCast_iff _ _ _).2
      ((h1.of_dvd (Dvd.intro_left q₁ rfl)).trans hρQ)
  -- the Pólya–Vinogradov bound for the candidate set
  have hcop : Nat.Coprime (q₁ * Q') p :=
    Nat.coprime_mul_iff_left.2 ⟨(Nat.coprime_primes hq₁ hp).2 hq₁p,
      Nat.coprime_mul_iff_left.2 ⟨(Nat.coprime_primes hq₁ hp).2 hq₁p,
        Nat.Coprime.pow_left _ ((Nat.coprime_primes hq₂ hp).2 hq₂p)⟩⟩
  have hb : ((q₁ * Q' : ℕ) : ZMod p) ≠ 0 := ((ZMod.isUnit_iff_coprime _ p).2 hcop).ne_zero
  have hPV : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      ‖∑ u ∈ S, χ ((q₁ : ZMod p) * ((u : ℕ) : ZMod p))‖
        ≤ Real.sqrt p * (1 + Real.log p) := by
    intro χ hχ
    have hkey : ∀ t : ℕ, (q₁ : ZMod p) * ((ρ + Q' * t : ℕ) : ZMod p)
        = ((q₁ * Q' : ℕ) : ZMod p) *
          (((q₁ * ρ : ℕ) : ZMod p) / ((q₁ * Q' : ℕ) : ZMod p) + ((t : ℕ) : ZMod p)) := by
      intro t
      have h1 : ((q₁ * Q' : ℕ) : ZMod p) * (((q₁ * ρ : ℕ) : ZMod p) / ((q₁ * Q' : ℕ) : ZMod p))
          = ((q₁ * ρ : ℕ) : ZMod p) := by field_simp
      rw [mul_add, h1]
      push_cast
      ring
    calc ‖∑ u ∈ S, χ ((q₁ : ZMod p) * ((u : ℕ) : ZMod p))‖
        = ‖∑ t ∈ Finset.range ((M - ρ + Q' - 1) / Q'),
            χ ((q₁ : ZMod p) * ((ρ + Q' * t : ℕ) : ZMod p))‖ := by
          rw [hSdef, Nat.sum_filter_range_modEq hQ'pos hρlt]
      _ = ‖χ ((q₁ * Q' : ℕ) : ZMod p) * ∑ t ∈ Finset.range ((M - ρ + Q' - 1) / Q'),
            χ (((q₁ * ρ : ℕ) : ZMod p) / ((q₁ * Q' : ℕ) : ZMod p) + ((t : ℕ) : ZMod p))‖ := by
          rw [Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun t _ => by rw [hkey t, map_mul]
      _ ≤ 1 * (Real.sqrt p * (1 + Real.log p)) := by
          rw [norm_mul]
          exact mul_le_mul (DirichletCharacter.norm_le_one _ _)
            (DirichletCharacter.norm_sum_le_sqrt_mul_one_add_log hp χ hχ _ _)
            (norm_nonneg _) zero_le_one
      _ = Real.sqrt p * (1 + Real.log p) := one_mul _
  -- the count
  have hq₁R : (0 : ℝ) < q₁ := by exact_mod_cast hq₁.pos
  have hq₂R : (0 : ℝ) < q₂ := by exact_mod_cast hq₂.pos
  have hcount : (p : ℝ) / ((q₁ : ℝ) ^ 2 * (q₂ : ℝ) ^ 2) - 2 ≤ #S := by
    have h1 := Nat.le_card_range_filter_modEq (M := M) hQ'pos ρ
    have h1R : (M : ℝ) / ((q₁ : ℝ) * (q₂ : ℝ) ^ 2) - 1 ≤ #S := by
      have h2 := (Rat.cast_le (K := ℝ)).2 h1
      push_cast at h2
      have hQ'R : ((Q' : ℕ) : ℝ) = (q₁ : ℝ) * (q₂ : ℝ) ^ 2 := by
        rw [hQ'def, hQdef]
        push_cast
        ring
      rw [hQ'R] at h2
      rw [hSdef]
      exact h2
    have hM : (p : ℝ) / q₁ - 1 ≤ (M : ℝ) := by
      have hdm : q₁ * M + p % q₁ = p := by rw [hMdef]; exact Nat.div_add_mod p q₁
      have h2 : (q₁ : ℝ) * (M : ℝ) + ((p % q₁ : ℕ) : ℝ) = (p : ℝ) := by exact_mod_cast hdm
      have h3 : ((p % q₁ : ℕ) : ℝ) < (q₁ : ℝ) := by exact_mod_cast Nat.mod_lt _ hq₁.pos
      rw [sub_le_iff_le_add, div_le_iff₀ hq₁R]
      nlinarith
    have hd : (0 : ℝ) < (q₁ : ℝ) * (q₂ : ℝ) ^ 2 := by positivity
    have h4 : ((p : ℝ) / q₁ - 1) / ((q₁ : ℝ) * (q₂ : ℝ) ^ 2)
        ≤ (M : ℝ) / ((q₁ : ℝ) * (q₂ : ℝ) ^ 2) := by gcongr
    have h5 : (p : ℝ) / ((q₁ : ℝ) ^ 2 * (q₂ : ℝ) ^ 2) - 1 / ((q₁ : ℝ) * (q₂ : ℝ) ^ 2)
        = ((p : ℝ) / q₁ - 1) / ((q₁ : ℝ) * (q₂ : ℝ) ^ 2) := by
      field_simp
    have h6 : 1 / ((q₁ : ℝ) * (q₂ : ℝ) ^ 2) ≤ 1 := by
      rw [div_le_one hd]
      have h7 : (1 : ℝ) ≤ (q₁ : ℝ) := by exact_mod_cast hq₁.one_lt.le
      have h8 : (1 : ℝ) ≤ (q₂ : ℝ) := by exact_mod_cast hq₂.one_lt.le
      nlinarith
    linarith
  -- apply Section 7
  refine not_normEuclidean_of_charSum' hp hn hm hmn hdeg hroot hc hdvd hnd hq₁ hq₂
    (fun h => hne (((Nat.prime_dvd_prime_iff_eq hq₂ hq₁).1 (by exact_mod_cast h)).symm)) hq₁p
    hr₁ hr₂ hr₀ S hSlt hSnd hScong (by positivity) hPV (lt_of_lt_of_le hcond hcount)



end NumberField
