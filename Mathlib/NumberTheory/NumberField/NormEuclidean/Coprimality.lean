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
# Weakening the coprimality condition

The character-sum argument of `Mathlib.NumberTheory.NumberField.NormEuclidean.Character` needs a
lower bound for the number of candidates
`S = {u < p / q₁ : q₁ ∤ u, u ≡ r₀ (mod q₂ ^ 2)}`,
and needs to know that every candidate `u` has `q₁ u` invertible modulo `p`.  Both are proved
here, giving the argument a completely explicit sufficient condition.

The count is elementary: the residue class of `r₀` modulo `q₂ ^ 2` contributes at least
`M / q₂ ^ 2 - 1` integers below `M`, and the multiples of `q₁` inside it form a single class
modulo `q₁ q₂ ^ 2` (the moduli are coprime) and so contribute at most `M / (q₁ q₂ ^ 2) + 1`.
With `M = p / q₁` this gives `#S ≥ p (q₁ - 1) / (q₁ ^ 2 q₂ ^ 2) - 3`.

Taking instead for `S` a *single* arithmetic progression `u ≡ ρ (mod q₁ q₂ ^ 2)`, with `ρ ≡ 1`
modulo `q₁`, makes the condition `q₁ ∤ u` automatic and lets the Pólya–Vinogradov inequality be
applied directly, giving the theorem with no analytic hypothesis at all:
`NumberField.not_normEuclidean_of_eisensteinDumas_of_gcd_lt`.

## Main results

* `Nat.sum_filter_range_modEq`: a sum over a residue class below `M`, reindexed by an initial
  segment.
* `NumberField.le_card_filter_range_div_not_dvd`: the lower bound
  `p (q₁ - 1) / (q₁ ^ 2 q₂ ^ 2) - 3`.
* `NumberField.not_normEuclidean_of_charSum_bound_lt`: Section 7, with the size condition on the
  character-sum bound `B` made explicit.
* `NumberField.not_normEuclidean_of_eisensteinDumas_of_gcd_lt`: Section 7 unconditionally, with
  the Pólya–Vinogradov inequality supplied.
* `NumberField.eventually_gcd_condition`, `NumberField.eventually_gcd_condition_gcd`: the
  explicit condition of that theorem holds for all large `p`, so it is not vacuous.
## References

This is the final section of [Hibbler, McGown, Treviño, *Polynomial densities and Heilbronn's
criterion*][hibbler_mcgown_trevino2025], with the two congruence conditions on the auxiliary
integer combined into a single arithmetic progression, so that only characters modulo the prime
`p` occur and the inequality of [Pólya][polya1918] and [Vinogradov][vinogradov1918] applies
without a reduction to primitive characters.
-/

public section

open Finset

namespace Nat

/-- Reindexing a sum over a residue class below `M` as a sum over an initial segment.  The
underlying description of the class, `Nat.filter_range_modEq_eq_image`, is in
`Mathlib/Data/Int/CardIntervalMod.lean`; only this consequence needs big operators. -/
theorem sum_filter_range_modEq {M Q r : ℕ} (hQ : 0 < Q) (hr : r < Q) {A : Type*}
    [AddCommMonoid A] (f : ℕ → A) :
    ∑ u ∈ {u ∈ Finset.range M | u ≡ r [MOD Q]}, f u
      = ∑ t ∈ Finset.range ((M - r + Q - 1) / Q), f (r + Q * t) := by
  classical
  rw [filter_range_modEq_eq_image hQ hr,
    Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hQ (add_left_cancel h))]

end Nat

namespace NumberField

/-- The candidate set, with the congruence rewritten as a `Nat.ModEq`. -/
theorem filter_range_natCast_eq {M Q : ℕ} (q v : ℕ) :
    {u ∈ Finset.range M | ¬ q ∣ u ∧ ((u : ℕ) : ZMod Q) = ((v : ℕ) : ZMod Q)}
      = {u ∈ Finset.range M | ¬ q ∣ u ∧ u ≡ v [MOD Q]} := by
  refine Finset.filter_congr fun u _ => ?_
  simp only [ZMod.natCast_eq_natCast_iff]

/-- **Lower bound for the number of candidates.**  At least
`p (q₁ - 1) / (q₁ ^ 2 q₂ ^ 2) - 3` of the `u < p / q₁` are prime to `q₁` and congruent to `v`
modulo `q₂ ^ 2`. -/
theorem le_card_filter_range_div_not_dvd {p q₁ q₂ : ℕ} (hq₁ : q₁.Prime) (hq₂ : q₂.Prime)
    (hne : q₁ ≠ q₂) (v : ℕ) :
    (p : ℝ) * ((q₁ : ℝ) - 1) / ((q₁ : ℝ) ^ 2 * (q₂ : ℝ) ^ 2) - 3 ≤
      #{u ∈ Finset.range (p / q₁) |
        ¬ q₁ ∣ u ∧ ((u : ℕ) : ZMod (q₂ ^ 2)) = ((v : ℕ) : ZMod (q₂ ^ 2))} := by
  rw [filter_range_natCast_eq]
  set M := p / q₁ with hM
  have hq₁pos : (0 : ℝ) < q₁ := by exact_mod_cast hq₁.pos
  have hq₂pos : (0 : ℝ) < q₂ := by exact_mod_cast hq₂.pos
  have hcop : Nat.Coprime (q₂ ^ 2) q₁ :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes hq₂ hq₁).2 (Ne.symm hne))
  have hQ : 0 < q₂ ^ 2 := pow_pos hq₂.pos 2
  have hbase := Nat.le_card_range_filter_modEq_not_dvd (M := M) hQ hq₁.pos hcop v
  have hreal : (M : ℝ) / ((q₂ : ℝ) ^ 2) - (M : ℝ) / ((q₁ : ℝ) * (q₂ : ℝ) ^ 2) - 2 ≤
      #{u ∈ Finset.range M | ¬ q₁ ∣ u ∧ u ≡ v [MOD q₂ ^ 2]} := by
    have h := (Rat.cast_le (K := ℝ)).2 hbase
    push_cast at h
    linarith
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
theorem not_normEuclidean_of_charSum_bound_lt {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}
    {n m p q₁ q₂ r₀ : ℕ} {a : ℕ → ℤ} {cc : ℕ → ℕ}
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
  refine not_normEuclidean_of_forall_charSum hp hn hm hmn hdeg hroot hc hdvd hnd hq₁ hq₂
    (fun h => hne (((Nat.prime_dvd_prime_iff_eq hq₂ hq₁).1 (by exact_mod_cast h)).symm)) hq₁p
    hr₁ hr₂ hr₀ _ (fun u hu => Finset.mem_range.1 (Finset.mem_filter.1 hu).1)
    (fun u hu => (Finset.mem_filter.1 hu).2.1)
    (fun u hu => (Finset.mem_filter.1 hu).2.2) hB hPV ?_
  exact lt_of_lt_of_le hcond (le_card_filter_range_div_not_dvd hq₁ hq₂ hne r₀)

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
  refine not_normEuclidean_of_forall_charSum hp hn hm hmn hdeg hroot hc hdvd hnd hq₁ hq₂
    (fun h => hne (((Nat.prime_dvd_prime_iff_eq hq₂ hq₁).1 (by exact_mod_cast h)).symm)) hq₁p
    hr₁ hr₂ hr₀ S hSlt hSnd hScong (by positivity) hPV (lt_of_lt_of_le hcond hcount)

/-- **The explicit condition of Section 7 is satisfiable.**  For fixed `g` and fixed auxiliary
primes `q₁, q₂`, the inequality required by
`NumberField.not_normEuclidean_of_eisensteinDumas_of_gcd_lt` holds for every sufficiently large
`p`, because `√p (1 + log p) = O(p ^ (3/4))`. -/
theorem eventually_gcd_condition (g q₁ q₂ : ℕ) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) :
    ∀ᶠ p : ℕ in Filter.atTop,
      ((g : ℝ) - 1) * (Real.sqrt p * (1 + Real.log p)) <
        (p : ℝ) / ((q₁ : ℝ) ^ 2 * (q₂ : ℝ) ^ 2) - 2 := by
  set D : ℕ := q₁ ^ 2 * q₂ ^ 2 with hDdef
  have hD1 : 1 ≤ D := Nat.one_le_iff_ne_zero.2 (by positivity)
  filter_upwards [Filter.eventually_ge_atTop ((8 * D * g + 4 * D + 1) ^ 4)] with p hp
  set T : ℝ := 8 * (D : ℝ) * (g : ℝ) + 4 * (D : ℝ) + 1 with hTdef
  have hDR : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
  have hgR : (0 : ℝ) ≤ (g : ℝ) := by positivity
  have hT1 : 1 ≤ T := by rw [hTdef]; nlinarith
  have hpR : (0 : ℝ) < p := by
    have : 0 < p := lt_of_lt_of_le (by positivity) hp
    exact_mod_cast this
  set t : ℝ := Real.sqrt (Real.sqrt p) with htdef
  have ht0 : 0 < t := Real.sqrt_pos.2 (Real.sqrt_pos.2 hpR)
  -- `t = p ^ (1/4)`, so `t ^ 4 = p` and `√p = t ^ 2`
  have hsq : Real.sqrt p = t ^ 2 := by
    rw [htdef, Real.sq_sqrt (Real.sqrt_nonneg _)]
  have ht4 : t ^ 4 = (p : ℝ) := by
    have h1 : t ^ 4 = (t ^ 2) ^ 2 := by ring
    rw [h1, ← hsq, Real.sq_sqrt hpR.le]
  -- `t ≥ T`
  have htT : T ≤ t := by
    have hTp : T ^ 4 ≤ (p : ℝ) := by
      have h1 : ((8 * D * g + 4 * D + 1 : ℕ) : ℝ) = T := by rw [hTdef]; push_cast; ring
      have h2 : (((8 * D * g + 4 * D + 1) ^ 4 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      rw [Nat.cast_pow, h1] at h2
      exact h2
    have h3 : T ^ 2 ≤ Real.sqrt p := by
      refine Real.le_sqrt_of_sq_le ?_
      calc (T ^ 2) ^ 2 = T ^ 4 := by ring
        _ ≤ (p : ℝ) := hTp
    rw [htdef]
    exact Real.le_sqrt_of_sq_le h3
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
    have h : 1 ≤ p := le_trans (Nat.one_le_pow _ _ (by positivity)) hp
    exact_mod_cast h
  have hlogpos : 0 ≤ Real.log p := Real.log_nonneg hp1
  have ht1 : (1 : ℝ) ≤ t := le_trans hT1 htT
  have ht3 : (1 : ℝ) ≤ t ^ 3 := by nlinarith
  -- the logarithm
  have hlog : 1 + Real.log p ≤ 4 * t := by
    have h5 := Real.log_le_four_mul_sqrt_sqrt_sub_one hpR
    rw [← htdef] at h5
    linarith
  -- put it together
  have hden : (0 : ℝ) < (q₁ : ℝ) ^ 2 * (q₂ : ℝ) ^ 2 := by
    have h1 : (0 : ℝ) < q₁ := by exact_mod_cast hq₁
    have h2 : (0 : ℝ) < q₂ := by exact_mod_cast hq₂
    positivity
  have hDeq : (q₁ : ℝ) ^ 2 * (q₂ : ℝ) ^ 2 = (D : ℝ) := by rw [hDdef]; push_cast; ring
  have hpd : (p : ℝ) / (D : ℝ) = t ^ 4 * ((D : ℝ))⁻¹ := by rw [ht4, div_eq_mul_inv]
  rw [hDeq, hsq, hpd]
  have hub : ((g : ℝ) - 1) * (t ^ 2 * (1 + Real.log p)) ≤ 4 * (g : ℝ) * t ^ 3 := by
    have h1 : t ^ 2 * (1 + Real.log p) ≤ t ^ 2 * (4 * t) :=
      mul_le_mul_of_nonneg_left hlog (sq_nonneg t)
    rcases le_or_gt 1 (g : ℝ) with hg1 | hg1
    · nlinarith
    · have h3 : 0 ≤ t ^ 2 * (1 + Real.log p) :=
        mul_nonneg (sq_nonneg t) (by linarith)
      nlinarith
  have hkey : 4 * (g : ℝ) * t ^ 3 + 2 < t ^ 4 * ((D : ℝ))⁻¹ := by
    rw [lt_mul_inv_iff₀ (by linarith)]
    have h6 : t ^ 3 * (8 * (D : ℝ) * (g : ℝ) + 4 * (D : ℝ) + 1) ≤ t ^ 4 := by
      have := mul_le_mul_of_nonneg_left htT (pow_nonneg ht0.le 3)
      rw [hTdef] at this
      nlinarith [this]
    have h7 : (D : ℝ) ≤ (D : ℝ) * t ^ 3 := by nlinarith
    have h8 : (0 : ℝ) ≤ (D : ℝ) * (g : ℝ) * t ^ 3 := by positivity
    nlinarith [h6, h7, h8]
  linarith

/-- **The condition of Section 7 is satisfiable for the relevant `g`.**  The `g` in
`not_normEuclidean_of_eisensteinDumas_of_gcd_lt` is `gcd (p - 1, n)`, which depends on `p`; since
it is at most `n` and the left-hand side is increasing in it, the condition still holds for every
sufficiently large `p`, with `n` and the auxiliary primes fixed. -/
theorem eventually_gcd_condition_gcd (n q₁ q₂ : ℕ) (hn : 0 < n) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) :
    ∀ᶠ p : ℕ in Filter.atTop,
      ((Nat.gcd (p - 1) n : ℝ) - 1) * (Real.sqrt p * (1 + Real.log p)) <
        (p : ℝ) / ((q₁ : ℝ) ^ 2 * (q₂ : ℝ) ^ 2) - 2 := by
  filter_upwards [eventually_gcd_condition n q₁ q₂ hq₁ hq₂, Filter.eventually_ge_atTop 1]
    with p hpc hp1
  have hg : (Nat.gcd (p - 1) n : ℝ) ≤ (n : ℝ) := by
    have h : Nat.gcd (p - 1) n ≤ n := Nat.gcd_le_right _ hn
    exact_mod_cast h
  have hnn : (0 : ℝ) ≤ Real.sqrt p * (1 + Real.log p) := by
    have h1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
    have h2 : 0 ≤ Real.log p := Real.log_nonneg h1
    positivity
  refine lt_of_le_of_lt ?_ hpc
  exact mul_le_mul_of_nonneg_right (by linarith) hnn

end NumberField
