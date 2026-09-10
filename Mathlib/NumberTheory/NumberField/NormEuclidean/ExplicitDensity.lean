/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.NormEuclidean.Coprimality
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Explicit density bounds

Specialising the master theorem
`NumberField.tendsto_density_atLeastTwo` to concrete sets `Q` of auxiliary primes gives explicit
lower densities for the Eisenstein–Dumas polynomials whose fields are provably not
norm-Euclidean.

* `Q = {2, 3}` gives `2 / 27`; this is `NumberField.tendsto_density_two_three`.
* `Q = {2, 3, 5}` gives `136 / 675 = 0.20148…`
  (`NumberField.eventually_le_density_two_three_five`): the local densities are
  `C_2 = 1/4`, `C_3 = 8/27` and `C_5 ≥ 8/25`, and the probability that at least two of three
  independent events occur is increasing in each probability.
* `Q =` all primes at most `Y < p` gives `1 - (1 + π Y)(3/4) ^ π Y`
  (`NumberField.eventually_le_density_primesLE`); for `Y = ⌊p ^ (1/4)⌋` this tends to `1` as
  `p → ∞`
  (`NumberField.tendsto_one_add_primeCounting_mul_pow_atTop_nhds_zero`).  The condition of
  Heilbronn's criterion holds for every pair of primes in that set because `q₁ ^ 2 q₂ ^ 2 ≤ p`
  (`NumberField.exists_rep_of_mem_primesLE`).

The last section restates Section 7 in the indexing used by the density theorems, so that the two
halves can be combined:
`NumberField.not_normEuclidean_of_eisensteinDumas_fin_of_gcd_lt`.
## References

The bounds `2 / 27` and `1 - ε(p)` are those of [Hibbler, McGown, Treviño, *Polynomial densities
and Heilbronn's criterion*][hibbler_mcgown_trevino2025]; the intermediate bounds, of which
`136 / 675` is an instance, come from the master theorem that interpolates between them.
-/

public section

open Finset Polynomial

namespace NumberField

/-! ### Corollary: three auxiliary primes -/

/-- The probability that at least two of three independent events occur, expanded. -/
theorem sum_atLeastTwo_three (c : ℕ → ℝ) :
    ∑ U ∈ {U ∈ ({2, 3, 5} : Finset ℕ).powerset | 2 ≤ #U},
        (∏ q ∈ U, c q) * ∏ q ∈ ({2, 3, 5} : Finset ℕ) \ U, (1 - c q)
      = c 2 * c 3 * (1 - c 5) + c 2 * c 5 * (1 - c 3) + c 3 * c 5 * (1 - c 2)
        + c 2 * c 3 * c 5 := by
  have hset : {U ∈ ({2, 3, 5} : Finset ℕ).powerset | 2 ≤ #U}
      = ({{2, 3}, {2, 5}, {3, 5}, {2, 3, 5}} : Finset (Finset ℕ)) := by decide
  have h1 : ({2, 3, 5} : Finset ℕ) \ {2, 3} = {5} := by decide
  have h2 : ({2, 3, 5} : Finset ℕ) \ {2, 5} = {3} := by decide
  have h3 : ({2, 3, 5} : Finset ℕ) \ {3, 5} = {2} := by decide
  have h4 : ({2, 3, 5} : Finset ℕ) \ {2, 3, 5} = ∅ := by decide
  rw [hset, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, h1, h2, h3, h4]
  simp only [Finset.prod_insert (show (2 : ℕ) ∉ ({3, 5} : Finset ℕ) by decide),
    Finset.prod_pair (show (2 : ℕ) ≠ 3 by decide),
    Finset.prod_pair (show (2 : ℕ) ≠ 5 by decide),
    Finset.prod_pair (show (3 : ℕ) ≠ 5 by decide),
    Finset.prod_singleton, Finset.prod_empty]
  ring

/-- With `C_2 = 1/4`, `C_3 = 8/27` and `C_5 ≥ 8/25`, at least two of the three events occur with
probability at least `136 / 675`. -/
theorem le_sum_atLeastTwo_three {c : ℕ → ℝ} (h2 : c 2 = 1 / 4) (h3 : c 3 = 8 / 27)
    (h5 : 8 / 25 ≤ c 5) :
    136 / 675 ≤ ∑ U ∈ {U ∈ ({2, 3, 5} : Finset ℕ).powerset | 2 ≤ #U},
        (∏ q ∈ U, c q) * ∏ q ∈ ({2, 3, 5} : Finset ℕ) \ U, (1 - c q) := by
  rw [sum_atLeastTwo_three, h2, h3]
  linarith

/-- The local density at `2` is exactly `1 / 4`, in the form used by the master theorem. -/
theorem card_no_root_div_two_eq {n : ℕ} (hn : 2 ≤ n) :
    (Nat.card {y : Fin n → ZMod 2 //
        ∀ r : ZMod 2, ¬ (X ^ n + ∑ i : Fin n, C (y i) * X ^ (i : ℕ)).IsRoot r} : ℝ)
      / ((2 : ℕ) : ℝ) ^ n = 1 / 4 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact card_no_root_zmod_two_div hn

/-- The local density at `3` is exactly `8 / 27`, in the form used by the master theorem. -/
theorem card_no_root_div_three_eq {n : ℕ} (hn : 3 ≤ n) :
    (Nat.card {y : Fin n → ZMod 3 //
        ∀ r : ZMod 3, ¬ (X ^ n + ∑ i : Fin n, C (y i) * X ^ (i : ℕ)).IsRoot r} : ℝ)
      / ((3 : ℕ) : ℝ) ^ n = 8 / 27 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact card_no_root_zmod_three_div hn

/-- The local density at `5` is at least `8 / 25`. -/
theorem le_card_no_root_div_five {n : ℕ} (hn : 2 ≤ n) :
    8 / 25 ≤ (Nat.card {y : Fin n → ZMod 5 //
        ∀ r : ZMod 5, ¬ (X ^ n + ∑ i : Fin n, C (y i) * X ^ (i : ℕ)).IsRoot r} : ℝ)
      / ((5 : ℕ) : ℝ) ^ n := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcard : Fintype.card (ZMod 5) = 5 := ZMod.card 5
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h := (Polynomial.card_no_root_univ_div_bounds (F := ZMod 5) hn).1
  rw [hcard] at h
  norm_num at h ⊢
  linarith


open scoped Classical in
/-- **Corollary 1.7.**  For `n ≥ 3` and a prime `p ∉ {2, 3, 5}`, the proportion of the
Eisenstein–Dumas family attached to `p` whose polynomial has no root modulo at least two of
`2, 3, 5` is eventually at least `136 / 675 = 0.20148…`.

Each such polynomial generates a field that is not norm-Euclidean, by
`not_normEuclidean_of_eisensteinDumas_fin` applied to two of those primes, whose pair condition
holds for `p ≥ 225` by `exists_eq_add_mul_of_sq_mul_sq_le`. -/
theorem eventually_le_density_two_three_five {n : ℕ} (hn : 3 ≤ n) {p : ℕ} {c : Fin n → ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop,
      136 / 675 - ε ≤
        (#{a ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ) |
            ((∀ i, (p : ℤ) ^ c i ∣ a i) ∧
              ¬ (p : ℤ) ^ (c ⟨0, by omega⟩ + 1) ∣ a ⟨0, by omega⟩) ∧
            2 ≤ #{q ∈ ({2, 3, 5} : Finset ℕ) | ∀ r : ZMod q,
              ¬ (X ^ n + ∑ i : Fin n, C (((a i : ℤ) : ZMod q)) * X ^ (i : ℕ)).IsRoot r}} : ℝ) /
        (#{a ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ) |
            (∀ i, (p : ℤ) ^ c i ∣ a i) ∧
              ¬ (p : ℤ) ^ (c ⟨0, by omega⟩ + 1) ∣ a ⟨0, by omega⟩} : ℝ) := by
  have hQ : ∀ q ∈ ({2, 3, 5} : Finset ℕ), q.Prime := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_five
  have hpQ : p ∉ ({2, 3, 5} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hlim := tendsto_density_atLeastTwo (n := n) (c := c) (by omega) hp hQ hpQ
  refine hlim.eventually_const_le ?_
  rw [sum_atLeastTwo_three (fun q => (Nat.card {y : Fin n → ZMod q //
      ∀ r : ZMod q, ¬ (X ^ n + ∑ i : Fin n, C (y i) * X ^ (i : ℕ)).IsRoot r} : ℝ) / (q : ℝ) ^ n),
    card_no_root_div_two_eq (show 2 ≤ n by omega), card_no_root_div_three_eq hn]
  linarith [le_card_no_root_div_five (n := n) (show 2 ≤ n by omega)]

/-! ### Corollary: all primes up to `p ^ (1/4)` -/

/-- Any two distinct primes at most `⌊p ^ (1/4)⌋` admit the representation `p = u q₁ + v q₂` with
`q₁ ∤ u` and `q₂ ∤ v` required by Heilbronn's criterion, since `q₁ ^ 2 q₂ ^ 2 ≤ p`. -/
theorem exists_rep_of_mem_primesLE {p q₁ q₂ : ℕ}
    (hq₁ : q₁ ∈ Nat.primesLE (Nat.sqrt (Nat.sqrt p)))
    (hq₂ : q₂ ∈ Nat.primesLE (Nat.sqrt (Nat.sqrt p))) (hne : q₁ ≠ q₂) :
    ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ p = u * q₁ + v * q₂ ∧ ¬ q₁ ∣ u ∧ ¬ q₂ ∣ v := by
  obtain ⟨h₁le, h₁p⟩ := Nat.mem_primesLE.1 hq₁
  obtain ⟨h₂le, h₂p⟩ := Nat.mem_primesLE.1 hq₂
  refine exists_eq_add_mul_of_sq_mul_sq_le h₁p.one_lt h₂p.one_lt
    ((Nat.coprime_primes h₁p h₂p).2 hne) ?_
  have h2 : Nat.sqrt (Nat.sqrt p) ^ 2 ≤ Nat.sqrt p := Nat.sqrt_le' _
  calc q₁ ^ 2 * q₂ ^ 2 ≤ Nat.sqrt (Nat.sqrt p) ^ 2 * Nat.sqrt (Nat.sqrt p) ^ 2 :=
        Nat.mul_le_mul (Nat.pow_le_pow_left h₁le 2) (Nat.pow_le_pow_left h₂le 2)
    _ ≤ Nat.sqrt p * Nat.sqrt p := Nat.mul_le_mul h2 h2
    _ = Nat.sqrt p ^ 2 := (pow_two _).symm
    _ ≤ p := Nat.sqrt_le' p

open scoped Classical in
/-- **Corollary 1.8.**  Let `Q` be the set of all primes at most `⌊p ^ (1/4)⌋` and let
`t = π (⌊p ^ (1/4)⌋)`.  The proportion of the Eisenstein–Dumas family attached to `p` whose
polynomial has no root modulo at least two primes of `Q` is eventually at least
`1 - (1 + t) (3/4) ^ t`.

Every pair of primes in `Q` satisfies the condition of Heilbronn's criterion by
`exists_rep_of_mem_primesLE`, so every polynomial counted in the numerator generates a field that
is not norm-Euclidean; and `1 - (1 + t) (3/4) ^ t → 1` as `p → ∞` by
`tendsto_one_add_primeCounting_mul_pow_atTop_nhds_zero`. -/
theorem eventually_le_density_primesLE {n : ℕ} (hn : 2 ≤ n) {p : ℕ} {c : Fin n → ℕ}
    (hp : p.Prime) (Y : ℕ) (hY : Y < p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop,
      1 - (1 + (Nat.primeCounting Y : ℝ)) * (3 / 4 : ℝ) ^ Nat.primeCounting Y - ε ≤
        (#{a ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ) |
            ((∀ i, (p : ℤ) ^ c i ∣ a i) ∧
              ¬ (p : ℤ) ^ (c ⟨0, by omega⟩ + 1) ∣ a ⟨0, by omega⟩) ∧
            2 ≤ #{q ∈ Nat.primesLE Y | ∀ r : ZMod q,
              ¬ (X ^ n + ∑ i : Fin n, C (((a i : ℤ) : ZMod q)) * X ^ (i : ℕ)).IsRoot r}} : ℝ) /
        (#{a ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ) |
            (∀ i, (p : ℤ) ^ c i ∣ a i) ∧
              ¬ (p : ℤ) ^ (c ⟨0, by omega⟩ + 1) ∣ a ⟨0, by omega⟩} : ℝ) := by
  have hQ : ∀ q ∈ Nat.primesLE Y, q.Prime := fun q hq => (Nat.mem_primesLE.1 hq).2
  have hpQ : p ∉ Nat.primesLE Y := by
    intro h
    have h1 : p ≤ Y := (Nat.mem_primesLE.1 h).1
    omega
  have h := eventually_le_density_atLeastTwo (n := n) (c := c) hn hp hQ hpQ hε
  rwa [Nat.primesLE_card_eq_primeCounting] at h

open scoped Classical in
/-- **Corollary 1.8 for the fourth root.**  Taking `Y = ⌊p ^ (1 / 4)⌋`, every pair of primes of
`Q` satisfies the condition of Heilbronn's criterion (`exists_rep_of_mem_primesLE`), so the
density bound applies with `t = π (⌊p ^ (1 / 4)⌋)`. -/
theorem eventually_le_density_primesLE_sqrt_sqrt {n : ℕ} (hn : 2 ≤ n) {p : ℕ} {c : Fin n → ℕ}
    (hp : p.Prime) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop,
      1 - (1 + (Nat.primeCounting (Nat.sqrt (Nat.sqrt p)) : ℝ)) *
          (3 / 4 : ℝ) ^ Nat.primeCounting (Nat.sqrt (Nat.sqrt p)) - ε ≤
        (#{a ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ) |
            ((∀ i, (p : ℤ) ^ c i ∣ a i) ∧
              ¬ (p : ℤ) ^ (c ⟨0, by omega⟩ + 1) ∣ a ⟨0, by omega⟩) ∧
            2 ≤ #{q ∈ Nat.primesLE (Nat.sqrt (Nat.sqrt p)) | ∀ r : ZMod q,
              ¬ (X ^ n + ∑ i : Fin n, C (((a i : ℤ) : ZMod q)) * X ^ (i : ℕ)).IsRoot r}} : ℝ) /
        (#{a ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ) |
            (∀ i, (p : ℤ) ^ c i ∣ a i) ∧
              ¬ (p : ℤ) ^ (c ⟨0, by omega⟩ + 1) ∣ a ⟨0, by omega⟩} : ℝ) := by
  refine eventually_le_density_primesLE hn hp _ ?_ hε
  have h2 : Nat.sqrt (Nat.sqrt p) ≤ Nat.sqrt p := Nat.sqrt_le_self _
  have h3 : Nat.sqrt p < p := Nat.sqrt_lt_self hp.one_lt
  omega

/-- The error term of Corollary 1.8, `(1 + π (⌊p ^ (1/4)⌋)) (3/4) ^ π (⌊p ^ (1/4)⌋)`, tends to
`0` as `p → ∞`:  the number of primes below `⌊p ^ (1/4)⌋` tends to infinity, and
`(1 + t) (3/4) ^ t → 0`. -/
theorem tendsto_one_add_primeCounting_mul_pow_atTop_nhds_zero :
    Filter.Tendsto (fun p : ℕ => (1 + (Nat.primeCounting (Nat.sqrt (Nat.sqrt p)) : ℝ)) *
        (3 / 4 : ℝ) ^ Nat.primeCounting (Nat.sqrt (Nat.sqrt p)))
      Filter.atTop (nhds 0) := by
  have hsqrt : Filter.Tendsto (fun p : ℕ => Nat.sqrt (Nat.sqrt p)) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_atTop.2 fun k => ⟨k ^ 4, fun p hp => ?_⟩
    rw [Nat.le_sqrt, Nat.le_sqrt]
    calc k * k * (k * k) = k ^ 4 := by ring
      _ ≤ p := hp
  have hcomp : Filter.Tendsto (fun p : ℕ => Nat.primeCounting (Nat.sqrt (Nat.sqrt p)))
      Filter.atTop Filter.atTop := Nat.tendsto_primeCounting.comp hsqrt
  have hbase : Filter.Tendsto (fun t : ℕ => (1 + (t : ℝ)) * (3 / 4 : ℝ) ^ t)
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun t : ℕ => (3 / 4 : ℝ) ^ t) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h2 : Filter.Tendsto (fun t : ℕ => (t : ℝ) * (3 / 4 : ℝ) ^ t) Filter.atTop (nhds 0) :=
      tendsto_self_mul_const_pow_of_lt_one (by norm_num) (by norm_num)
    have h3 := h1.add h2
    rw [zero_add] at h3
    exact h3.congr fun t => by ring
  exact hbase.comp hcomp

/-! ### The Fin-indexed form of Section 7 -/

/-- **Section 7, in the indexing of the density theorems.**  The same statement as
`not_normEuclidean_of_eisensteinDumas_of_gcd_lt`, with the coefficients indexed by `Fin n` and
the rootlessness expressed by `Polynomial.IsRoot`, so that it applies directly to the tuples
counted by the density theorems.  No hypothesis on `gcd (p - 1, n)` beyond the explicit size
condition. -/
theorem not_normEuclidean_of_eisensteinDumas_fin_of_gcd_lt {K : Type*} [Field K] [NumberField K]
    {θ : 𝓞 K} {n m p q₁ q₂ : ℕ} {a : Fin n → ℤ} {c : Fin n → ℕ} (hn : 0 < n)
    (hp : p.Prime) (hm : 0 < m) (hmn : Nat.Coprime m n)
    (hdeg : Module.finrank ℚ K = n)
    (hroot : θ ^ n + ∑ i : Fin n, ((a i : ℤ) : 𝓞 K) * θ ^ (i : ℕ) = 0)
    (hc : ∀ i : Fin n, m * (n - (i : ℕ)) ≤ n * c i)
    (hdvd : ∀ i : Fin n, (p : ℤ) ^ c i ∣ a i)
    (hnd : ¬ (p : ℤ) ^ (m + 1) ∣ a ⟨0, hn⟩)
    (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (hne : q₁ ≠ q₂) (hq₁p : q₁ ≠ p) (hq₂p : q₂ ≠ p)
    (hr₁ : ∀ r : ZMod q₁,
      ¬ (X ^ n + ∑ i : Fin n, C (((a i : ℤ) : ZMod q₁)) * X ^ (i : ℕ)).IsRoot r)
    (hr₂ : ∀ r : ZMod q₂,
      ¬ (X ^ n + ∑ i : Fin n, C (((a i : ℤ) : ZMod q₂)) * X ^ (i : ℕ)).IsRoot r)
    (hcond : ((Nat.gcd (p - 1) n : ℝ) - 1) * (Real.sqrt p * (1 + Real.log p)) <
      (p : ℝ) / ((q₁ : ℝ) ^ 2 * (q₂ : ℝ) ^ 2) - 2) :
    ¬ ∀ α β : 𝓞 K, β ≠ 0 → ∃ γ ρ : 𝓞 K, α = γ * β + ρ ∧
      (Algebra.norm ℤ ρ).natAbs < (Algebra.norm ℤ β).natAbs := by
  classical
  set a' : ℕ → ℤ := fun i => if h : i < n then a ⟨i, h⟩ else 0 with ha'
  set c' : ℕ → ℕ := fun i => if h : i < n then c ⟨i, h⟩ else 0 with hc'
  have ha'0 : a' 0 = a ⟨0, hn⟩ := by simp [ha', hn]
  have hmap : ∀ q : ℕ, Polynomial.map (Int.castRingHom (ZMod q))
      (X ^ n + ∑ i ∈ Finset.range n, C (a' i) * X ^ i)
      = X ^ n + ∑ i : Fin n, C (((a i : ℤ) : ZMod q)) * X ^ (i : ℕ) := by
    intro q
    rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
      ← Fin.sum_univ_eq_sum_range
        (fun i => Polynomial.map (Int.castRingHom (ZMod q)) (C (a' i) * X ^ i)) n]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
    simp [ha', i.2]
  refine not_normEuclidean_of_eisensteinDumas_of_gcd_lt (θ := θ) (a := a') (cc := c')
    hp hn hm hmn hdeg ?_ ?_ ?_ ?_ hq₁ hq₂ hne hq₁p hq₂p ?_ ?_ hcond
  · rw [← hroot]
    congr 1
    rw [← Fin.sum_univ_eq_sum_range (fun i => ((a' i : ℤ) : 𝓞 K) * θ ^ i) n]
    exact Finset.sum_congr rfl fun i _ => by simp [ha', i.2]
  · intro i hi
    simpa [hc', hi] using hc ⟨i, hi⟩
  · intro i hi
    simpa [ha', hc', hi] using hdvd ⟨i, hi⟩
  · rwa [ha'0]
  · intro r
    rw [Polynomial.eval₂_eq_eval_map, hmap q₁]
    exact hr₁ r
  · intro r
    rw [Polynomial.eval₂_eq_eval_map, hmap q₂]
    exact hr₂ r

end NumberField
